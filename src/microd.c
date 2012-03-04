
// This implements microD

#include "microd.h"

#include <assert.h>
#include<typeinfo>

#include "rmem.h"
#include "root.h"

#include "module.h"
#include "template.h"
#include "declaration.h"
#include "statement.h"
#include "attrib.h"
#include "init.h"
#include "aggregate.h"
#include "arraytypes.h"
#include "id.h"

Dsymbols xdeferred;

OutBuffer buf1; // struct/union/enum forward declaration & includes
OutBuffer buf2; // struct/union/enum definition & var/func forward declaration
OutBuffer buf3; // var/func definition

void microd_decl1(const char *format, ...);
void microd_decl2(const char *format, ...);
void microd_decl3(const char *format, ...);

void microd_decl12(const char *format, ...);
void microd_decl23(const char *format, ...);
void microd_decl123(const char *format, ...);

char *comment1(const char *format, ...);
char *comment2(const char *format, ...);

void sinkImplements(md_fptr sink, ClassDeclaration* decl1, int prependComma);

//////////////////////////////////////////////////////////////////////////

struct MDState;

MDState *mds = NULL;

struct MDState
{
    VarDeclaration *sthis;
    MDState *prev;
    Module *m;
    Dsymbol *symbol;

    /////////////////////

    FuncDeclaration *getFunc()
    {
        MDState *bc = this;
        for (; bc->prev; bc = bc->prev);
        return (FuncDeclaration *)(bc->symbol);
    }

    /////////////////////

    MDState(Module *m, Dsymbol *s)
    {
        autopop = 1;
        push(m, s);
    }
    ~MDState()
    {
        if (autopop)
            pop();
    }
private:

    MDState *next;
    int autopop;

    MDState()
    {
        autopop = 0;
    }

    static void push(Module *m, Dsymbol *s)
    {
        MDState *x = new MDState;
        x->next = mds;
        mds = x;

        mds->prev = NULL;
        mds->m = m;
        mds->symbol = s;
        mds->sthis = NULL;
    }

    static void pop()
    {
        mds = mds->next;
    }
};

//////////////////////////////////////////////////////////////////////////

void getEthis(md_fptr sink, Loc loc, FuncDeclaration *fd);
void callfunc(md_fptr sink, int directcall, Type *tret, Expression *ec, Type *ectype,
              FuncDeclaration *fd, Type *t, Expression *ehidden, Expressions *arguments);
void escapeString(md_fptr sink, StringExp *se);

//////////////////////////////////////////////////////////////////////////

void microd_generate(Modules *modules)
{
	// FIXME: filthy hack for associative array iteration. I want to use JS for(x in y) but can't represent that in object.d itself right now.,
	// and semantic has already translated foreach into _aaApply calls...
	buf1.writestring("function _aaApply(obj, keysize, func) { for(var i in obj) { var result = func(obj[i]); if(result) return result;  }}");
	buf1.writestring("function _aaApply2(obj, keysize, func) { for(var i in obj) { var result = func(i, obj[i]); if(result) return result;  }}");

	// also for struct copying...
	buf1.writestring("function __d_struct_copy(obj) { if(obj === null) return obj; var n = {}; for(i in obj) n[i] = obj[i]; return n; }");

	// and for binding delegates...
	buf1.writestring("function __d_delegate(d_this, func) { return function() { var args = []; for(var a = 0; a < arguments.length; a++) args.push(arguments[a]); args.push(d_this); return func.apply(d_this, args); } }");

    for (size_t i = 0; i < modules->dim; i++)
    {
        Module *m = modules->tdata()[i];
        if (global.params.verbose)
            printf("microd gen %s\n", m->toChars());

        m->toMicroD();
    }

    char *n = FileName::name((*global.params.objfiles)[0]);
    File *mdfile = new File(FileName::forceExt(n, "js"));
    mdfile->ref = 1;

    buf1.writestring(buf2.toChars());
    buf1.writestring(buf3.toChars());

    buf1.writestring("if(_Dmain != null) _Dmain();\n");

    mdfile->setbuffer(buf1.data, buf1.offset);
    mdfile->writev();
}

//////////////////////////////////////////////////////////////////////////

void Module::toMicroD()
{
    for (size_t i = 0; i < members->dim; i++)
    {
        Dsymbol *s = (*members)[i];
        s->toMicroD();
    }

    while (xdeferred.dim != 0)
    {
        Dsymbol *s = xdeferred[0];
        xdeferred.remove(0);
        s->toMicroD();
    }
}

//////////////////////////////////////////////////////////////////////////

void Dsymbol::toMicroD()
{
	// I just want these to shut up
	if(strcmp(kind(), "import") == 0) 	return; // FIXME
	if(strcmp(kind(), "alias") == 0) 	return; // FIXME
    printf("ignored: %s [%s] %s\n", kind(), typeid(*this).name(), toChars());
}

void AssocArrayLiteralExp::toMicroD(md_fptr sink) {
	// AAs in JS are represented as objects, so we'll convert our literal to a JS object literal.
	assert(keys);
	assert(values);

	assert(keys->dim == values->dim);

	sink("({");
	for(size_t a = 0; a < keys->dim; a++) {
		if(a)
			sink(",");

		keys->tdata()[a]->toMicroD(sink);
		sink(":");
		values->tdata()[a]->toMicroD(sink);
	}
	sink("})");
}

int inComma = 0;
void CommaExp::toMicroD(md_fptr sink) {
	inComma++;
	// dmd likes to put out variable declarations here when running with -inline.
	// javascript doesn't allow that.
	// inComma is a global to inform the var declaration to omit the "var " - we'll just
	// use an implicit global instead, which works but sucks so I'd like to FIXME
	sink("(");
		sink("(");
		e1->toMicroD(sink);
		sink(")");
	sink(",");
		sink("(");
		e2->toMicroD(sink);
		sink(")");
	sink(")");

	inComma--;
}

void AttribDeclaration::toMicroD()
{
	if(suppress_js_output)
		return;
    Dsymbols *d = include(NULL, NULL);

    if (d)
    {
        for (size_t i = 0; i < d->dim; i++)
        {
            Dsymbol *s = (*d)[i];
            s->toMicroD();
        }
    }
}

void SymbolExp::toMicroD(md_fptr sink) {
	if(var)
	var->toMicroD(sink);
}

//////////////////////////////////////////////////////////////////////////

void DelegateExp::toMicroD(md_fptr sink) {
	if(!func)
		return;

	// we have to bind this to it somehow
	sink("__d_delegate(");
	e1->toMicroD(sink);
	sink(",");

	if(!func->isFuncLiteralDeclaration()) {
		func->toMicroD(sink);
	} else
		func->toMicroD();//sink);

	sink(")");
}

void FuncDeclaration::toMicroD(md_fptr sink) {
	if(suppress_js_output) return;

	if(isNested() && !this->inMicroD)
		toMicroD();
	else {
		if(linkage == LINKjs) {
			AggregateDeclaration* parent = isThis();
			char* name = NULL;
			if(parent) {
				name = parent->toChars();
				// D considers these to be a part of the class, but we want a part of the object...
				// it is important for at least the basics to work here to do feature detection of browsers
				if(strcmp(name, "JSDocument") == 0) // HACK HACK HACK HACK
					name = "document";
				else if(strcmp(name, "JSWindow") == 0) // HACK
					name = "window";
				else if(strcmp(name, "JSHistory") == 0) // HACK
					name = "history";
				else {
					//sink("__d_"); // to get to the class definition
					//name = parent->mangle();
					name = NULL;
				}
			}
		// if it is a member, we have to sink that too...

			if(name) {
				sink(name);
				sink(".");
				sink(toChars());
			} else {
				sink(mangle());
			}
		} else {
			sink(mangle());
		}
	}
}

void FuncDeclaration::toMicroD()
{
	if(suppress_js_output) return;
    // Find module m for this function
    Module *m = NULL;
    for (Dsymbol *p = parent; p; p = p->parent)
    {
        m = p->isModule();
        if (m)
            break;
    }
    assert(m);
    MDState xmds(m, this);

	if(!type) {
		return;
		printf("skipping: %s\n", toChars());
	}
    assert(type);

    assert(type->ty == Tfunction);
    md_fptr sink = &microd_decl3;

    /// functions without bodies shouldn't be there in JS
    /// it is probably just a built in
    if(!fbody) {
    	return;
    }


	// FIXME: I did this because binaryFunc in std.functional nests a function,
	// but then uses it later. I tried moving it to the outside, but that breaks
	// other nested funcs.

	// so the real FIXME is to find a way to take unnecessary function wrappers out.
	/*
	if(isNested() && !needsClosure() && !isFuncLiteralDeclaration()) {
		// these might be reused I think.... I'm moving it outside the present location
		// which should be ok since it doesn't need a closure. I hope. Maybe. FIXME: needs more testing

		sink = &microd_decl2;
	}
	*/

    inMicroD = 1; // FIXME: this is so nested references don't output multiple times. I wonder if there's a cleaner way?

    TypeFunction *tf = (TypeFunction *)type;
    assert(tf);
    // tf->next->toMicroD(sink);
    sink("function ");
    if(!isFuncLiteralDeclaration())
	    sink(mangle());

    sink("(");
    if(parameters)
    for (size_t i = 0; parameters && i < parameters->dim; i++)
    {
        if (i != 0)
            sink(", ");
        VarDeclaration *p = (*parameters)[i];
	assert(p);
        p->toMicroD(sink);
    }
    if (vthis)
    {
	mds->sthis = vthis;

	if(isCtorDeclaration()) {

	} else if(isDtorDeclaration()) {
		//printf("destructor\n");
	        vthis->toMicroD(sink);
	} else if(isPostBlitDeclaration()) {
	        vthis->toMicroD(sink);
	} else {
		assert(tf);
		assert(tf->parameters);
            if (tf->parameters->dim)
                sink(", ");
	        vthis->toMicroD(sink);
	}
    }
    // Body
    if (fbody)
    {
        sink(") {\n");
	if(isCtorDeclaration() && vthis) {
		/* JS actually constructs the object... */
		sink("var ");
		vthis->toMicroD(sink);
		sink(" = this;\n"); // new Object();\n");
	} else if(vthis) {
		// fallback for regular javascript this thingy calls. If the this argument
		// isn't an object like it should be, try this, but don't accept the window
		sink("if(typeof ");
		vthis->toMicroD(sink);
		sink(" != \"object\") ");
		vthis->toMicroD(sink);
		sink(" = this; \n");
	}
        fbody->toMicroD(sink);

	if(this->ident == Id::cpctor) {
		// if it is a copy constructor, we need to be able to keep the reference.
		// we'll hack this up by simply returning it.
		sink(" return ");
		vthis->toMicroD(sink);
		sink(";");
	}

        sink("}\n");
    }
    else
        sink(");\n");
}

void ScopeDsymbol::toMicroD() {
	if(suppress_js_output) return;

	TemplateDeclaration* td = this->isTemplateDeclaration();
	if(td) {
		// FIXME: I guess this could be TemplateDeclaration::toMicroD
		assert(td->semanticRun);

		for(unsigned a = 0; a < td->instances.dim; a++) {
			TemplateInstance* ti = td->instances.tdata()[a];
			ti->toMicroD();
		}
	} else {
		for(unsigned i = 0; i < members->dim; i++) {
			Dsymbol* s = (Dsymbol*) members->data[i];
			if(s->isFuncDeclaration()) {
			// FIXME: outputs the definition multiple times thanks to the above ti->toMicroD too.
			// but I think I need them both to do functions and structs..
					s->toMicroD();
			}  else {
				printf("idk [%s]  %s\n", typeid(*this).name(), this->toChars());
				s->toMicroD();
				/*
				assert(scope);
				s->semantic(scope);
				s->toMicroD();
				*/
			}
		}
	}
}

void sinkInitializer(md_fptr sink, VarDeclaration* vd, Initializer* init) {
	int isStruct = dynamic_cast<TypeStruct*>(vd->type) != NULL;

	if(isStruct) {
		// we have to copy a struct, not assign a reference
		sink("__d_struct_copy(");
	}

	init->toMicroD(sink);

	if(isStruct) {
		sink(")");
	}
}

void VarDeclaration::toMicroD()
{
	if(suppress_js_output) return;
	md_fptr sink = &microd_decl3;

	if(storage_class & STCstatic)
		assert(0);

	if(linkage == LINKjs) // don't put out things that are supposed to be in js
		return;

	type->toMicroD(sink);
	sink(" ");
	sink(mangle());
	microd_decl3(" = ");

	if (init)
		sinkInitializer(sink, this, init);
	else
		type->defaultInit(0)->toMicroD(sink);
	sink(";\n");
}

void StructDeclaration::toMicroD()
{
	if(suppress_js_output) return;

    char *name = mangle();

    md_fptr sink = &microd_decl2;

    sink("function __d_");
    sink(name);
    sink("() {\n");

    for (size_t i = 0; i < members->dim; i++)
    {
        Dsymbol *s = (*members)[i];

        if (Declaration *vd = s->isVarDeclaration())
        {
            vd->toMicroD(sink);
            sink(";\n");
        }
        else if (FuncDeclaration *fd = s->isFuncDeclaration())
        {
            xdeferred.push(fd);
        }
        else
        {
    //        s->error(" %s not supported in MicroD", typeid(*this).name());
    //        sink("null/*__dsymbol__*/;\n");
        }
    }

    sink("}\n");
}

void sinkvirtual(md_fptr sink, ClassDeclaration* cd, FuncDeclaration* fd) {
	// adds it to the vtable
	if(fd->isAbstract())
		return; // abstract functions aren't defined
	sink("this.__d_vtbl[%d] = ", fd->vtblIndex);
	fd->toMicroD(sink);
	sink(";\n");
}

void sinkclassbase(md_fptr sink, ClassDeclaration* base) {
	if(base == NULL)
		return;
	sinkclassbase(sink, base->baseClass);
	// this will do reverse order so Object is the first one initialized
	sink("__d_");
	sink(base->mangle());
	sink(".call(this, null);\n");
}

void ClassDeclaration::toMicroD()
{
	if(suppress_js_output) return;
    char *name = mangle();

    md_fptr sink = &microd_decl2;

	// classes have constructors, so we don't need this kind of initializer. or do we?

    sink("function __d_");
    sink(name);
    sink("(__d_constructor) {\n"); // constructor args are passed as variadic fyi

    assert(this->baseclasses != NULL);

    if(this->baseClass == NULL) {
    	// this is Object itself, so declare the vtable
	sink("this.__d_vtbl = [];\n");
    }

    // call base classes too. this will set up the parent's initializers and the basic methods for inheritance
    sinkclassbase(sink, this->baseClass);
    

    sink("this.__d_vtbl.length = %d;\n", vtbl.dim); // preparing our own vtable to have the slots filled in later

    for (size_t i = 0; i < members->dim; i++)
    {
        Dsymbol *s = (*members)[i];

	if(s->suppress_js_output)
		continue;

        if (Declaration *vd = s->isVarDeclaration())
        {
            vd->toMicroD(sink);
            sink(";\n");
        }
        else if (FuncDeclaration *fd = s->isFuncDeclaration())
        {
            xdeferred.push(fd);

	    if(fd->isVirtual()) {
	    	sinkvirtual(sink, this, fd);
	    }
        }
	else if(AttribDeclaration* f = s->isAttribDeclaration()) {
			    Dsymbols *d = f->include(NULL, NULL);

			    if (d)
			    {
				for (size_t i = 0; i < d->dim; i++)
				{
				    Dsymbol *s = (*d)[i];
				    if(FuncDeclaration* fd = s->isFuncDeclaration()) {
            					xdeferred.push(fd);
									
					    if(fd->isVirtual()) {
					    	sinkvirtual(sink, this, fd);
					    }
				    } else
				    s->toMicroD();
				}
			    }

	}
        else
        {
            // s->error("not supported in MicroD %s", typeid(*s).name());
            //sink("__dsymbol__;\n");
        }
    }

    // add some run time type information
    sink("this.__d_classname = \"");
    sink(toPrettyChars());
    sink("\";\n");
    sink("this.__d_implements = [");
    	// it implements itself...
		sink("\"");
    		sink(mangle());
		sink("\"");
	// and whatever else it inherits from
	// FIXME: let's not do this out here.. let's instead add stuff to it from Object on down
	// in the initializers.
    sinkImplements(sink, this, 1);
    sink("];\n");

    // now we have to call the constructor with the arguments given...
    sink("return __d_construct.call(this, __d_constructor, arguments);");

    sink("}\n");
}


void sinkImplements(md_fptr sink, ClassDeclaration* decl1, int prependComma) {
    if(decl1->baseclasses)
    for(unsigned a = 0; a < decl1->baseclasses->dim; a++) {
	ClassDeclaration* decl = decl1->baseclasses->tdata()[a]->base;
	if(decl) {
		if(prependComma)
			sink(", ");
		sink("\"");
		sink(decl->mangle());
		sink("\"");
		prependComma = 1;

		sinkImplements(sink, decl, prependComma);
	}
    }
}


//////////////////////////////////////////////////////////////////////////

void Declaration::toMicroD(md_fptr sink)
{
    error("Declaration %s not supported ('%s')", typeid(*this).name(), toChars());
    sink("/*__Declaration__*/");
}

void AliasDeclaration::toMicroD(md_fptr sink) {
	// doing nothing because the frontend has already handled the important stuff about alias
}

void FuncExp::toMicroD(md_fptr sink) {
	if(fd)
		fd->toMicroD();
}

void VarDeclaration::toMicroD(md_fptr sink)
{
    if(storage_class & STCstatic)
    	sink = &microd_decl1; // static variables should be global in scope

    if(!inComma && !isParameter() && !isThis()) { // inComma is a hack for inlining (filthy one too, we're depending on the mangled names to save us with uniqueness). See CommaExp for more info
    	assert(type);
    	type->toMicroD(sink);
	    sink(" ");
    }

    if(inComma) {
    	md_fptr oldsink;
	oldsink = sink;
    	sink = &microd_decl1; // HACK: hoist the declaration to the global namespace
	sink("var ");
	sink(mangle());
	sink(";\n");
	sink = oldsink;
    }

    if(isThis()) {
	sink("this.");
    }

    sink(mangle());


    if (init)
    {
        sink(" = ");
        ExpInitializer *ie = init->isExpInitializer();
	assert(type);
        if (ie && (ie->exp->op == TOKconstruct || ie->exp->op == TOKblit))
        {
            Expression *ex = ((AssignExp *)ie->exp)->e2;
	    assert(ex);
            if (ex->op == TOKint64 && type->ty == Tstruct)
		sinkInitializer(sink, this, init);
                //goto Ldefault;
            else
		sinkInitializer(sink, this, init);
                //ex->toMicroD(sink);
        }
        else if (ie && ie->exp->op == TOKint64 && type->ty == Tstruct)
		sinkInitializer(sink, this, init);
            //goto Ldefault;
        else {
		sinkInitializer(sink, this, init);
	}
    }
    else if (!isParameter() && !isThis())
    {
        sink(" = ");
    Ldefault:
        type->defaultInitLiteral(loc)->toMicroD(sink);
    }

    if(!init && isThis()) {
    	sink(" = ");
	type->defaultInitLiteral(loc)->toMicroD(sink);
    }

    if(storage_class & STCstatic)
    	sink(";"); // not sure why this is needed..
}

void ArrayLiteralExp::toMicroD(md_fptr sink) {
	sink("[");
	if(elements)
		for(unsigned i = 0; i < elements->dim; i++) {
			if(i != 0)
				sink(", ");
			Expression* e = (Expression*) elements->data[i];
			e->toMicroD(sink);
		}
	sink("]");
}

//////////////////////////////////////////////////////////////////////////

void Type::toMicroD(md_fptr sink)
{
//    error(0, "Type '%s' not supported in MicroD", toChars());
    sink("var");
}

void TypeArray::toMicroD(md_fptr sink)
{
	sink("var");
}

void TypeBasic::toMicroD(md_fptr sink)
{
	sink("var");
	/*
    switch(ty)
    {
    case Tvoid:
    case Tint8:
    case Tuns8:
    case Tint16:
    case Tuns16:
    case Tint32:
    case Tuns32:
        sink("__d_%s", toChars());
        return;
    default:
        Type::toMicroD(sink);
    }
    */
}

void TypeStruct::toMicroD(md_fptr sink)
{
    sink("var");
}

//////////////////////////////////////////////////////////////////////////

void Parameter::toMicroD(md_fptr sink)
{
    //type->toMicroD(sink);
    //sink(" ");
    sink(ident->toChars());
    if (defaultArg)
    {
        sink(" = ");
        defaultArg->toMicroD(sink);
    }
}

//////////////////////////////////////////////////////////////////////////

void Expression::toMicroD(md_fptr sink)
{
    error("Expression %s not supported in MicroD ('%s')", typeid(*this).name(), toChars());
    //sink(toChars());
    sink("/*__expression__*/");
}

void argsToMicroD(md_fptr sink, Expressions* arguments)
{
    if (arguments)
    {
        for (size_t i = 0; i < arguments->dim; i++)
        {   Expression *arg = arguments->tdata()[i];

            if (arg)
            {   if (i)
                    sink(",");
		arg->toMicroD(sink);
            }
        }
    }
}


void NewExp::toMicroD(md_fptr sink) {
    sink("new ");
    /* // js has no placement new or anything
    if (newargs && newargs->dim)
    {
        sink("(");
        argsToMicroD(sink, newargs);
        sink(")");
    }
    */
    //sink(newtype->toChars()); // this isn't toMicroD because we want the type name, not var, to construct

	if(!member) {
		// FIXME: what if it is a custom D type without a constructor?
		Dsymbol* sym = type->toDsymbol(NULL);
		if(sym != NULL)
			sink(sym->toChars());
//		sink(type->mangle());
		sink("()");
		return;
	}

    ClassDeclaration* classOf = member->isMember2()->isClassDeclaration();
    assert(classOf);

    int putComma = 0;

    if(member->linkage == LINKjs) {
	sink(classOf->toChars());
	    sink("(");
    } else{
	    sink("__d_");
	    sink(classOf->mangle()); // the class we want
	    sink("(");
	    if(member)
		    sink(member->mangle()); // constructor
	    else
		    sink("null");
	    putComma = 1;
	}

    if (arguments && arguments->dim)
    {
	if(putComma)
	        sink(",");
        argsToMicroD(sink, arguments); // constructor arguments
    }
    sink(")");
}

Expression* slicing = NULL; // hack for $ work

void IndexExp::toMicroD(md_fptr sink) {
	slicing = e1; // hack for handling $
	e1->toMicroD(sink);
	if(e1->type->isString()) {
		// D expects a char here, but JS can't index a string
		// moreover, we expect char to be int-like, not a string.
		// the charCodeAt function does the indexing, giving us an int.
		sink(".charCodeAt(");
		e2->toMicroD(sink);
		sink(")");
	} else {
		sink("[");
		e2->toMicroD(sink);
		sink("]");
	}
	slicing = NULL;
}

void SliceExp::toMicroD(md_fptr sink) {
	sink("(");
	e1->toMicroD(sink);
	sink(")");

	if(!upr && !lwr)
		return; // if we want the whole thing as a slice, no need to do anything

	slicing = e1; // global variable hack for $

	sink(".slice(");

	if(lwr) {

		lwr->toMicroD(sink);
	} else {
		sink("0");
	}

	if(upr) {
		sink(",");
		upr->toMicroD(sink);
	} else {
		if(lengthVar) {
			sink(",");
			lengthVar->toMicroD(sink);
		}
	}

	sink(")");

	slicing = NULL;
}

void RealExp::toMicroD(md_fptr sink) {
	sink("%Lg", toReal());
}

void IntegerExp::toMicroD(md_fptr sink)
{
    dinteger_t v = toInteger();
    sink("%d", v);
}

void DeclarationExp::toMicroD(md_fptr sink)
{
    Declaration *d = declaration->isDeclaration();
    if(!d) {
    	StructDeclaration *sd = declaration->isStructDeclaration();
	if(sd) {
		// FIXME
		sd->toMicroD();
	} else {
		printf("wtf [%s] %s", typeid(*declaration).name(), toChars());
	}
    } else {
	    assert(d);
	    d->toMicroD(sink);
    }
}

void LabelStatement::toMicroD(md_fptr sink) {
	sink("%s:", ident->toChars());
	if(statement)
		statement->toMicroD(sink);
}

void BreakStatement::toMicroD(md_fptr sink) {
	sink("break");
	if(ident) {
		sink(" %s", ident->toChars());
	}
	sink(";");
}
void ContinueStatement::toMicroD(md_fptr sink) {
	sink("continue");
	if(ident) {
		sink(" %s", ident->toChars());
	}
	sink(";");
}

void ThrowStatement::toMicroD(md_fptr sink) {
	sink("throw ");
	exp->toMicroD(sink);
	sink(";");
}

void TryFinallyStatement::toMicroD(md_fptr sink) {
	int needsTry = dynamic_cast<TryCatchStatement*>(body) == NULL;
	if(needsTry)
		sink("try {");
	body->toMicroD(sink); // body is a TryCatchStatement
	if(needsTry)
		sink("}");
	if(finalbody) {
		sink("finally {\n");
		finalbody->toMicroD(sink);
		sink("}\n");
	}
}

void TryCatchStatement::toMicroD(md_fptr sink) {
	sink("try {\n");
	if(body)
		body->toMicroD(sink);
	sink("}\n");

	static int catchCount = 0;

	if(catches) {
		sink("catch (__d_exception_%d) {\n", ++catchCount);
		sink("var __d_exception_%d_caught = false;", catchCount);
		for(unsigned i = 0; i < catches->dim; i++) {
			Catch* c = (Catch*) catches->data[i];
			if(c) {
				sink("if(!__d_exception_%d_caught) {", catchCount);
				Dsymbol* t1 = c->type->toDsymbol(NULL);
				assert(t1);
				ClassDeclaration* t = t1->isClassDeclaration();
				assert(t);

				sink("var %s = __d_dynamic_cast(__d_exception_%d, \"%s\");\n", c->var->mangle(), catchCount, t->mangle());
				sink("if(%s) {\n", c->var->mangle());
				sink("__d_exception_%d_caught = true;\n", catchCount);
				c->handler->toMicroD(sink);
				sink("}");
				sink("}"); // if(!caught)
			}
		}

		// if none of our handlers actually handle this type, we have to rethrow
		sink("if(!__d_exception_%d_caught) throw __d_exception_%d;", catchCount, catchCount);

		sink("}\n");
	}
}

void UnaExp::toMicroD(md_fptr sink) {
	switch(op) {
		case TOKneg:
		case TOKplusplus:
		case TOKminusminus:
		case TOKnot:
			sink(Token::toChars(op));
			sink("(");
		        e1->toMicroD(sink);
			sink(")");
		break;
		default:
			Expression::toMicroD(sink);
		break;
	}
}

void PostExp::toMicroD(md_fptr sink) {
	switch(op) {
		case TOKplusplus:
		case TOKminusminus:
			sink("(");
		        e1->toMicroD(sink);
			sink(")");
			sink(Token::toChars(op));
		break;
		default:
			Expression::toMicroD(sink);
		break;
	}
}

void ArrayLengthExp::toMicroD(md_fptr sink) {
	sink("(");
	e1->toMicroD(sink);
	sink(".length");
	sink(")");
}

void IdentityExp::toMicroD(md_fptr sink) {
	sink("(");
	e1->toMicroD(sink);
	if(op == TOKidentity)
		sink("===");
	else // must be !is
		sink("!==");
	e2->toMicroD(sink);
	sink(")");
}

int inAssignment = 0; // yet another hack. this one is used for reference assignments

void AssignExp::toMicroD(md_fptr sink) {
	VarExp* exp = dynamic_cast<VarExp*>(e1);
	if(exp && exp->var && exp->var->isRef()) {
		inAssignment = 1;
		e1->toMicroD(sink);
		inAssignment = 0;

		// we do reference params as lambdas, so we call it here.
		sink("(");
		e2->toMicroD(sink);
		sink(")");
	} else {
		BinExp::toMicroD(sink);
	}
}

void BinExp::toMicroD(md_fptr sink)
{
    switch (op)
    {
    case TOKdivass:
    case TOKdiv:
    	// javascript can return a float here, but we expect truncation in D for ints
	if(type->isintegral())
		sink("Math.floor");

    case TOKlt:
    case TOKle:
    case TOKgt:
    case TOKge:
    case TOKnotequal:

    case TOKadd:
    case TOKmin:
    case TOKmul:
    case TOKand:
    case TOKor:
    case TOKxor:

    case TOKaddass:
    case TOKminass:
    case TOKmulass:
    case TOKandass:
    case TOKorass:
    case TOKxorass:

    //case TOKconstruct:

    case TOKoror:
    case TOKandand:
    case TOKshl:
    case TOKin: // FIXME: D expects a pointer
  generic_operator:
        sink("(");
        e1->toMicroD(sink);
        sink(" %s ", Token::toChars(op));
        e2->toMicroD(sink);
        sink(")");
        break;
    case TOKequal:
    	// Javascripts == operator works for us most the time, but not for non-string arrays
	// FIXME: check - ensure that opEquals works on objects and check structs too

	// assuming e1 and e2 are the same type already, so only checking e1
	if(e1->type->isscalar() || e1->type->isString())
		goto generic_operator; // treat them generically; JS's == is good enough
	else {
		// we have to use a runtime function; this must be an array
		// again assuming that D's semantics mean they are already compatible for this
		sink("__d_array_compare(");
		e1->toMicroD(sink);
		sink(", ");
		e2->toMicroD(sink);
		sink(")");
	}
    break;
    case TOKconstruct: {
		// we special case this again for structs
		TypeStruct* ts = dynamic_cast<TypeStruct*>(e1->type);
		if(!ts) {
    			op = TOKassign;
			goto generic_operator;
		}

		// if it is another struct, we need to copy that struct
		// if it is some other type, just default construct it

		TypeStruct* tsrhs = dynamic_cast<TypeStruct*>(e2->type);
		if(tsrhs) {
			sink("__d_struct_copy(");
			e2->toMicroD(sink);
			sink(")");
		} else {
			sink("new __d_");
			assert(ts);
			assert(ts->sym);
			sink(ts->sym->mangle());
			sink("(null)");
		}
    } break;
    case TOKblit:
    	op = TOKassign;
    case TOKassign: {
    	// JS assign semantics are ok most the time, but there's one big exception: structs
	// we implement it as a JS object, which is managed by reference. A D struct is done by
	// value, and may also have a postblit function that needs to be called.

	TypeStruct* ts = dynamic_cast<TypeStruct*>(e2->type);
	if(ts) {
		e1->toMicroD(sink);
		sink(" = __d_struct_copy(");
		e2->toMicroD(sink);
		sink(")");
	} else {
		goto generic_operator;
	}

	// FIXME: check opAssign too
    } break;
    case TOKcatass:
        e1->toMicroD(sink);
        sink(" = (");
        e1->toMicroD(sink);
        sink(".concat(");
        e2->toMicroD(sink);
        sink("))");
	break;

    break;
    case TOKcat:
        sink("(");
        e1->toMicroD(sink);
        sink(".concat(");
        e2->toMicroD(sink);
        sink("))");
	break;
    default:
    	printf("op is [%d] %d %s\n", TOKassign, op, Token::toChars(op));
        Expression::toMicroD(sink);
        break;
    }
}

void CallExp::toMicroD(md_fptr sink)
{
	assert(e1);
    Type *t1 = e1->type->toBasetype();
    assert(t1);
    Type *ectype = t1;
    Expression *ec = NULL;
    FuncDeclaration *fd = NULL;
    int directcall = 0;
    Expression *ehidden = NULL;

    if (e1->op == TOKdotvar && t1->ty != Tdelegate)
    {
        DotVarExp *dve = (DotVarExp *)e1;

        fd = dve->var->isFuncDeclaration();
        Expression *ex = dve->e1;
        while (1)
        {
            switch (ex->op)
            {
                case TOKsuper:          // super.member() calls directly
                case TOKdottype:        // type.member() calls directly
                    directcall = 1;
                    break;

                case TOKcast:
                    ex = ((CastExp *)ex)->e1;
                    continue;

                default:
                    //ex->dump(0);
                    break;
            }
            break;
        }
        ec = dve->e1;
        ectype = dve->e1->type->toBasetype();
    }
    else if (e1->op == TOKvar)
    {
        fd = ((VarExp *)e1)->var->isFuncDeclaration();
        ec = e1;
    }
    else
    {
        ec = e1;
    }

    if(fd && fd->linkage == LINKjs)
    	directcall = 1;

    callfunc(sink, directcall, type, ec, ectype, fd, t1, ehidden, arguments);
}

void DotVarExp::toMicroD(md_fptr sink)
{
    sink("(");
    e1->toMicroD(sink);
    sink(")");

    if(var->linkage == LINKjs) {
    	char* name = var->toChars();
	int len = strlen(name);
	if(len > 5 && name[0] == '_' && name[1] == '_' && name[2] == 'j' && name[3] == 's' && name[4] == '_') {
		name += 5;
	}
	if(strcmp(name, "this") == 0) {
		// .this doesn't actually make sense in javascript; this is a keyword that never works there.
		// if this is here, it is probably a hack for alias this expansion... we don't want
		// to actually output anything in this case.

		// why do i allow this hack? If you want to do custom classes around a builtin and
		// extend it without inheritance, you can give the old class as __js_this and alias this it.
		// filthy hack but it allows some added efficiency in wrappers; adding free functions to a
		// native thing while looking like a class in D.
	} else {
		sink(".");
	        sink(name);
	}
    } else {
    	sink(".");
        sink(var->mangle());
    }
}

void VarExp::toMicroD(md_fptr sink)
{
	if(!var) return;

	if(var->ident && var->ident == Id::ctfe) {
		sink("0");
		return;
	}


	if(var->ident && var->ident == Id::dollar) {
		VarDeclaration* v = dynamic_cast<VarDeclaration*>(var);
		assert(v);
		// the dollar is only valid in slices
		// the slice is implemented in js as Array.slice
		if(v->init && !v->init->isVoidInitializer())
			v->init->toMicroD(sink); // I'm just trying to run it inline... not sure if this works
		else {
			assert(slicing);
			slicing->toMicroD(sink);
			sink(".length");
		}

		return;
	}

	char* name = var->toChars();
	int len = strlen(name);
	if(len > 5 && name[0] == '_' && name[1] == '_' && name[2] == 'j' && name[3] == 's' && name[4] == '_') {
		// these correspond directly to javascript keywords in some way
		if(strcmp(name, "__js_array_literal") == 0)
			sink("[]");
		else if(strcmp(name, "__js_object_literal") == 0)
			sink("{}");
		else
			sink(name + 5); // probably a keyword or something
	} else {
		// FIXME: another filthy hack to get around struct init forward declaration errors
		if(strstr(name, "__initZ")) {
		    sink("new __d_");
		    TypeStruct* ts = dynamic_cast<TypeStruct*>(this->type);
		    assert(ts);
		    sink(ts->sym->mangle());
		    sink("()");
		}
		else
		sink(var->mangle());
	}

	if(!inAssignment && (var->isRef())) {
		// to pass variables by reference in javascript, we do it with a lambda
		sink("()");
	}

}

void CastExp::toMicroD(md_fptr sink)
{
	assert(to);

	ClassDeclaration* classOf = NULL;
	Type* from = e1->type;

	// only class to class needs dynamic_cast
	if(from->isClassHandle())
		classOf = to->isClassHandle();

	// FIXME: what about casting from (say) int to ubyte? We expect truncation of bits in D, and two's complement negatives.

	if(classOf)
		sink("__d_dynamic_cast");
	else if(to->isintegral() && !from->isintegral()) // if they already match, no need to do the Math again
		sink("Math.floor"); // in D, when you cast to int, you expect truncation
	else if(to->isfloating() && !from->isfloating())
		sink("Number");
	else if(to->isString() && !from->isString())
		sink("String");

    sink("(");
    e1->toMicroD(sink);
	if(classOf) {
		sink(", \"");
		sink(classOf->mangle());
		sink("\"");
	}
    sink(")");
}

void AssertExp::toMicroD(md_fptr sink)
{
    e1->toMicroD(sink);
    sink(" || ");
    if (msg)
    {
        sink("__d_assert_msg(");
        msg->toMicroD(sink);
        sink(", ");
    }
    else
        sink("__d_assert(");

	if(loc.filename)
    escapeString(sink, new StringExp(0, (char*)loc.filename, strlen(loc.filename)));
    	else sink("\"[unknown]\"");
    sink(", %d)", loc.linnum);
}

void StringExp::toMicroD(md_fptr sink)
{
    Type *tb = type->toBasetype();
    if (!tb->nextOf() || tb->nextOf()->ty != Tchar)
    {
        error("only utf-8 strings are supported in MicroD, not %s", toChars());
        sink("__StringExp__");
        return;
    }

    if (tb->ty == Tpointer)
    {
        escapeString(sink, this);
    }
    else if (tb->ty == Tarray)
    {
        escapeString(sink, this);
    }
    else
    {
        error("only char* strings are supported in MicroD, not %s", toChars());
        sink("__StringExp__");
        return;
    }
}

void sinkEmptyType(md_fptr sink, Type* type) {
    if(type == NULL) {
	    sink("null");
	    return;
    }

    if(type->isString())
    	    sink("\"\"");
    else if(type->ty == Tsarray) {
    		// a static array should have the length set too, since we know it

		// these might be a good candidate for the webgl typed arrays too, but
		// since they aren't necessarily present in JS, I don't want to completely rely upon them
		TypeSArray* sa = dynamic_cast<TypeSArray*>(type);
		assert(sa);
		sink("new Array(");
		sa->dim->toMicroD(sink);
		sink(")");
    } else if(type->ty == Tarray)
    	    sink("[]");
    else if(type->ty == Taarray)
    	    sink("{}");
    else
    	sink("null");
}

void NullExp::toMicroD(md_fptr sink)
{
	sinkEmptyType(sink, type);
}

void BoolExp::toMicroD(md_fptr sink) { // FIXME: i'm not really sure what this is
    e1->toMicroD(sink);
}

void AddrExp::toMicroD(md_fptr sink)
{
    e1->toMicroD(sink);
}

void PtrExp::toMicroD(md_fptr sink) // FIXME: should this be here?
{
    e1->toMicroD(sink);
}

void ThisExp::toMicroD(md_fptr sink)
{
    FuncDeclaration *fd;
    assert(mds->sthis);

    if (var)
    {
        assert(var->parent);
        fd = var->toParent2()->isFuncDeclaration();
        assert(fd);
        getEthis(sink, loc, fd);
    }
    else
        sink(mds->sthis->mangle());
}

void StructLiteralExp::toMicroD(md_fptr sink)
{
// FIXME: confirm this works with arguments too
    sink("new __d_");
    sink(this->sd->mangle());
    sink("(");
    for (size_t i = 0; i < elements->dim; i++)
    {
        Expression *e = (*elements)[i];
        if (i)
            sink(", ");
        e->toMicroD(sink);
    }
    sink(")");
}

//////////////////////////////////////////////////////////////////////////

void Initializer::toMicroD(md_fptr sink)
{
    error("This type of initializer, %s, not supported in MicroD ('%s')", typeid(*this).name(), toChars());
    sink("__init__");
}

void ExpInitializer::toMicroD(md_fptr sink)
{
    exp->toMicroD(sink);
}

void VoidInitializer::toMicroD(md_fptr sink) {
	sinkEmptyType(sink, type);
}

//////////////////////////////////////////////////////////////////////////

void Statement::toMicroD(md_fptr sink)
{
    error("Statement %s not supported in MicroD ('%s')", typeid(*this).name(), toChars());
    sink("__statement__;\n");
}

void SwitchStatement::toMicroD(md_fptr sink) {
	sink("switch(");
	condition->toMicroD(sink);
	sink(") {\n");
	body->toMicroD(sink);
	sink("}");
}

void CaseStatement::toMicroD(md_fptr sink) {
	sink("case ");
	exp->toMicroD(sink);
	sink(":\n");
	statement->toMicroD(sink);
}

void DefaultStatement::toMicroD(md_fptr sink) {
	sink("default:\n");
	statement->toMicroD(sink);
}

void CompoundStatement::toMicroD(md_fptr sink)
{
	if(statements)
    for (size_t i = 0; i < statements->dim; i++)
    {
        Statement *s = (*statements)[i];
	if(s) {
        	s->toMicroD(sink);
	}
    }
//	sink("/* end compound */");
}

void CompoundDeclarationStatement::toMicroD(md_fptr sink)
{
    int nwritten = 0;
    for (size_t i = 0; i < statements->dim; i++)
    {
        Statement *s = (*statements)[i];
        ExpStatement *es = s->isExpStatement();
        assert(es && es->exp->op == TOKdeclaration);
        DeclarationExp *de = (DeclarationExp *)es->exp;
        Declaration *d = de->declaration->isDeclaration();
        assert(d);
        VarDeclaration *v = d->isVarDeclaration();
        if (v)
        {
            if (nwritten)
                sink(",");
            // write storage classes
            if (v->type && !nwritten)
                v->type->toMicroD(sink);
            sink(" ");
            sink(v->mangle());
            if (v->init)
            {
                sink(" = ");
                ExpInitializer *ie = v->init->isExpInitializer();
                if (ie && (ie->exp->op == TOKconstruct || ie->exp->op == TOKblit))
                    ((AssignExp *)ie->exp)->e2->toMicroD(sink);
                else
                    v->init->toMicroD(sink);
            }
        }
        else
            d->toMicroD(sink);
        nwritten++;
    }
    sink(";\n");
}

void ExpStatement::toMicroD(md_fptr sink)
{
    exp->toMicroD(sink);
    sink(";\n");
}

void IfStatement::toMicroD(md_fptr sink)
{
	sink("if (");
	assert(condition);
	condition->toMicroD(sink);
	sink(") {");
	if(ifbody)
	ifbody->toMicroD(sink);
	sink("}");
	if(elsebody) {
		sink("else {");
		elsebody->toMicroD(sink);
		sink("}");
	}
}

void ConditionalStatement::toMicroD(md_fptr sink)
{
	// FIXME I don't even know what this actually is
}

void CondExp::toMicroD(md_fptr sink) {
	sink("(");
	sink("(");
	econd->toMicroD(sink);
	sink(")");
	sink("?(");
	e1->toMicroD(sink);
	sink("):(");
	e2->toMicroD(sink);
	sink("))");
}

void ScopeStatement::toMicroD(md_fptr sink) {
	if(statement)
	statement->toMicroD(sink);
}

void ForStatement::toMicroD(md_fptr sink)
{
    sink("for (");
    if(init)
    init->toMicroD(sink);
    else
    sink("; ");

    if(condition)
    condition->toMicroD(sink);
    sink("; ");

    if(increment)
    increment->toMicroD(sink);
    sink(") {");
    if(body)
    body->toMicroD(sink);
    sink("}\n");
}

void WhileStatement::toMicroD(md_fptr sink) {
	sink("while (");
	condition->toMicroD(sink);
	sink(") {\n");
	body->toMicroD(sink);
	sink("}\n");
}

void DoStatement::toMicroD(md_fptr sink) {
	sink("do {\n");
	body->toMicroD(sink);
	sink("} while(");
	condition->toMicroD(sink);
	sink(");\n");
}

void ForeachStatement::toMicroD(md_fptr sink) {
	// this space intentionally left blank (it will do a for i think)
}

void ReturnStatement::toMicroD(md_fptr sink)
{
    sink("return ");
    if(exp)
    exp->toMicroD(sink);
    sink(";\n");
}

//////////////////////////////////////////////////////////////////////////

void microd_decl1(const char *format, ...)
{
    va_list ap;
    va_start(ap, format);
    buf1.vprintf(format,ap);
    va_end(ap);
}

void microd_decl2(const char *format, ...)
{
    va_list ap;
    va_start(ap, format);
    buf2.vprintf(format,ap);
    va_end(ap);
}

void microd_decl3(const char *format, ...)
{
    va_list ap;
    va_start(ap, format);
    buf3.vprintf(format,ap);
    va_end(ap);
}

void microd_decl12(const char *format, ...)
{
    va_list ap;
    va_start(ap, format);
    buf1.vprintf(format,ap);
    buf2.vprintf(format,ap);
    va_end(ap);
}

void microd_decl23(const char *format, ...)
{
    va_list ap;
    va_start(ap, format);
    buf2.vprintf(format,ap);
    buf3.vprintf(format,ap);
    va_end(ap);
}

void microd_decl123(const char *format, ...)
{
    va_list ap;
    va_start(ap, format);
    buf1.vprintf(format,ap);
    buf2.vprintf(format,ap);
    buf3.vprintf(format,ap);
    va_end(ap);
}


char *comment1(const char *format, ...)
{
    va_list ap;
    va_start(ap, format);
    OutBuffer buf;
    buf.writestring("/***********************************************************\n * \n * ");
    buf.vprintf(format, ap);
    buf.writestring("\n * \n */\n\n");
    va_end(ap);
    return buf.extractData();
}
char *comment2(const char *format, ...)
{
    va_list ap;
    va_start(ap, format);
    OutBuffer buf;
    buf.writestring("/***********************************************************\n * ");
    buf.vprintf(format, ap);
    buf.writestring("\n */\n\n");
    va_end(ap);
    return buf.extractData();
}

void getEthis(md_fptr sink, Loc loc, FuncDeclaration *fd)
{
    FuncDeclaration *thisfd = mds->getFunc();
    Dsymbol *fdparent = fd->toParent2();

    if (fd->ident == Id::require || fd->ident == Id::ensure)
        assert(0);

    if (fdparent == thisfd)
    {
        //if (mds->sclosure)

        if (mds->sthis)
        {
            sink(mds->sthis->mangle());
        }
        else
        {
            assert(0);
        }
    }
    else
    {
        if (!mds->sthis)
        {
            fd->error(loc, "is a nested function and cannot be accessed from %s", mds->getFunc()->toPrettyChars());
            sink("__ethis__");
            return;
        }
        else
        {
            VarDeclaration *ethis = mds->sthis;
            Dsymbol *s = thisfd;
            while (fd != s)
            {
                thisfd = s->isFuncDeclaration();
                if (thisfd)
                {
                    if (fdparent == s->toParent2())
                        break;
                    if (thisfd->isNested())
                    {
                        FuncDeclaration *p = s->toParent2()->isFuncDeclaration();
                        if (!p || p->hasNestedFrameRefs())
                            sink("*");
                    }
                    else if (thisfd->vthis)
                    {
                    }
                    else
                    {   // Error should have been caught by front end
                        assert(0);
                    }
                }
                else
                {
                    assert(0);
                }
                s = s->toParent2();
                assert(s);
            }
            sink(ethis->mangle());
        }
    }
}

void sinkRefArg(md_fptr sink, Expression* arg) {
	sink("function(val) { if(typeof val != \"undefined\") ");
		arg->toMicroD(sink);
	sink(" = val; return ");
	arg->toMicroD(sink);
	sink(";}");
}

void callfunc(md_fptr sink, int directcall, Type *tret, Expression *ec, Type *ectype,
              FuncDeclaration *fd, Type *t, Expression *ehidden, Expressions *arguments)
{

    int useVtbl = 0;
    int useDotSyntax = 0;
    if(fd && fd->linkage == LINKjs)
    	useDotSyntax = 1;

    t = t->toBasetype();
    TypeFunction *tf = NULL;
    Expression *ethis = NULL;

    if (t->ty == Tdelegate)
    {
    	TypeDelegate* td = (TypeDelegate*) t;
	assert(td);
    	tf = (TypeFunction*) td->next;
    } else if(t->ty == Tfunction) {
        tf = (TypeFunction *)t;
    }

    if (fd && fd->isMember2())
    {
        AggregateDeclaration *ad = fd->isThis();

        if (ad)
        {
            ethis = ec;
            if (ad->isStructDeclaration() && ectype->toBasetype()->ty != Tpointer)
                ethis = ethis->addressOf(NULL);
        }
        else
        {
		// it is probably static...
		// FIXME this is another hack that probably won't work in real D stuff
		ClassDeclaration* cd = fd->isMember2()->isClassDeclaration();
		assert(cd);
		sink(cd->toChars());
		sink(".");
		sink(ec->toChars());
		goto arguments_time;
        }

        if (!fd->isVirtual() ||
            directcall ||
            fd->isFinal())
        {
            ec = new VarExp(0, fd);
        }
        else
        {
		// virtual function
		useDotSyntax = 1;
		useVtbl = 1;
        }
    }

    //if (tf->isref)
     //   sink("*");


     /* HACK: if this is an opAssign, we need to actually assign the this when we call */
     if(fd && ethis && strcmp(fd->ident->toChars(), "opAssign") == 0) {
		// FIXME: this is a filthy hack, since the this isn't done by reference I think.
		ethis->toMicroD(sink);
		sink(" = ");
     }

   if(useDotSyntax && ethis && fd && !fd->isCtorDeclaration()) {
        ethis->toMicroD(sink);
        sink(".");
	if(useVtbl)
		sink("__d_vtbl[%d]", fd->vtblIndex);
	else
	sink(ec->toChars()); // original name so JS can see it
   } else {
    // mangled name
        ec->toMicroD(sink);
   }
 arguments_time:
   int putComma = 0;

   if(fd && fd->isCtorDeclaration() && ethis) {
	sink(".call(");
	putComma = 1;
	ethis->toMicroD(sink);
   } else
       sink("(");

    if (arguments)
    {
        int j = (tf && tf->linkage == LINKd && tf->varargs == 1);

        for (size_t i = 0; i < arguments->dim; i++)
        {
            if (i != 0 || putComma)
                sink(", ");

		int done = 0;
            Expression *arg = (*arguments)[i];
            size_t nparams = Parameter::dim(tf->parameters);
            if (i - j < nparams && i >= j)
            {
                Parameter *p = Parameter::getNth(tf->parameters, i - j);

                if (p->storageClass & (STCout | STCref)) {
			sinkRefArg(sink, arg);
			done = 1;
		} else if(dynamic_cast<TypeStruct*>(arg->type)) {
			// we have to pass structs by value, which means copying them here
			sink("__d_struct_copy(");
				arg->toMicroD(sink);
			sink(")");

			done = 1;
		}
            }

	    if(!done)
            arg->toMicroD(sink);
        }
    }

    if ((!useDotSyntax || useVtbl) && ethis)
    {
        if (arguments && arguments->dim)
            sink(", ");

	ethis->toMicroD(sink);
    }
    sink(")");
}

void escapeString(md_fptr sink, StringExp *se)
{
    sink("\"");
    for (size_t i = 0; i < se->len; i++)
    {
        unsigned c = se->charAt(i);

        switch (c)
        {
            case '"':
            case '\\':
                sink("\\");
            default:
                if (c <= 0xFF)
                {   if (c <= 0x7F && isprint(c))
                        sink("%c", c);
                    else
                        sink("\\x%02x", c);
                }
                else if (c <= 0xFFFF)
                    sink("\\x%02x\\x%02x", c & 0xFF, c >> 8);
                else
                    sink("\\x%02x\\x%02x\\x%02x\\x%02x",
                        c & 0xFF, (c >> 8) & 0xFF, (c >> 16) & 0xFF, c >> 24);
                break;
        }
    }
    sink("\"");
}
