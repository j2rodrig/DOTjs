window.compile = (input, stopAfter) ->
	try
		clearLog()

		tokens = tokenize(input)

		if stopAfter == "tokens"
			return (for tok in tokens
				tok.print()).join('\n')

		ast = parse(tokens)

		if stopAfter == "trees"
			return ast.print(0)

		predefCtx = createPredefContext()   # create a context for predefined types
		doTypeCompleters(ast, predefCtx.fresh(ast))   # generate subcontexts and info() functions

		if stopAfter == "symbols"
			printSymbolTables(ast)

		outputBuffer = []
		genConstructor(ast, predefCtx, 0, outputBuffer)
		outputBuffer.push(";")
		output = outputBuffer.join("")

		logText = if channels[stderr] then "/** Stderr log:\n\n" + channels[stderr].join("\n") + "\n**/" else ""

		return [output, logText].join("\n\n")

	catch error
		message = if error.message? then error.message else error
		message = if message.toUpperCase().startsWith("ERROR") or message.toUpperCase().startsWith("INTERNAL COMPILER ERROR") then message else "Error: " + message
		stacktrace = if error.stack? then "COMPILER STACKTRACE:\n" + error.stack else ""
		logText = if channels[stderr] then "Stderr log:\n\n" + channels[stderr].join("\n") else ""
		return [message, logText, stacktrace].join("\n\n")


channels = {}

stderr = "stderr"

clearLog = () ->
	channels = {}

log = (ch, msg) ->
	if not channels[ch]
		channels[ch] = [msg]
	else
		channels[ch].push msg

###

NOTES

Compilers are Databases

	Should I structure this compiler like Odersky's core ER (Entity Relationship) diagram?
	Yes, that seems like a good idea.

	Should I literally build tables of entities here?
	No. But something more flexible than what Martin did is a good idea.

	Is the flexibility issue I'm seeing an interface problem?
	Yes.

	How do I do infterfaces better?
	Just think - ...

What's a Type?

	A type is what we know (or assume) about something.

	A type may be associated with a tree (but it doesn't have to be).
	A type may be associated with a symbol (but it doesn't have to be).

	So what does a type do?

	What do we want to do with a type?

	We want to make sure that for every term selection p.x, p contains x.
	We want to make sure that for every type selection p.T, p contains T.
	We want to make sure that for every term assignment a = b, b is substitutable for a.
	We want to make sure that for every term assignment a = b, a is assignable.
	(Assignability is [among other things] related to variance and privacy: a field is not writable/assignable if its type is covariant and non-private [which is notably the case for all fields in DOT].)
	We want to make sure that for every instance creation T.new, all needed members of T are known.
	For every declaration block '{ stmts }', we want to know what declarations it contains.
	The type of a statement block must be related to: 1. The declarations in that block (which may be inferred), and 2. the sequence of assignments in that block (term and type assignments).

	What about subtyping?
	'{ stmts1 }' <: '{ stmts2 }' if for every declaration in stmts2 there is a compatible declaration in stmts1. That is, for all D2 in stmts2, there exists a D1 in stmts1 s.t. D1 <: D2. This interpretation of statement-block subtyping is compatible with the idea that the type of a statement block is the intersection of all declarations in that block.


	Declaration subsumption
	We only have 2 kinds of declarations.
	Type declarations have the form 'ID : A .. B' where A and B are types.
	Term declarations have the form 'id : T' where T is a type.

	'id1:T1' <: 'id2:T2' if T1 == T2. (May be relaxed if T1 or T2 is covariant or contravariant.)

	'ID1:A1..B1 <: ID2:A2..B2' if A2 <: A1 and B1 <: B2.


	Inheritance of Field Types
	Despite DOT, it seems like field types should be invariant under inheritance, unless stated otherwise.
	What does this mean for subtyping?

	Scala has separate notions of a getter and setter.
	Say, for example, A <: B. And:
		trait D { var f: A }
		trait E extends D { var f: B = ??? }
	If we try
		new E{}
	Scala won't take it because the setter for f:A has not been defined.
	The getter for f:A is overridden by f:B, so that part's OK.

	Maybe we need to find out how getters and setters work in DOTjs:
	{
		f: A
		GetF = {
			out value: A
			value = f
		}
		SetF = {
			in value: A
			f = value
		}
	}
	Calling:
	{
		fOut = GetF.new.value
		SetF{ value = fIn }.new
	}
	Mixing in:
	{
		f: B
		GetF = {  // presence of public getter constrains f's type <: A&B
			out value: B  // "out" means there's no way to assign outside of this object*
			value = f
		}
		SetF = {  // presence of public setter constrains A|B <: f's type
			in value: B   // "in" means there's no way to read outside of this object**
			f = value
		}
	}
	* Assignments to the value can occur within the statement block where the value is declared.
	  Field f can be arbitrarily assigned within the block because mixin composition occurs
	  over such assignments, and they can be type-checked at the time of object instantiation.
	** Reads of the value can occur within the statement block where the value is declared.
	  Like assignments, reads of values within the statement block are type-checked at the
	  point of object creation. Access to the final type of the field allows this.


	Mixins, declarations, and assignments

	Declarations are order-agnostic. Regardless of mixin ordering, all declarations must be satisfied.
	Satisfaction of declarations means:
		For every declared type T, the upper bound must be no less than the lower bound.
		All assignments to T must be within those bounds.
		For every publically-readable field fo declared with type FO, FO serves as an upper bound
		of the actual type of fo. For every publically-writable field fi with type FI, FI serves
		as a lower bound of the actual type of fi.

	Assignments are order-dependent.

	Type assignments must be evaluated at compile time.
	Term assignments may be evaluated at runtime.

	A type assignment remains in effect only until the type is re-assigned
	(a type assignment is a temporary narrowing of type bounds).

	Here's the key:
	Declarations participate in the static type of an object, but assignments do not.
	(Although it is possible to infer certain declarations given a set of assignments.)

	Example of type assignment:
	J = {
		L = Int
		f: L
		f = 3
		L = String  // changes the type of L for subsequent statements
		g: L
		g = "Hi!"
	}
	j = J.new
	l: j.L   // j.L is a string here, since that was the last assignment to L in j
	l = "Hi again!"

	Key note: (
		All term members start as undefined, all type members as Undefined.
		When are errors generated on use of undefined or Undefined?
	)

	Path-dependent subtyping rules allow j.L to be equal to j.L,
	but another path k.L is not necessarily equal to j.L.

(Triple venti vanilla frappucino)


###

###
APPROACH TO TYPE CHECKING

A function to get the bounds on a tree's type. (What's the result here?)

A function to get the declarations on a tree's type. There are lower- and upper-bound versions.

A function to get the assignments on a tree's type. Ther result is always a constructible lower bound.


HOW TO TYPECHECK: A & { x = y } . new

Register a new context for A & { x = y }    # reflects creation of new object
Linearize statements in A & { x = y }
Resolve and check explicit declarations in A & { x = y }
	(the declarations in A are thereby entered into the newly-created current context.)
Generate type aliases from type assignments (and check that they are within declared bounds).
Infer field types (term declarations) from term assignments (where needed).

Specific to { x = y }:
	Check that y.type <: x.widen.
	Which involves:
		Look up y in the context where y is used (in this case, the newly-created current context)
		Look up x in the context where x is used (in this case, the newly-created current context)
Generalization:
	Check that term assignments have compatible types.
	The type of a path p is simply p itself.
	If necessary, p is widened to its declared type.

Path-dependence and A:
	( assume A is { y: Y;  y = a } )
	Lookup of y from { x = y } produces type Y, which may be in A's outer context.
	( assume { Y: at least L at most U ; A = { y: Y;  y = a } } )
	The type of p.y in "p = A & { x = y } . new" is: p.Y
		because Y is invariant with respect to a particular object reference p.
	So Y without a prefix is always equal to Y without a prefix, and p.Y === p.Y.
		But: Y != p.Y and p.Y != q.Y  ---> path-dependence.
		(unless Y is aliased to another type which does compare.)

Code Generation

{
	A : at least {
		y: Y
		y = ???
	}

	bar = A & { x = y }.new
	bar.x
}

(function (c0) {
	c0.A = function (c1) {
		c1.y = throw "Not Implemented";
	};
	c0.bar = (function (c2) {
		c0.A(c2);
		c2.x = c2.y;
		return c2;   // return is only generated for ".new"
	})({});
	c0.bar.x;
	return c0;
})({});

###

###
Progress Notes, June 14, 2016.

	It seems that I should do an overhaul of how contexts are generated and used.
Specifically, contexts should be given unique names. All user-specified names without
prefixes are prefixed with the appropriate context name.

	My previous approach is probably incorrect in another way also. Previously, I was
assuming that all statements in all constructors could be simply linearized upon
instantiation. However, that approach does not account for the possibility that
constructors will access names in their enclosing contexts. Instead, I now think that
the linearization really needs to identify not merely inherited statements, but rather
the appropriate base-class constructors. These constructors ought to be called as
functions in linearization order.

	Javascript will handle referencing enclosing contexts via is closure mechanism.

Notes, June 15

	Name mangling: If I want to support custom/hidden/private(?) attributes,
I can use a name starting with a low-frequency letter (e.g., "q"). Some escape pattern
can be used for any user names that happen to start with that letter.

	For private fields, perhaps codegen can produce Javascript variables. The closure
mechanism will still be able to access those variables, but they will never be present
within derived types. 

	How do I proceed?
	1. Codegen. Write it out.
	2. ...

Notes, June 17

	On membership:
	The reasons I need to know about membership are:
	1. To determine whether a name selection is always valid (either in the current context, constructor context, or prefix context),
	2. To find out which constructors should be called on named type instantiation.

	Abstract execution plan:
	1. Generate code for constructors. Which depends on:
		a. Finding a sequence of base trees.
		a1. Looking up base trees from named types in the current or enclosing contexts.
			b1. Name declarations must be registered in their current contexts.
			b2. Looking up declarations in a constructor context must search base trees for matching declarations.
				c1. 
		a2. 


June 19.

	Due to the recurive nature of path-dependent typing, I am now skeptical that a simple bottom-up approach to typing
and linearization will work. Finding the complete membership of a type involves finding membership of its term prefix,
which involves finding the membership of that term's type.

	First, we need to be able to move from contexts to trees. This will allow examination of type trees to determine
members, base types, etc.

	Second, we may need a findMember that searches type trees for specific named members. The inputs to findMember are
a prefix type tree and a name. The result of findMember is a type tree. To support unions and intersections, synthetic type trees
may be created.*

	Third, we need a findMember that searches within a context. If searching a constructor context, we switch to the
findMember that searches through type trees.

*There is a canonical form for any type tree: (S1 & ... & SN) | ... | (T1 & ... & TM) where every Sn and Tm is a
statement block.

June 21.

	How do we generate mixin constructors?

	Say we have:
		T : { a } & { b }
	When we go to construct an instance of T:
		T.new
	we need to have a mixin constructor for T that builds an object with a type compatiable with T.
	Compatibility with T means that the constructed object's type must be compatible with T's lower bound.

	As for the statments that go into T's mixin constructor, we can select any statements we want.
	However, we should at least make an effort to ensure that all fields declared in T's lower bound get initialized
	and initialized in a reasonable order, even if the lower bound of T contains union types.
	The solution here is to traverse the lower-bound type of T all the way down to concrete statements,
	and generate all term-like statements in the order that they appear.
	For consistency, we may say that Nothing contains no statements (although it contains all possible
	declarations). By saying that Nothing contains no statements, the lower bound of an intersection type
	A & B -- although quite possibly containing a union with Nothing -- will still be constructible and
	generate all expected statements. There is still an issue with implementation inheritance, however:
	after narrowing a type member's bounds, one would expect that the statements in a newly-declared
	lower bound would supercede -- not append to -- statements in the previously-declared lower bound.

	The issue of implementation inheritance would benefit from some more thought...

	For now, it suffices to say that side-effect-free constructors called in linearization order should
	produce a reasonable result; term-member initializations override any prior conflicting initializations
	at runtime, and indeed unneeded prior initializations are potentially elidable through optimization.

	Perhaps the best thing to do here is try some examples after codegen is completed.


	Another issue is what to do about out-of-order statements. For now, nothing. Ideally, statements
would be reordered based on depenency. But this doesn't have to happen yet.


June 24.

	I may need to re-think exactly how/when symbols are added to contexts. There are problems with circular references in symbol lookups.

	1. Remove contexts on STATEMENTS trees, leaving only constructor/mixin-constructor contexts.
	2. Constructor membership is evaluated lazily. Basically, requesting a member of a context forces
	   computation of the entire memberhsip set for that context. For each constructor, the membership
	   set is always computed before any element is selected from it.

	Possible way to break this approach:
		x: L
		L: x.K   // the membership of L depends on a member of L. It's probably OK to treat this as an error

	Possible counter-counter example:
	L: {
		H: at most L   // OK. The mixin context surrounding L here is evaluated lazily, so all members of L are established before we get here.
	}

July 2.

	The problem of symbol lookup seems to be solved. Up next: Type comparison.

###

Any =
	type: "ANY"
	line: "(built-in)"
	column: "(built-in)"

Nothing =
	type: "NOTHING"
	line: "(built-in)"
	column: "(built-in)"

TakeLowerBound = (underlying) ->
	type: "TAKE-LOWER-BOUND"
	underlying: underlying
	line: "(built-in)"
	column: "(built-in)"

AndType = (lhsTyp, rhsTyp) ->
	type: "AND-TYPE"
	lhs: lhsTyp
	rhs: rhsTyp
	line: "(built-in)"
	column: "(built-in)"

OrType = (lhsTyp, rhsTyp) ->
	type: "OR-TYPE"
	lhs: lhsTyp
	rhs: rhsTyp
	line: "(built-in)"
	column: "(built-in)"

TypeBounds = (typLower, typUpper) ->
	type: "TYPE-BOUNDS"
	lower: typLower
	upper: typUpper


### TYPE OPERATIONS ###

derivedTypeBounds = (tree, lower, upper) ->
	if lower is tree.lower and upper is tree.upper
		tree
	else
		TypeBounds(lower, upper)

derivedAndOrType = (tree, lhs, rhs) ->
	if lhs is tree.lhs and rhs is tree.rhs
		tree
	else if tree.type is "AND-TYPE"
		AndType(lhs, rhs)
	else if tree.type is "OR-TYPE"
		OrType(lhs, rhs)

lowerBound = (tree) ->
	if tree.type is "TYPE-BOUNDS"
		tree.lower
	else
		tree

upperBound = (tree) ->
	if tree.type is "TYPE-BOUNDS"
		tree.upper
	else
		tree

simplifyType = (tree) ->

	if tree.type is "TYPE-BOUNDS"
		tree2 = derivedTypeBounds(tree, simplifyType(tree.lower), simplifyType(tree.upper))
		if tree2.lower is tree2.upper   # if bounds are equivalent, then just return one of them
			tree2.lower
		else
			tree2

	else if tree.type is "AND-TYPE"
		tree2 = derivedAndOrType(tree, simplifyType(tree.lhs), simplifyType(tree.rhs))
		if tree2.lhs is tree2.rhs       # if components are equivalent, then just return one of them
			tree2.lhs
		else if tree2.lhs is Nothing or tree2.rhs is Nothing   # intersection with Nothing === Nothing
			Nothing
		else if tree2.lhs is Any   # intersection with Any is redundant
			tree2.rhs
		else if tree2.rhs is Any
			tree2.lhs
		else
			tree2

	else if tree.type is "OR-TYPE"
		tree2 = derivedAndOrType(tree, simplifyType(tree.lhs), simplifyType(tree.rhs))
		if tree2.lhs is tree2.rhs       # if components are equivalent, then just return one of them
			tree2.lhs
		else if tree2.lhs is Any or tree2.rhs is Any   # union with Any === Any
			Any
		else if tree2.lhs is Nothing   # union with Nothing is redundant
			tree2.rhs
		else if tree2.rhs is Nothing
			tree2.lhs
		else
			tree2

	else
		tree


### CONTEXTS AND SYMBOL LOOKUP ###

createPredefContext = () ->
	predefTree =
		type: "STATEMENTS"
		statements: []
	predefTree.statements.push TypeDecl(
		Token("ID", "Any", undefined, undefined),
		Any, Any
	)
	predefTree.statements.push TypeDecl(
		Token("ID", "Nothing", undefined, undefined),
		Nothing, Nothing
	)
	predefTree.statements.push TermDecl(
		Token("ID", "???", undefined, undefined), Nothing
	)
	ctx = freshContext(undefined, predefTree)
	Any.ctx = ctx   # hack: make the contexts of predefined types point to the predef context
	Nothing.ctx = ctx
	ctx


freshContext = (outer, typTree) ->
	ctx = {}

	if outer
		ctx.nestLevel = outer.nestLevel + 1
		ctx.outer = outer
	else
		ctx.nestLevel = 0
		ctx.outer = undefined

	ctx.indents = tabs(ctx.nestLevel)

	ctx.name = "c#{ctx.nestLevel}"

	ctx.fresh = (typTree) -> freshContext(ctx, typTree)

	# Notes on findMember:
	#  Always search on the lower bound of the context's tree. The lower bound contains the members that are actually included during construction.
	ctx.findMember = (name) ->
		asConstructed = typeAsConstructed(typTree, ctx.outer)
		findMember(name, asConstructed, ctx.outer, true)

	ctx

findMember = (name, typTree, ctx, returnLowerBound) ->  # params: name to find, type tree to look into, enclosing context to resolve type/term names in the type tree

	if typTree.type is "STATEMENTS"
		found = undefined
		for st in typTree.statements
			if st.type is "TYPE-DECL" and st.lhs.match is name
				if found then throw new Error("Duplicate definition of '#{name}' on line #{st.lhs.line} character #{st.lhs.column}")
				found = if returnLowerBound then st.rhsLower else st.rhsUpper
			else if st.type is "TERM-DECL" and st.lhs.match is name
				if found then throw new Error("Duplicate definition of '#{name}' on line #{st.lhs.line} character #{st.lhs.column}")
				found = st.rhs
		found

	else if typTree.type is "ANY"
		undefined

	else if typTree.type is "NOTHING"
		throw new Error("Attempt to find member '#{name}' in type Nothing, which contains contradictory definitions of '#{name}'.")
		# Note on Nothing: (July 2, 2016)
		#   Nothing contains all possible members, which means that for any given name,
		# Nothing contains contradictory definitions. Since we can't return anything sensical,
		# we throw an exception.
		#   There is the possibility of a type that contains contradictory definitions for
		# some names, but not for others. For example, the ReadonlyNothing type would return
		# a result for the mutability member, but not for other members.

	else if typTree.type is "ID"
		widenedIdTree = widen(typTree, ctx)
		findMember(name, widenedIdTree, widenedIdTree.ctx, returnLowerBound)

	else if typTree.type is "TYPE-SELECT"
		widenedTyp = widen(typTree, ctx)
		findMember(name, widenedTyp, widenedTyp.ctx, returnLowerBound)

	else if typTree.type is "AND-TYPE"
		lhsType = findMember(name, typTree.lhs, ctx, returnLowerBound)
		rhsType = findMember(name, typTree.rhs, ctx, returnLowerBound)
		if (not lhsType) or (lhsType is rhsType)
			rhsType
		else if not rhsType
			lhsType
		else
			AndType(lhsType, rhsType)

	else
		throw new Error("Internal compiler error: Unexpected #{typTree.type} tree in findMember")

widen = (tree, ctx, returnLowerBound) ->
	if tree.type is "id"
		requireMemberInContext(tree.match, ctx, tree)
	else if tree.type is "ID"
		requireMemberInContext(tree.match, ctx, tree, returnLowerBound)
	else if tree.type is "TERM-SELECT"
		prefixTyp = widen(tree.prefix, ctx)
		requireMemberInType(tree.id, prefixTyp, tree)
	else if tree.type is "TYPE-SELECT"
		prefixTyp = widen(tree.prefix, ctx)
		requireMemberInType(tree.ID, prefixTyp, tree, returnLowerBound)
	else if tree.type is "CONSTRUCT"
		typeAsConstructed(tree.typTree, ctx)
	else
		throw new Error("Unexpected #{tree.type} tree in widen")

findMemberInContext = (name, ctx) ->
	if not ctx
		undefined
	else
		found = ctx.findMember(name)
		if found
			found
		else
			findMemberInContext(name, ctx.outer)

# Finds the context that defines the given name, if it is in ctx or enclosing.
getDefContext = (name, ctx) ->
	if not ctx
		undefined
	else
		if ctx.findMember(name)
			ctx
		else
			getDefContext(name, ctx.outer)

# Throws an error if the given name is not defined in the given or enclosing contexts.
requireMemberInContext = (name, ctx, sourceTree) ->
	typTree = findMemberInContext(name, ctx)
	if not typTree
		throw new Error("Name '#{name}' is not defined at line #{sourceTree.line} character #{sourceTree.column}")
	typTree

requireMemberInType = (name, typTree, sourceTree, returnLowerBound) ->
	found = findMember(name, typTree, typTree.ctx, returnLowerBound)
	if not found
		throw new Error("Member '#{name}' at line #{sourceTree.line} character #{sourceTree.column} could not be found")
	found

requireDefContext = (name, ctx, sourceTree) ->
	found = getDefContext(name, ctx)
	if not found
		throw new Error("Name '#{name}' is not defined at line #{sourceTree.line} character #{sourceTree.column}")
	found


### BASE/CONSTRUCTOR TYPE QUERIES ###

typeAsConstructed = (typTree, ctx) ->

	# We return the intersection base types here (instead of the original type tree).
	# This allows us to look at the membership of the object as actually constructed, rather than
	#  a conservative upper-bound approximation.
	typ = Any
	for block in findBaseStatementBlocks(typTree, ctx)
		typ = AndType(typ, block)
	typ

findBaseStatementBlocks = (typTree, ctx) ->

	if typTree._baseStatementBlocks
		return typTree._baseStatementBlocks

	statementsFound = []
	basesSeen = []

	for base in getBaseTypes(typTree)
		if not (base in basesSeen)
			basesSeen.push base
			if base.type is "STATEMENTS"
				statementsFound.push base
			else if base.type in ["ID", "TYPE-SELECT"]
				widenedType = widen(base, ctx, true)
				for stmts in findBaseStatementBlocks(widenedType, widenedType.ctx.outer)
					if not (stmts in basesSeen)
						basesSeen.push stmts
						statementsFound.push stmts
			else if base.type is Any or base.type is Nothing
				statementsFound.push base
			else
				throw new Error("Internal complier error: unexpected base tree type #{base.type} in findBaseStatementBlocks")

	typTree._baseStatementBlocks = statementsFound
	statementsFound

getBaseTypes = (typTree) ->

	if typTree.type in ["ID", "TYPE-SELECT"]
		[typTree]
	else if typTree.type is "TYPE-BOUNDS"
		# Get lower bound of TypeBounds types.
		getBaseTypes(typTree.lower)
	else if typTree.type is "AND-TYPE"
		# AndTypes include bases from both the left-hand side and the right-hand side of the AndType.
		getBaseTypes(typTree.lhs).concat(getBaseTypes(typTree.rhs))
	else if typTree.type is "OR-TYPE"
		# Choose either the right-hand side or the left-hand side of the OrType.
		# Here, we choose the left-hand side unless one of its base types is Nothing.
		# (NOTE I don't follow type aliases here, so it is still possible that the LHS is
		#  non-constructible even if none of its immediate bases is Nothing.
		#  I don't know if this behaviour is reasonable or not.)
		lhsBases = getBaseTypes(typTree.lhs)
		rhsBases = getBaseTypes(typTree.rhs)
		for b in lhsBases
			if b is Nothing or b.match is "Nothing"
				return rhsBases
		lhsBases
	else if typTree.type is "STATEMENTS"
		[typTree]
	else
		throw new Error("Internal compiler error: Expected a type tree in getBaseTypes, got #{typTree.type} tree")



### LAZY INFO FUNCTIONS ... TODO: Do we really need these? ###

doTypeCompleters = (tree, ctx) ->

	tree.ctx = ctx

	if tree.type is "STATEMENTS"
		for st in tree.statements
			doStatementCompleters(st, tree.ctx)

	else if tree.type is "ID"
		# TODO?

	else if tree.type is "TYPE-SELECT"
		doTermCompleters(tree.prefix, ctx)

	else if tree.type is "AND-TYPE" or tree.type is "OR-TYPE"
		doTypeCompleters(tree.lhs, ctx)
		doTypeCompleters(tree.rhs, ctx)

	else
		throw new Error("Unexpected #{tree.type} tree in doTypeCompleters")


doTermCompleters = (tree, ctx) ->

	if tree.type is "id"
		tree.info = () ->
			requireMemberInContext(tree.match, ctx, tree)

	else if tree.type is "TERM-SELECT"
		tree.info = () ->
			requireMemberInType(tree.id, tree.prefix.info(), tree)
		doTermCompleters(tree.prefix, ctx)

	else if tree.type is "CONSTRUCT"
		ctx = ctx.fresh(tree.typTree)
		# Note on info() functions: The invariant of info() is that it always returns a type tree (not a statement or a term).
		# There are at least two variants on info(): return the type tree as-is, or return a STATEMENTS tree containing linearized declarations.
		#  (We do the former here.)
		tree.info = () ->
			tree.typTree
		doTypeCompleters(tree.typTree, ctx)

	else
		throw new Error("Unexpected #{tree.type} tree in doTermCompleters")

doStatementCompleters = (tree, ctx) ->
	if tree.type is "TERM-DECL"
		doTypeCompleters(tree.rhs, ctx)

	else if tree.type is "TYPE-DECL"
		doTypeCompleters(tree.rhsLower, ctx.fresh(tree.rhsLower))
		doTypeCompleters(tree.rhsUpper, ctx.fresh(tree.rhsUpper))

	else if tree.type is "TYPE-ASSIGN"
		doTypeCompleters(tree.lhs, ctx)
		doTypeCompleters(tree.rhs, ctx)

	else if tree.type is "TERM-ASSIGN"
		doTermCompleters(tree.lhs, ctx)
		doTermCompleters(tree.rhs, ctx)

	else
		doTermCompleters(tree, ctx)  # assume anything else is a term


### CODEGEN ###

gen = (tree, ctx, indent, output) ->

	# On statement ordering

	if tree.type is "STATEMENTS"
		for st in tree.statements
			if st.type is "TYPE-DECL"
				output.push(tabs(indent))
				defCtx = requireDefContext(st.lhs.match, ctx, tree)
				output.push("#{defCtx.name}.#{st.lhs.match}")
				output.push(" = ")
				genInitializer(st.rhsLower, indent, output)
				output.push(";\n")

		for st in tree.statements
			if st.type is "TERM-ASSIGN"
				lhsType = st.lhs.info()
				rhsType = st.rhs.info()
				# TODO: check for rhs <: lhs compatibility
				output.push(tabs(indent))
				if st.guard
					output.push("if(")
					gen(st.guard.condition, ctx, indent, output)
					output.push("){ ")
				gen(st.lhs, ctx, indent, output)
				output.push(" = ")
				gen(st.rhs, ctx, indent, output)
				if st.guard
					output.push(" }")
				output.push(";\n")
			else if st.type in ["id", "TERM-SELECT", "CONSTRUCT"]
				output.push(tabs(indent))
				if st.guard
					output.push("if(")
					gen(st.guard.condition, ctx, indent, output)
					output.push("){ ")
				gen(st, ctx, indent, output)
				if st.guard
					output.push(" }")
				output.push(";\n")
			else
				if st.guard
					throw new Error("Unexpected guard on #{st.type} statement on line #{st.guard.line}")

	else if tree.type is "CONSTRUCT"
		genConstructor(tree.typTree, ctx, indent, output)

	else if tree.type is "id"
		if tree.match is "???"
			output.push("(function(){ throw new Error('Not Implemented'); })()")
		else
			defCtx = requireDefContext(tree.match, ctx, tree)
			output.push("#{defCtx.name}.#{tree.match}")

	else if tree.type is "TERM-SELECT"
		prefixType = widen(tree.prefix, ctx)
		requireMemberInType(tree.id, prefixType, tree)  # Typecheck: make sure id exists in prefix type
		gen(tree.prefix, ctx, indent, output)
		output.push(".")
		output.push(tree.id)

genInitializer = (tree, indent, output) ->
	ctx = tree.ctx
	output.push("function(#{ctx.name}){\n")
	bases = getBaseTypes(tree)   # TODO remove duplicates?

	# Here, generate statements only. Calls to other initializers should really be hoisted into constructors
	for base in bases
		if base.type is "STATEMENTS"
			gen(base, ctx, indent + 1, output)

	output.push(tabs(indent + 1))
	output.push("return #{ctx.name};\n")
	output.push(tabs(indent))
	output.push("}")

genConstructor = (tree, outer, indent, output) ->
	ctx = tree.ctx
	output.push("(function(#{ctx.name}){\n")
	bases = getBaseTypes(tree)   # TODO remove duplicates?

	for base in bases
		if base.type is "STATEMENTS"
			gen(base, ctx, indent + 1, output)
		else if base.type is "ID"
			defCtx = requireDefContext(base.match, outer, base)
			output.push(tabs(indent + 1))
			output.push("#{defCtx.name}.#{base.match}(#{ctx.name});\n")
		else if base.type is "TYPE-SELECT"
			output.push(tabs(indent + 1))
			gen(base.prefix, outer, indent + 1, output)
			output.push(".#{base.ID}(#{ctx.name});\n")
		else if base.type is "ANY"
			# don't need to do anything with Any
		else if base.type is "NOTHING"
			throw new Error("Cannot construct an object with a base class of Nothing. Constructor at line #{tree.line} character #{tree.column}")
		else
			throw new Error("Internal compiler error: Unexpected base type tree #{base.type} in genConstructor. Line #{tree.line} character #{tree.column}")

	output.push(tabs(indent + 1))
	output.push("return #{ctx.name};\n")
	output.push(tabs(indent))
	output.push("})({})")


### PARSER ###

Token = (tokType, text, line, column) ->
	tk =
		type: tokType
		match: text
		line: line
		column: column
		isToken: true
	tk.stringify = () -> tk.match.replace('\n', '\\n')
	tk.print = () -> "#{tk.type}, \"#{tk.match.replace('\n', '\\n')}\", line #{tk.line}, character #{tk.column}"
	tk

TypeDecl = (lhs, rhsLower, rhsUpper) ->
	t =
		type: "TYPE-DECL"
		alttypes: ["STATEMENT"]
		lhs: lhs
		rhsLower: rhsLower
		rhsUpper: rhsUpper
		line: lhs.line
		column: lhs.column
	t.stringify = (indent) -> t.lhs.stringify(indent) +
		": at most " + t.rhsUpper.stringify(indent) +
		" at least " + t.rhsLower.stringify(indent)
	t.subtrees = () -> [t.lhs, t.rhsLower, t.rhsUpper]
	t

TermDecl = (lhs, rhs) ->
	t =
		type: "TERM-DECL"
		alttypes: ["STATEMENT"]
		lhs: lhs
		rhs: rhs
		line: lhs.line
		column: lhs.column
	t.stringify = (indent) -> t.lhs.stringify(indent) + ": " + t.rhs.stringify(indent)
	t.subtrees = () -> [t.lhs, t.rhs]
	t

WithGuard = (guard, statement) ->
	statement.guard = guard
	prevStringify = statement.stringify
	statement.stringify = (indent) -> guard.stringify(indent) + prevStringify(indent)
	prevSubtrees = statement.subtrees
	statement.subtrees = () -> [statement.guard].concat(prevSubtrees())
	statement

parse = (tokens) ->

	stack = []

	unreducedTokenCount = () ->
		for i in [1..stack.length]
			if not stack[stack.length - i].isToken
				return i - 1
		return stack.length

	matches = (types, skip = 0) ->
		if types.length <= stack.length - skip
			for i in [0..types.length - 1]
				if types[i] != "*"  # always match if the given type is "*"
					elem = stack[stack.length - types.length + i - skip]
					# fail the match if neither elem.type not elem.alttypes has the needed type
					if elem.type != types[i] and not (elem.alttypes and (types[i] in elem.alttypes))
						return false
			true
		else
			false

	fromTopOfStack = (i = 0) ->
		if i > stack.length - 1
			undefined
		else
			stack[stack.length - 1 - i]

	shift = () ->
		t = tokens.shift()
		if t.type == "id" then t.alttypes = ["TERM"]   # note that an id is also a term
		if t.type == "ID" then t.alttypes = ["TYPE"]   # note that an ID is also a type
		stack.push t

	expected = (description) ->
		if stack.length > 0
			t = stack[stack.length - 1]
			value = if t.isToken then t.match.replace('\n', '\\n') else t.stringify(0)
			throw "Parse error on line #{t.line} character #{t.column} : Expected #{description}; got #{t.type} with value \"#{value}\""
		else
			throw "Parse error with empty stack: Expected #{description}"

	reduce = () ->
		# Try to perform a reduction.
		# Returns true if a reduction is performed, false if more input is needed.
		# Throws an exception if parsing fails.

		### Handle Comments ###

		if matches ["COMMENT"]
			# remove line comments
			stack.pop()
			return true

		if matches(["START-BLOCK-COMMENT", "END-BLOCK-COMMENT"])
			# remove completed block comment
			stack.pop()
			stack.pop()
			return true

		if matches(["START-BLOCK-COMMENT", "START-BLOCK-COMMENT"])
			# start of nested block comment - nothing needs to be done here
			return false  # to indicate that no change was made to the stack

		if matches(["START-BLOCK-COMMENT", "*"])
			# Consume tokens inside comment
			stack.pop()
			return true

		### Recognize ids that are really keywords ###

		if matches(["id"])
			if fromTopOfStack(0).match is "new"
				fromTopOfStack(0).type = "NEW"
				fromTopOfStack(0).alttypes = undefined
				return true
			if fromTopOfStack(0).match is "if"
				fromTopOfStack(0).type = "IF"
				fromTopOfStack(0).alttypes = undefined
				return true
			if fromTopOfStack(0).match is "then"
				fromTopOfStack(0).type = "THEN"
				fromTopOfStack(0).alttypes = undefined
				return true
			if fromTopOfStack(0).match is "outer"
				fromTopOfStack(0).type = "OUTER"
				fromTopOfStack(0).alttypes = undefined
				return true

		if matches(["id", "id"])
			a = fromTopOfStack(1)
			b = fromTopOfStack(0)
			if a.match is "at" and b.match is "least"
				stack.pop()
				a.type = "ATLEAST"
				a.match = a.match + " " + b.match
				a.alttypes = undefined
				return true
			if a.match is "at" and b.match is "most"
				stack.pop()
				a.type = "ATMOST"
				a.match = a.match + " " + b.match
				a.alttypes = undefined
				return true

		### Selections ###

		if matches(["IF", "TERM", "THEN"])
			stack.pop()
			condition = stack.pop()
			stack.pop()
			guard =
				type: "GUARD"
				condition: condition
				line: condition.line
				column: condition.column
			guard.stringify = (indent) -> "if #{guard.condition.stringify(indent)} then "
			guard.subtrees = () -> [guard.condition]
			stack.push guard
			return true

		if matches(["GUARD", "STATEMENT"])
			statement = stack.pop()
			guard = stack.pop()
			stack.push WithGuard(guard, statement)
			return true

		if matches(["GUARD", "*", "NEWLINE"])
			nl = stack.pop()
			term = stack.pop()
			guard = stack.pop()
			stack.push WithGuard(guard, term)
			stack.push nl
			return true

		if matches(["TERM", "DOT", "id"])
			id = stack.pop()
			stack.pop()
			prefix = stack.pop()
			t =
				type: "TERM-SELECT"
				alttypes: ["TERM"]
				prefix: prefix
				id: id.match
				line: id.line
				column: id.column
			t.stringify = (indent) -> t.prefix.stringify(indent) + ".#{t.id}"
			t.subtrees = () -> [t.prefix]
			stack.push t
			return true

		if matches(["TERM", "DOT", "ID"])
			ID = stack.pop()
			stack.pop()
			prefix = stack.pop()
			t =
				type: "TYPE-SELECT"
				alttypes: ["TYPE"]
				prefix: prefix
				ID: ID.match
				line: ID.line
				column: ID.column
			t.stringify = (indent) -> t.prefix.stringify(indent) + ".#{t.ID}"
			t.subtrees = () -> [t.prefix]
			stack.push t
			return true

		if matches(["ID", "COLON", "*", "*", "*", "*", "NEWLINE"])
			stack.pop()
			if matches(["ATMOST", "TYPE", "ATLEAST", "TYPE"])
				rhsLower = stack.pop()
				stack.pop()
				rhsUpper = stack.pop()
				stack.pop()
				stack.pop()
				lhs = stack.pop()
				stack.push TypeDecl(lhs, rhsLower, rhsUpper)
				return true
			else if matches(["ATLEAST", "TYPE", "ATMOST", "TYPE"])
				rhsUpper = stack.pop()
				stack.pop()
				rhsLower = stack.pop()
				stack.pop()
				stack.pop()
				lhs = stack.pop()
				stack.push TypeDecl(lhs, rhsLower, rhsUpper)
				return true

		if matches(["ID", "COLON", "*", "*", "NEWLINE"])
			stack.pop()
			if matches(["ATMOST", "TYPE"])
				rhsUpper = stack.pop()
				stack.pop()
				stack.pop()
				lhs = stack.pop()
				rhsLower = Token("ID", "Nothing", rhsUpper.line, rhsUpper.column)  # synthetic lower
				stack.push TypeDecl(lhs, rhsLower, rhsUpper)
				return true
			else if matches(["ATLEAST", "TYPE"])
				rhsLower = stack.pop()
				stack.pop()
				stack.pop()
				lhs = stack.pop()
				rhsUpper = Token("ID", "Any", rhsLower.line, rhsLower.column)  # synthetic upper
				stack.push TypeDecl(lhs, rhsLower, rhsUpper)
				return true

		if matches(["ID", "COLON", "*", "NEWLINE"])    # a type alias
			stack.pop()
			if matches(["TYPE"])
				rhs = stack.pop()
				stack.pop()
				lhs = stack.pop()
				stack.push TypeDecl(lhs, rhs, rhs)
				return true
			else
				expected("TYPE in declaration of #{fromTopOfStack(2).stringify(0)}")

		if matches(["id", "COLON", "*", "NEWLINE"])
			stack.pop()
			if matches(["TYPE"])
				rhs = stack.pop()
				stack.pop()
				lhs = stack.pop()
				stack.push TermDecl(lhs, rhs)
				return true
			else
				expected("TYPE in declaration of #{fromTopOfStack(2).stringify(0)}")

		if matches(["ID", "EQUALS", "*", "NEWLINE"])
			stack.pop()
			if matches(["TYPE"])
				rhs = stack.pop()
				stack.pop()
				lhs = stack.pop()
				t =
					type: "TYPE-ASSIGN"
					alttypes: ["STATEMENT"]
					lhs: lhs
					rhs: rhs
					line: lhs.line
					column: lhs.column
				t.stringify = (indent) -> t.lhs.stringify(indent) + " = " + t.rhs.stringify(indent)
				t.subtrees = () -> [t.lhs, t.rhs]
				stack.push t
				return true
			else
				expected("TYPE in assignment to #{fromTopOfStack(2).stringify(0)}")

		if matches(["id", "EQUALS", "*", "NEWLINE"]) or matches(["TERM-SELECT", "EQUALS", "*", "NEWLINE"])
			stack.pop()
			if matches(["TERM"])
				rhs = stack.pop()
				stack.pop()
				lhs = stack.pop()
				t =
					type: "TERM-ASSIGN"
					alttypes: ["STATEMENT"]
					lhs: lhs
					rhs: rhs
					line: lhs.line
					column: lhs.column
				t.stringify = (indent) -> t.lhs.stringify(indent) + " = " + t.rhs.stringify(indent)
				t.subtrees = () -> [t.lhs, t.rhs]
				stack.push t
				return true
			else
				expected("TERM in assignment to #{fromTopOfStack(2).stringify(0)}")

		if matches(["TYPE", "AND", "TYPE"])
			rhs = stack.pop()
			stack.pop()
			lhs = stack.pop()
			t =
				type: "AND-TYPE"
				alttypes: ["TYPE"]
				lhs: lhs
				rhs: rhs
				line: lhs.line
				column: lhs.column
			t.stringify = (indent) -> t.lhs.stringify(indent) + " & " + t.rhs.stringify(indent)
			t.subtrees = () -> [t.lhs, t.rhs]
			stack.push t
			return true

		if matches(["TYPE", "OR", "TYPE"])
			rhs = stack.pop()
			stack.pop()
			lhs = stack.pop()
			t =
				type: "OR-TYPE"
				alttypes: ["TYPE"]
				lhs: lhs
				rhs: rhs
				line: lhs.line
				column: lhs.column
			t.stringify = (indent) -> t.lhs.stringify(indent) + " | " + t.rhs.stringify(indent)
			t.subtrees = () -> [t.lhs, t.rhs]
			stack.push t
			return true

		if matches(["STATEMENTS", "*", "NEWLINE"])
			stack.pop()
			if matches(["TERM"])
				stmt = stack.pop()
				stmts = stack.pop()
				stmts.statements.push stmt
				stmts.line = stmt.line
				stmts.column = stmt.column
				stack.push stmts
				return true
			else
				expected("STATEMENT")

		if matches(["STATEMENTS", "STATEMENT"])
			stmt = stack.pop()
			stmts = stack.pop()
			stmts.statements.push stmt
			stmts.line = stmt.line
			stmts.column = stmt.column
			stack.push stmts
			return true

		if matches(["LBRACE"])   # if we get '{', start a nested block of statements
			lparen = fromTopOfStack()
			begin(lparen.line, lparen.column)
			return true

		if matches(["LBRACE", "STATEMENTS", "RBRACE"])  # match braces around statement blocks
			stack.pop()
			stmts = stack.pop()
			stack.pop()
			stack.push stmts
			return true

		if matches(["*", "DOT", "NEW"])
			nw = stack.pop()
			stack.pop()
			if matches(["TYPE"])
				_typTree = stack.pop()
				construct =
					type: "CONSTRUCT"
					alttypes: ["TERM"]
					typTree: _typTree
					line: nw.line
					column: nw.column
				construct.stringify = (indent) -> "#{construct.typTree.stringify(indent)}.new"
				construct.subtrees = () -> [construct.typTree]
				stack.push construct
				return true
			else
				throw new Error("Expected type in object construction on line #{nw.line} character #{nw.column}, got #{fromTopOfStack(0).stringify(0)}")

		if matches(["STATEMENTS", "NEWLINE"])
			stack.pop()  # get rid of redundant newline
			return true

	begin = (ln, col) ->
		stmts =
			type: "STATEMENTS"
			alttypes: ["TYPE"]  # a block of statements is a type
			statements: []
			line: ln
			column: col
		stmts.stringify = (indent) ->
			"{\n" +
				(for stmt in stmts.statements
					tabs(indent + 1) + stmt.stringify(indent + 1) + "\n").join("") +
				tabs(indent) + "}"
		stmts.subtrees = () -> stmts.statements
		stmts.print = stmts.stringify
		stack.push stmts

	showTypes = (t) ->
		s = t.type
		if t.alttypes
			s = s + " & " + (for typ in t.alttypes
				typ).join(" & ")
		return s

	# Do a (mostly) bottom-up parser.
	begin(1, 1)
	loop
		while reduce()
			true
		if tokens[0].type == "EOF" or unreducedTokenCount() >= 8 then break  # done yet?
		shift()

	if stack.length != 1
		i = -1
		stack_contents = (for t in stack
			i += 1
			"Item #{i}: #{showTypes(t)}\n#{t.stringify(0)}").join("\n\n")
		throw "Parse error: Unreduced items on stack at End-of-Input. Stack contents:\n\n#{stack_contents}"

	return stack[0]

tokenize = (input) ->
	line = 1
	column = 1

	tokenList = [
		{ name: "GUARD_ARROW", regex: /^=>/ }

		{ name: "id", regex: /^([a-z][a-zA-z0-9_]*|\?\?\?)/ }
		{ name: "ID", regex: /^[A-Z][a-zA-z0-9_]*/ }

		{ name: "NEWLINE", regex: /^(\n|\r\n|\r)/ }
		{ name: "COMMENT", regex: /^\/\/.*/ }
		{ name: "START-BLOCK-COMMENT", regex: /^\/\*/ }
		{ name: "END-BLOCK-COMMENT", regex: /^\*\// }

		{ name: "DOT", regex: /^\./ }
		{ name: "AND", regex: /^&/ }
		{ name: "OR", regex: /^\|/ }
		{ name: "EQUALS", regex: /^=/ }
		{ name: "LPAREN", regex: /^\(/ }
		{ name: "RPAREN", regex: /^\)/ }
		{ name: "LBRACE", regex: /^{/ }
		{ name: "RBRACE", regex: /^}/ }
		{ name: "COLON", regex: /^:/ }
		{ name: "EOF", regex: /^$/ }
	]
	Whitespace = { name: "SPACE", regex: /^[\t \v\f]+/ }

	getNextToken = () ->
		# skip leading whitespace
		matches = Whitespace.regex.exec(input)
		if matches
			input = input.substring(matches[0].length)
			column += matches[0].length  # column is just number of characters here - to make this an actual column number, we'd have to decide how wide tab characters and other whitespaces actually are

		# find the first token type that matches the input
		for tok in tokenList
			matches = tok.regex.exec(input)
			if matches
				return Token(tok.name, matches[0], line, column)

		length = input.indexOf('\n')
		if length <= 0 then length = input.length
		throw "Tokenization error on line #{line} character #{column} : Unable to match a token starting at '#{input.substring(0,length)}'"

	consumeNextToken = () ->
		tok = getNextToken()
		input = input.substring(tok.match.length)
		column += tok.match.length
		if tok.type == "NEWLINE"
			column = 1
			line += 1
		tok

	# begin tokenize
	tokens = []
	loop
		t = consumeNextToken()
		if t.type == "RBRACE" or t.type == "EOF"  # add a synthetic newline before "}" or EOF for parsing convenience
			tk = Token("NEWLINE", "\n", t.line, t.column)
			tk.stringify = () -> "(synthetic \\n)"
			tk.print = () -> "synthetic NEWLINE on line #{t.line}, char #{t.column}"
			tokens.push tk
		tokens.push t
		if t.type == "EOF" then break

	tokens

tabs = (indent) -> "\t".repeat(indent)
