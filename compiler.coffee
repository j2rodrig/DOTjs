window.compile = (input, stopAfter) ->
	try
		tokens = tokenize(input)

		if stopAfter == "tokens"
			return (for tok in tokens
				tok.print()).join('\n')

		ast = parse(tokens)

		if stopAfter == "trees"
			return ast.print(0)

		registerSymbols(ast, createGlobalContext())
		registerBaseTypes(ast)  # for convenience, we want to precompute lower and upper base type sequences.

		if stopAfter == "symbols"
			printSymbolTables(ast)

		# We want to be able to create an instance of this program,
		# so we treat the entire AST as a constructor definition.
		registerDeclarationsForConstruction(ast, ast.ctx)

		output = construct(ast)

		output

	catch error
		return if error.stack then error.stack else error

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

###


createGlobalContext = () ->
	ctx = freshContext()
	ctx.addSymbolFromType("Any", Any)
	ctx.addSymbolFromType("Nothing", Nothing)
	ctx

freshContext = (outer) ->
	ctx = {}

	if outer
		ctx.nestLevel = outer.nestLevel + 1
		ctx.outer = outer
	else
		ctx.nestLevel = 0
		ctx.outer = undefined

	ctx.indents = tabs(ctx.nestLevel)

	ctx.name = "c#{ctx.nestLevel}"

	ctx.members = {}

	ctx.fresh = () -> freshContext(outer)

	# The rule for membership is simpler than Scala:
	# Two symbols denote the same member if they are registered in the same context with the same name.

	ctx.addSymbolFromType = (name, typ, meta, line, column) ->
		if ctx.members[name]
			throw "Error : Duplicate definition of '#{name}' at line #{line} character #{column}"
		record =
			name: name
			ctx: ctx  # convenience: remember which context registered the symbol (we need this for codegen)
			typ: typ
			meta: meta
		ctx.members[name] = record

	ctx.addSymbolFromTree = (name, defTree, meta) ->
		if ctx.members[name]
			throw "Error : Duplicate definition of '#{name}' at line #{defTree.line} character #{defTree.column}"
		record = if ctx.members[name] then ctx.members[name] else
			name: name
			ctx: ctx  # convenience: remember which context registered the symbol (we need this for codegen)
			defTree: defTree
			meta: meta
		ctx.members[name] = record

	###
	ctx.findMember = (name, tree) ->
		if ctx.members[name] then return ctx.members[name]
		if ctx.isCtor
			findMemberInBaseTypes(name, tree)
		if ctx.outer then return outer.findMember(name)
		undefined

	ctx.requireMember = (name, line, column) ->
		record = ctx.findMember(name)
		if not record then throw "Member not found error : Could not find '#{name}' on line #{line} character #{column}"
		record
	###

	ctx


# The top type Any. Any is the most general type.
# In fact, Any is so general that every object in existence is an instance of it.
# Hence, the name "Any".
Any =
    typtyp: "AND-TYPE"
    components: []

# The bottom type Nothing. Nothing is the most specific type.
# In fact, Nothing is so specific that we can't create an instance of it.
# Hence, the name "Nothing".
Nothing =
    typtyp: "NOTHING"

TypeBounds = (lower, upper) ->
	typtyp: "TYPE-BOUNDS"
	lower: lower
	upper: upper

### CODEGEN ###

construct = (typTree, outerCtx) ->

	ctx = outerCtx.fresh()

	#todo linearize members, enter into symbol table
	# 1. find & narrow type declarations
	# 2. use type assignments to further narrow type declarations
	# 3. find term declarations
	# 4. use term assignments to infer types of undeclared terms

	linearizeStatements(typTree)
	findTypeDecls(typTree)

	# Generate constructor body
	constructorElements(typTree, ctx)

constructorElements = (typTree, ctx) ->
	linearBases = []

	doBases = (tree) ->
		if tree.type in ["ID", "TYPE-SELECT", "STATEMENTS"]
			linearBases.push tree
		else if tree.type in ["AND-TYPE", "OR-TYPE"]
			# Here, OR types are treated like AND types.
			# Basically, we do this in order to always get a constructible object.
			doBases(tree.lhs)
			doBases(tree.rhs)

	doBases(typTree)

	#


### MEMBERSHIP ###

# Finds the named symbol in the given context.
# Searches enclosing contexts if the name is not found in the given context.
findMemberInContext = (name, ctx) ->  #TODO: optional filtering of public/private names?
	if not ctx
		console.log("findMemberInContext '#{name}' : Not Found")
		return undefined

	if ctx.isConstructor
		console.log("findMemberInContext '#{name}' in constructor context '#{ctx.name}'")
		typTree = findMemberInTypeTree(name, ctx.tree)
		if typTree
			return typTree

	else if ctx.members[name]
		console.log("findMemberInContext '#{name}' in context '#{ctx.name}' : Found")
		return ctx.members[name].defTree  #todo: return defTree, member record, or something else? What's needed by the caller?

	findMemberInContext(name, ctx.outer)

# Finds the named member in the type defined by the given tree.
findMemberInTypeTree = (name, tree) ->

	if tree.type is "STATEMENTS"
		return tree.ctx.members[name]

	else if tree.type is "TYPE-SELECT"
		findMemberInTypeTree(name, widen(tree))

	else if tree.type is "ID"
		findMemberInTypeTree(name, widen(tree))

	else if tree.type is "AND-TYPE"
		lhs = findMemberInTypeTree(name, tree.lhs)
		rhs = findMemberInTypeTree(name, tree.rhs)

# Widens selections or identifiers to their declared types.
widen = (tree) ->
	if tree.type is "TYPE-SELECT" or tree.type is "TERM-SELECT"
		prefixTypTree = widen(tree.prefix)
		findMemberInTypeTree(tree.ID, prefixTypTree)

	else if tree.type is "ID" or tree.type is "id"
		findMemberInContext(tree.lhs.match, tree.ctx)



# ???
constrMembers = (tree, alreadySeen = []) ->

	# Membership is memoized.
	if tree.constrMembers then return tree.constrMembers

	if tree in alreadySeen
		throw "Recursive definition found while finding constructible members. Trees seen:\n" +
			(for t in alreadySeen
				"Line #{t.line}: " + t.stringify(0) + "\n\n") +
			tree.stringify(0)

	members =
		if tree.type is "STATEMENTS"
			members = {}
			for st in tree.statements
				if st.type is "TYPE-DECL" or st.type is "TERM-DECL"
					name = st.lhs.match
					if members[name] then throw "'#{name}' is declared more than once in the same statement block on line #{st.line} character #{st.column}"
					members[name] = st

		else if tree.type is "AND-TYPE" or tree.type is "OR-TYPE"

		else if tree.type is "TYPE-SELECT"
			prefixMem = constrMembers(tree.prefix)
			if not prefixMem[tree.ID]
				throw "Error : '#{ID}' is not a member of #{tree.prefix.stringify(0)}"
			record = prefixMem[tree.ID]
			if record.typTree
				constrMembers(record.typTree)
			else
				throw "Internal compiler error : Name "

		else if tree.type is "ID" or tree.type is "id"
			record = tree.ctx.requireMember(tree.match)
			if record.typTree
				constrMembers(record.typTree)

	tree.constrMembers = members
	members


### CONTEXTS AND SYMBOLS ###

registerSymbols = (tree, ctx) ->

	if tree.type is "CONSTRUCT"
		ctx = ctx.fresh()
		ctx.isConstructor = true

	else if tree.type is "STATEMENTS"
		ctx = ctx.fresh()

	else
		if tree.type is "TYPE-DECL" or tree.type is "TERM-DECL"
			ctx.addSymbolFromTree(tree.lhs.match, tree)

	if tree.subtrees
		for subtree in tree.subtrees
			registerSymbols(subtree, ctx)

	tree.ctx = ctx
	ctx.tree = tree



	#if tree.type is "CONSTRUCT"
	#	registerDeclarationsForConstruction(tree.typTree, tree.ctx)







registerLinearization = (tree, ctorCtx) ->

	if tree.type is "STATEMENTS"
		ctorCtx.addConcreteBase(tree)

	else if tree.type is "AND-TYPE"
		registerLinearization(tree.lhs, ctorCtx)
		registerLinearization(tree.rhs, ctorCtx)

	else if tree.type is "OR-TYPE"
		registerLinearization(tree.lhs, ctorCtx)
		registerLinearization(tree.rhs, ctorCtx)

	else if tree.type is "ID"
		record = tree.ctx.findMember(tree.match)   # should return a list of denotations, which are definition trees
		# todo look through returned denotation trees, and call registerLinearization again
		#ctorCtx.addConcreteBase(tree)

	else if tree.type is "TYPE-SELECT"
		ctorCtx.addConcreteBase(tree)


# Register base types.
# Makes a record of the base type trees needed to build each object in the appropriate constructor context.
# All base type trees are statement blocks, type IDs, or type selections.
registerBaseTypes = (tree, ctorCtx) ->

	if tree.type is "CONSTRUCT"
		registerBaseTypes(tree.typTree, tree.ctx)  # change the constructor context for subtrees

	else if ctorCtx
		if tree.type is "STATEMENTS"
			ctorCtx.addConcreteBase(tree)
			for st in tree.statements
				registerBaseTypes(st, null)  # look for more constructors

		else if tree.type is "AND-TYPE"
			registerBaseTypes(tree.lhs, ctorCtx)
			registerBaseTypes(tree.rhs, ctorCtx)

		else if tree.type is "OR-TYPE"
			registerBaseTypes(tree.lhs, ctorCtx)
			registerBaseTypes(tree.rhs, ctorCtx)

		else if tree.type is "ID"
			ctorCtx.addConcreteBase(tree)

		else if tree.type is "TYPE-SELECT"
			ctorCtx.addConcreteBase(tree)
			for st in tree.subtrees
				registerBaseTypes(st, null)  # look for more constructors

		else
			throw "Internal compiler error : Unexpected '#{tree.type}' tree in registerBaseTypes"

	else if tree.subtrees
		# look for constructors in subtrees
		for st in tree.subtrees
			registerBaseTypes(st, null)


registerDeclarationsForConstruction = (tree, intoCtx) ->
	# Membership in the self-type is determined lazily.
	# We're not going to register declarations directly.
	# Instead, we're going to set up a lazy evaluation of membership sets.
	# SO: what I'm going to do now is defer the construction of this method until lazy membership is defined.

	if tree.type is "ID"
		# TODO: find the ID in the self-type.



		# Linearize members of the type ID into the construction context
		record = tree.ctx.requireMember(tree.match, tree.line, tree.column)
		for mem in constrMembersOf(record)
			registerIfDeclaration(mem, intoCtx)

	else if tree.type is "AND-TYPE" or tree.type is "OR-TYPE"

	else if tree.type is "TYPE-SELECT"

	else if tree.type is "STATEMENTS"
		if tree.ctx is not intoCtx     # don't re-register symbols into the construction context if it is the same as the statment-block context
			for st in tree.statements
				registerIfDeclaration(st, intoCtx)

	else
		throw "Internal error : Unexpected '#{tree.type}' tree in registerDeclarationsForConstruction"

# Finds the declared membership of the lower bound of the given symbol record (that is, the union of membership sets).
constrMembersOf = (symRecord) ->
	mems = []
	for denot in symRecord.denotations
		if denot.defTree
			denot.defTree
			mems.push #TODO: what we've really got to do instead here is to do lazy evaluation of type membership...
		else
			throw "Internal error : Unexpected non-tree member definition in denotation set of symbol #{symRecord.name}"
	mems

registerIfDeclaration = (tree, ctx) ->
	if tree.type is "TYPE-DECL" or tree.type is "TERM-DECL"
		ctx.addSymbolFromTree(tree.lhs.match, tree)






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

		if matches(["id"])
			if fromTopOfStack(0).match is "outer"
				fromTopOfStack(0).type = "OUTER"
				fromTopOfStack(0).alttypes = undefined
				return true

		### Selections ###

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
			t.stringify = (indent) -> t.prefix.stringify(indent) + ".#{t.id}#{strtyp(t,indent)}"
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
			t.stringify = (indent) -> t.prefix.stringify(indent) + ".#{t.ID}#{strtyp(t,indent)}"
			t.subtrees = () -> [t.prefix]
			stack.push t
			return true

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
				" at least " + t.rhsLower.stringify(indent) + strtyp(t,indent)
			t.subtrees = () -> [t.lhs, t.rhsLower, t.rhsUpper]
			t

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
			else
				expected("TYPE in bounds declaration of #{fromTopOfStack(5).stringify(0)}")

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
			else
				expected("TYPE in declaration of #{fromTopOfStack(3).stringify(0)}")

		if matches(["id", "COLON", "*", "NEWLINE"])
			stack.pop()
			if matches(["TYPE"])
				rhs = stack.pop()
				stack.pop()
				lhs = stack.pop()
				t =
					type: "TERM-DECL"
					alttypes: ["STATEMENT"]
					lhs: lhs
					rhs: rhs
					line: lhs.line
					column: lhs.column
				t.stringify = (indent) -> t.lhs.stringify(indent) + ": " + t.rhs.stringify(indent) + strtyp(t,indent)
				t.subtrees = () -> [t.lhs, t.rhs]
				stack.push t
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

		if matches(["TYPE", "DOT", "NEW"])
			nw = stack.pop()
			stack.pop()
			_typTree = stack.pop()
			construct =
				type: "CONSTRUCT"
				alttypes: ["TERM"]
				typTree: _typTree
				line: nw.line
				column: nw.column
			construct.stringify = (indent) -> "#{construct.typTree.stringify(indent)}.new" + strtyp(construct,indent)
			construct.subtrees = () -> [construct.typTree]
			stack.push construct
			return true

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

		{ name: "id", regex: /^[a-z][a-zA-z0-9_]*/ }
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
