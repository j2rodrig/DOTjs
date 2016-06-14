window.compile = (input, stopAfter) ->
	try
		tokens = tokenize(input)

		if stopAfter == "tokens"
			return (for tok in tokens
				tok.print()).join('\n')

		ast = parse(tokens)

		if stopAfter == "trees"
			return ast.print(0)

		debugOutput = contextify(CreateGlobalContext(), ast)

		if stopAfter == "symbols"
			return debugOutput

		#if stopAfter == "types"
		#	printTyp(typTree(ast, 0))

		#summ = getSummary(ast, true)
		#if stopAfter == "types"
		#	return stringifyMembershipSet(summ.typeMembers("UPPER"), 0)
		#	# ast.print(0)

		gen(ast)

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

Given A & { x = y } . new  where A is  { y: Y;  y = a }  :

Generation for A:
	function A(obj_A) {
		var r = {};
		r.y = a;
		return r;
	}
Generation for A & { x = y } . new:
	(function() {
		var r = {};

		return r;
	})();

???

###


gen = (tree) ->
	if tree.type is "CONSTRUCT"
		gen(tree.typTree)

	else if tree.type is "STATEMENTS"
		s = []
		for st in lowerBoundStatements(typTree(tree))
			s.push gen(st.tree)
		s.join("\n")

	else if tree.type is "TERM-ASSIGN"
		lhsTyp = typTree(tree.lhs)
		rhsTyp = typTree(tree.rhs)
		demandSubType(rhsTyp, lhsTyp)
		gen(tree.lhs) + " = " + gen(tree.rhs)

	else if tree.type is "TYPE-ASSIGN"
		"/* #{tree.lhs} = #{printTyp(typTree(tree.rhs), 0)} */"

	else
		typ = typTree(tree)
		
		if tree.type is "id"
			return tree.match
		else if tree.type is "TERM-SELECT"
			return gen(tree.prefix) + "." + tree.id
		else
			throw "Internal compiler error: Request for unimplemented code generation for #{tree.type} tree on line #{tree.line} character #{tree.column}"


demandSubType = (a, b) ->
	if not isSubType(a, b)
		throw "Type Error : Expected #{printTyp(b, 1)}\n" +
		      " Got #{printTyp(a, 1)}\n" +
		      "on line #{b.tree.line} character #{b.tree.column}"

isSubType = (a, b) ->
	if a is Nothing or b is Any then return true
	if b is Nothing or a is Any then return false
	if a is b then return true

	#todo actual subtyping
	return true

# A named member declaration.
Name = (name, info, tree) ->
	typtyp: "NAME"
	name: name
	info: info
	tree: tree

# A type assignment, term assignment, or other executable statement.
# The "type" of a statement is Unit, which we don't care about because we never
#   use the result of a statement.
Statement = (tree) ->
	typtyp: "STATEMENT"
	tree: tree

# A type with lower and upper bounds.
TypeBounds = (lowerInfo, upperInfo, tree) ->
	typtyp: "BOUNDS"
	lowerInfo: lowerInfo
	upperInfo: upperInfo
	tree: tree
	members: () -> members(upperInfo())

# A type selection or term selection.
NameSelect = (name, prefixInfo, tree) ->
	typ =
		typtyp: "NAME-SELECT"
		name: name
		prefixInfo: prefixInfo
		tree: tree
	typ.info = () ->
		prefixMembers = members(typ.prefixInfo())
		if not prefixMembers[typ.name]
			throw "Error : Member named '#{typ.name}' was not found at line #{typ.tree.line} character #{typ.tree.column}"
		infoTree = prefixMembers[typ.name]
		typTree(infoTree)
	typ

# A named type or term with no prefix.
NameLookup = (name, tree) ->
	typ =
		typtyp: "NAME-LOOKUP"
		name: name
		tree: tree
	typ.info = () ->
		# try to find the name in the current object?
		# try to find the name in its original context
		symInfoTree = typ.tree.context.lookupSymbol(typ.name, typ.tree.line, typ.tree.column).rhs
		typTree(symInfoTree)
	typ

# An intersection type.
# Contains a list of named members, statements, and/or base types.
AndType = (components, tree) ->
	typ =
		typtyp: "AND-TYPE"
		components: components
		tree: tree
	typ.members = () ->
		if typ._members then return typ._members
		_members = {}
		#todo linearization of supertypes
		for c in typ.components
			if c.typtyp is "NAME"
				#todo bounds intersection/validity, field type compatibility
				_members[c.name] = c.info
		#todo field type inference (from assignments)
		typ._members = _members
		typ._members
	typ

# A union type.
# Contains a list of named members, statements, and/or base types.
OrType = (components, tree) ->
	typ =
		typtyp: "OR-TYPE"
		components: components
		tree: tree
	typ.members = () ->
		throw "Unimplemented: request for membership of OR-TYPE"
	typ

printTyp = (typ, indent = 0) ->
	if typ.typtyp is "AND-TYPE"
		"{\n" + (for st in typ.components
			tabs(indent + 1) + printTyp(st, indent + 1) + "\n"
			).join("") + tabs(indent) + "}"
	else if typ.typtyp is "NAME"
		typ.name + ": " + printTyp(typ.info(), indent)
	else if typ.typtyp is "STATEMENT"
		"(stmt) " + typ.tree.stringify(indent)
	else if typ.typtyp is "NAME-SELECT"
		printTyp(typ.prefixInfo(), indent) + "." + typ.name
	else if typ.typtyp is "NAME-LOOKUP"
		typ.name
	else if typ.typtyp is "BOUNDS"
		"at least " + printTyp(typ.lowerInfo(), indent) + " at most " + printTyp(typ.upperInfo(), indent)
	else
		"(unimplemented printTyp for '#{typ.typtyp}' type')"

members = (typ) ->
	if typ.members then return typ.members()   # members function exists?
	if typ._members then return typ._members   # members already computed?
	typ._members =
		if typ.typtyp.info
			members(typ.info())
		else
			throw "Internal compiler error : Request for membership of type '#{typ}' is unimplemented. Line #{typ.tree.line} character #{typ.tree.column}"
	typ._members

lowerBoundStatements = (typIn) ->
	linearized = []           # statements in linearization order
	alreadyLinearized = []    # types that have already been linearized (to avoid repeating statements)

	_lowerBoundStatements = (typ) ->
		if typ in alreadyLinearized then return
		alreadyLinearized.push typ

		if typ.typtyp is "AND-TYPE"
			for c in typ.components
				if c.typtyp is "NAME"
					true   # do nothing for declarations (we get declarations from the members function)
				else if c.typtyp is "STATEMENT"
					linearized.push c   # do all statements in order
				else
					# linearize statments in other types
					_lowerBoundStatements(c)
		else
			throw "Internal Compiler Error: Requested lower-bound linearization of #{typ.typtyp} type is not implemented. Line #{typ.tree.line} character #{typ.tree.column}"

	_lowerBoundStatements(typIn)
	linearized

typTree = (tree) ->
	if tree.typ then return tree.typ

	typ = undefined

	if tree.type is "STATEMENTS"
		components = []
		for st in tree.statements
			do (st) ->
				if st.type is "TYPE-DECL"
					lowerInfo = () -> typTree(st.rhsLower)
					upperInfo = () -> typTree(st.rhsUpper)
					components.push Name(st.lhs.match, (() -> TypeBounds(lowerInfo, upperInfo)), st)
				else if st.type is "TERM-DECL"
					components.push Name(st.lhs.match, (() -> typTree(st.rhs)), st)
				else
					components.push Statement(st)
		typ = AndType(components, tree)

	else if tree.type is "TYPE-SELECT"
		typ = NameSelect(tree.ID, (() -> typTree(tree.prefix)), tree)

	else if tree.type is "TERM-SELECT"
		typ = NameSelect(tree.id, (() -> typTree(tree.prefix)), tree)

	else if tree.type in ["ID", "id"]
		typ = NameLookup(tree.match, tree)

	else if tree.type is "AND-TYPE"
		typ = AndType([typTree(tree.lhs), typTree(tree.rhs)], tree.rhs)

	else if tree.type is "OR-TYPE"
		typ = OrType([typTree(tree.lhs), typTree(tree.rhs)], tree.rhs)

	else if tree.type is "CONSTRUCT"
		typ = typTree(tree.typTree)

	else
		throw "Internal compiler error : Request for type of #{tree.type} tree is not implemented"

	tree.typ = typ
	typ








strtyp = (tree, indent) ->
	output = []

	if tree.lowerBoundMembership
		mInfo = []
		for m in tree.lowerBoundMembership
			if m.type == "TERM-DECL"
				mInfo.push "#{m.lhs.match}#{strtyp(m.rhs,indent+1)}"

		output.push (if mInfo.length < 2 then "{ " + mInfo.join("") + " }" else "{\n" + mInfo.join("\n") + "\n}")

	outp = output.join(" ")
	if outp then " : #{outp} " else ""


###
What is a type anyway?
It is (according to Odersky) just what you type (literally).
Viewpoint adaptation needs to occur, due to path-dependent typing. ->
	This means subtitutions need to occur, and types need to be clonable. (this is why types are not mere trees)
(Membership is a separate issue.)
(Type inference is a separate issue.)
###

###
We only type-check terms?
###

###
DOT types.

See: Rompf and Amin. "From F to DOT: Type Soundness Proofs with Definitional Interpreters." Tech Report 2015.
###

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

# A named type member with lower and upper bounds.
# The type indicated by a TYPE-ASSIGN (if a type-assign is present),
#  otherwise the lower bound of a TYPE-DECL.
#TypeMember = () -> {}

# A named field. A FieldMember is the type indicated by a TERM-DECL.
# Called a "value member" in the DOT paper.
# However, the term "value member" does not convey the impression that the member can be
# reassigned at runtime. So we call it a "field member" to indicate assignability.
#FieldMember = () -> {}

# A type x.L where x is a term. TypeSelect is the type indicated by a TYPE-SELECT.
# Note that we can only determine that x.L equals y.L if x is the same reference as y.
#TypeSelect = (prefixTyp, ID) -> {}

#TermSelect = (prefixTyp, id) -> {}

# All types are potentially self-recursive, so we do not have a separate recursive self type as in DOT.
# Whenever a type is accessed by name, a substitution occurs: A version of the named type is
#  returned where its self reference is substituted by the locally-valid path used to reach that type.

# Instead of including some direct notion of a self-recursive type, we have the notion of a ThisType.
# A ThisType represents the self-reference of some enclosing scope. Wherever a type is used in an
#  expression, that type's ThisTypes are substituted by a (path) type that is valid in the current
#  context.

# ThisTypes no longer make sense to me... I can't think of a reason why we would need an explicit "this." Access to outer environments is done through closures. And we're building to Javascript, which has closures.
# More importantly, if we can write a program that reaches a given type, then we already have the correct self-reference, and if we have the correct self-reference, then we also have a reference into the enclosing environment.
# ThisTypes seem to be a way of dealing with linearization into concrete classes. Since I'm not dealing with Java compatibility, this kind of concretization is unnecessary. In DOTjs, concretization only happens where "new" is performed, and not before. Every type is a trait.

#AndType = (tp1, tp2) -> { tp1: tp1, tp2: tp2 }

#OrType = (tp1, tp2) -> { tp1: tp1, tp2: tp2 }


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

CreateGlobalContext = () ->
	context =
		symbols: {}
		outerContext: undefined

	AddSymbolFromNamedType(context, "Any", Any)
	AddSymbolFromNamedType(context, "Nothing", Nothing)

	context.lookupSymbol = (name, line, column) -> lookupSymbolInContext(context, name, line, column)
	context

lookupSymbolInContext = (context, symName, line, column) ->
	# searches enclosing contexts for the named symbol, returning the symbol table entry if it exists
	if symName of context.symbols
		context.symbols[symName]
	else if context.outerContext
		context.outerContext.lookupSymbol(symName, line, column)
	else
		throw "Symbol '#{symName}' not found at line #{line} character #{column}"

stringifyMembershipSet = (mems, indent) ->
	out = []
	for id, summary of mems
		out.push(tabs(indent+1) + id + " : " + summary.tree.stringify(indent+1) + "\n")
	"{\n" + out.join("") + tabs(indent) + "}"



AddSymbolFromNamedType = (context, name, typ) ->
	sym =
		name: name
		typ: typ
	context.symbols[name] = sym

	#sym.summary = () -> sym.typ

	sym

AddSymbolFromTree = (context, name, defTree, line, column) ->
	sym =
		name: name
		rhs: defTree
		line: line
		column: column
	context.symbols[name] = sym

	#sym.summary = () -> getSummary(sym.rhs)

	sym

contextify = (outerContext, tree) ->
	output = []   # for debugging: list of symbols found

	tree.context = outerContext  # default context is the same as parent tree's context

	if tree.type == "STATEMENTS"
		tree.context =     # create a nested context for the statement block
			symbols: {}
			outerContext: outerContext
			lookupSymbol: (name, line, column) -> lookupSymbolInContext(tree.context, name, line, column)

		for t in tree.statements
			# Add term declarations and type assignments to the symbol table
			# (Note their remarkable similarity!)
			if t.type == "TERM-DECL" or t.type =="TYPE-ASSIGN"
				symName = t.lhs.match
				prevDef = tree.context.symbols[symName]
				if prevDef
					throw "Duplicate definition of #{symName}: line #{prevDef.line} and line #{t.line}"
				AddSymbolFromTree(tree.context, symName, t.rhs, t.line, t.column)

				output.push "(line #{t.line} character #{t.column}) #{symName} : #{t.rhs.stringify(0)}"

			#TODO: type inference for term assignments that don't have matching term declarations?
			#  perhaps associate each term symbol with a list of terms, then compute a synthethic union type upon request?
			# else if t.type == "TERM-ASSIGN"

	# contextify subtrees
	if tree.subtrees
		for subtree in tree.subtrees()
			output = output.concat contextify(tree.context, subtree)
	else if not tree.isToken
		throw "Internal compiler error: Function \"subtrees\" not found during traveral of #{tree.type} tree at line #{tree.line} character #{tree.column}. Value: #{tree.value}"

	return output.join("\n")


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

tabs = (indent) ->
	"    ".repeat(indent)
