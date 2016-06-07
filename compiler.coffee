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

		typecheck(ast)

		if stopAfter == "types"
			return ast.print(0)

	catch error
		return error.stack

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


# Typecheck all executable statements, as well as any trees those statements refer to.
# We don't need to generate types for trees that are unnecessary for typechecking
#   executable trees.
typecheck = (tree) ->

	if tree.type == "STATEMENTS"
		members = lowerBoundMembership(tree)
		for t in members
			typecheck(t)

	else if tree.type in ["id", "ID", "TYPE-SELECT", "TERM-SELECT"]
		upperBoundMembership(tree)
		lowerBoundMembership(tree)

	else if tree.type == "TERM-ASSIGN"
		rhsTyp = upperBoundMembership(tree.rhs)
		lhsTyp = lowerBoundMembership(tree.lhs)

# Finds an array of statements which are the given tree's type.
# For lowerBoundMembership, the array of statements returned is complete -
#  it includes both definitions and executable statements, and so can be constructed directly.
lowerBoundMembership = (tree) ->
	# is the result cached?
	if tree.lowerBoundMembership then return tree.lowerBoundMembership

	members = undefined

	# the membership of a statement block is exactly the statements in that block
	if tree.type == "STATEMENTS"
		# TODO: type inference:
		#  insert a term decl for every term assigned but not declared
		# TODO: checking:
		#   make sure term assignments and type assignments correspond to their declarations
		members = tree.statements

	else if tree.type == "ID" or tree.type == "id"
		members = tree.context.lookupSymbol(tree.match).getMembersForConstruction()

	else if tree.type == "TYPE-SELECT" or tree.type == "TERM-SELECT"
		prefixTree = tree.lhs
		name = tree.rhs.match

		# conservatively find membership of LHS type. (when would we want to use base-class membership instead?)
		prefixTypeMembers = upperBoundMembership(prefixTree)

		st = findMember(name, prefixTypeMembers)
		if st.type == "TERM-DECL" or st.type == "TYPE-ASSIGN"
			members = lowerBoundMembership(st.rhs)
		else
			# TODO: handle type decls
			throw "Internal compiler error : Unexpected #{st.type} in lowerBoundMembership"

	else
		throw "Unimplemented request for lower-bound membership of #{tree.type} tree"

	# cache the result
	tree.lowerBoundMembership = members
	members

# Finds an array of statements which are the given tree's type.
# For upperBoundMembership, the array of statements includes only those statements
#   in all possible objects represented by this types.
upperBoundMembership = (tree) ->
	if tree.upperBoundMembership then return tree.upperBoundMembership

	members = undefined

	# the membership of a statement block is exactly the statements in that block
	if tree.type == "STATEMENTS"
		# TODO: type inference:
		#  insert a term decl for every term assigned but not declared
		# TODO: checking:
		#   make sure term assignments and type assignments correspond to their declarations
		members = tree.statements

	else if tree.type == "ID" or tree.type == "id"
		members = tree.context.lookupSymbol(tree.match).getMembersConservatively()

	else if tree.type == "TYPE-SELECT" or tree.type == "TERM-SELECT"
		prefixTree = tree.lhs
		name = tree.rhs.match

		# conservatively find membership of LHS type. (when would we want to use base-class membership instead?)
		prefixTypeMembers = upperBoundMembership(prefixTree)

		st = findMember(name, prefixTypeMembers)
		if st.type == "TERM-DECL" or st.type == "TYPE-ASSIGN"
			members = upperBoundMembership(st.rhs)
		else
			# TODO: handle type decls
			throw "Internal compiler error : Unexpected #{st.type} in upperBoundMembership"

	else
		throw "Unimplemented request for upper-bound membership of #{tree.type} tree"

	# cache the result
	tree.upperBoundMembership = members
	members


findMember = (name, statements, lowerBound = false) ->
	lastMatch = undefined
	for s in statements
		if s.type == "TERM-DECL" or s.type == "TYPE-ASSIGN"
			if name == s.lhs.match
				lastMatch = s
	# TODO: handle type decls
	lastMatch

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
Any = {}

# The bottom type Nothing. Nothing is the most specific type.
# In fact, Nothing is so specific that we can't create an instance of it.
# Hence, the name "Nothing".
Nothing = {}

# A named type member with lower and upper bounds.
# The type indicated by a TYPE-ASSIGN (if a type-assign is present),
#  otherwise the lower bound of a TYPE-DECL.
TypeMember = () -> {}

# A named field. A FieldMember is the type indicated by a TERM-DECL.
# Called a "value member" in the DOT paper.
# However, the term "value member" does not convey the impression that the member can be
# reassigned at runtime. So we call it a "field member" to indicate assignability.
FieldMember = () -> {}

# A type x.L where x is a term. TypeSelect is the type indicated by a TYPE-SELECT.
# Note that we can only determine that x.L equals y.L if x is the same reference as y.
TypeSelect = (prefixTyp, ID) -> {}

TermSelect = (prefixTyp, id) -> {}

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

AndType = (tp1, tp2) -> { tp1: tp1, tp2: tp2 }

OrType = (tp1, tp2) -> { tp1: tp1, tp2: tp2 }


###
assignTypeTypeAssign = (tree) ->
	ID = tree.lhs.match
	rhsType = assignType(tree.rhs)
	rhsType

assignTypeTypeSelect = (tree) ->
	prefixType = assignType(tree.prefix)
	prefixType.findMember(tree.ID)   # how do I avoid infinite loops?


#assignType...
	#tree.context.lookupSymbol()

# A memoized function to assign types to trees.
assignType = (tree) ->
	if tree.typ then return tree.typ

	tree.typ =
		#if tree.type == "STATEMENTS" then assignTypeStatments(tree)
		#else if tree.type == "TERM-ASSIGN" then assignTypeTermAssign(tree)
		#else if tree.type == "TYPE-SELECT" then assignTypeTypeSelect(tree)

		if tree.type is "TYPE-ASSIGN" then assignTypeTypeAssign(tree)

		if tree.type is "TYPE-SELECT" then assignTypeTypeSelect(tree)

	tree.typ
###


membershipOfStatements = (tree) ->

	typeMembers = {}
	for st in tree.statements
		if st.type is "TYPE-DECL"
			existing = typeMembers[st.lhs.match]
			typeMembers[st.lhs.match] =
				upperBound: if existing then AndType(existng.upperBound, st.rhsUpper) else st.rhsUpper
				lowerBound: st.rhsLower

	return
		typeMembers: {}   # ID -> { lowerBound: tree, upperBound: tree }
		termMembers: {}   # id -> 

getMembershipOf = (tree) ->
	if tree.type is "STATEMENTS" then membershipOfStatements(tree)


DefaultToken = (tkIn, defaultType, defaultText, defaultLine, defaultColumn) ->
	if tkIn then tkIn else Token(defaultType, defaultText, defaultLine, defaultColumn)

Token = (tokType, text, line, column) ->
	return
		type: tokType
		match: text
		line: line
		column: column
		isToken: true

CreateGlobalContext = () ->
	context =
		symbols: {}
		outerContext: undefined

	AddSymbolFromNamedType(context, "Any", Any)
	AddSymbolFromNamedType(context, "Nothing", Nothing)

	context.lookupSymbol = (symName, line, column) ->
		# searches enclosing contexts for the named symbol, returning the symbol table entry if it exists
		if symName of context.symbols
			context.symbols[symName]
		else if context.outerContext
			context.outerContext.lookupSymbol(symName, line, column)
		else
			throw "Symbol '#{symName}' not found at line #{line} character #{column}"

	context

# I think what we need to do here is be able to take a type (sym info)
#  and find a list of type/term members. We only expand symbol types as needed.
# Each member may be defined at most once. If there are multiple definitions
#  of a particular member, the definitions must either be reconciled, or an
#  error must be produced.
# Symbols that are not found among present members are
#  expanded in their original contexts. (Essentially, expansion in the
#  original context allows mixins to access enclosing environments.)

findMembers = (tree) ->

	if tree.type is "STATEMENTS"

		typeDecls = {}
		for st in tree.statements
			if st.type is "TYPE-DECL"
				ID = st.lhs.match
				# TODO: if type member already exists, restrict its bounds
				typeDecls[ID] =
					lowerTree: st.rhsLower
					upperTree: st.rhsUpper

		termDecls = {}
		for st in tree.statements
			if st.type is "TERM-DECL"
				id = st.lhs.match
				# TODO: if term decl already exists, it must have the same type
				termDecls[id] =
					lowerTree: st.rhs
					upperTree: st.rhs

	if tree.type is "AND-TYPE"



assignType = (tree) ->
	if not tree.typ
		tree.typ
	else
		tree.typ =

			# type-decl, term-decl, term-select, type-select, statements

			if tree.type is "TYPE-DECL"
				lower: () -> assignType(rhsLower).lower()
				upper: () -> assignType(rhsUpper).upper()

			else if tree.type is "TERM-DECL"
				lower: () -> assignType(rhs).lower()
				upper: () -> assignType(rhs).upper()

			else if tree.type is "TERM-SELECT"
				prefixTyp = assignType(tree.prefix)
				# Do we need to do any substitutions here? A: No, ...
				memberSym = prefixTyp.lower().findMember(tree.id)

			else if tree.type is "TYPE-SELECT"
				prefixTyp = assignType(tree.prefix)
				# Do we need to do any substitutions here? A: No, ...
				memberSym = prefixTyp.lower().findMember(tree.ID)

			else if tree.type is "STATEMENTS"


			#TODO: named base-type approximations?

		tree.typ

AddSymbolFromNamedType = (context, name, typ) ->
	sym =
		name: name
		typ: typ
	context.symbols[name] = sym

	sym.info = () -> sym.typ

	sym

AddSymbolFromTree = (context, name, defTree, line, column) ->
	sym =
		name: name
		rhs: defTree
		line: line
		column: column
	context.symbols[name] = sym

	sym.info = () -> assignType(sym.defTree)

	sym

contextify = (outerContext, tree) ->
	output = []   # for debugging: list of symbols found

	tree.context = outerContext  # default context is the same as parent tree's context

	if tree.type == "STATEMENTS"
		tree.context =     # create a nested context for the statement block
			symbols: {}
			outerContext: outerContext
			lookupSymbol: outerContext.lookupSymbol

		for t in tree.statements
			# Add term declarations and type assignments to the symbol table
			# (Note their remarkable similarity!)
			if t.type == "TERM-DECL" or t.type =="TYPE-ASSIGN"
				symName = t.lhs.match
				prevDef = tree.context.symbols[symName]
				if prevDef
					throw "Duplicate definition of #{symName}: line #{prevDef.line} and line #{t.line}"
				AddSymbolFromTree(tree.context, symName, t.rhs, t.line, t.column)

				output.push "(line #{t.line} character #{t.column}) #{symName} : #{typTree.stringify(0)}"

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

		if matches(["ID", "COLON", "*", "ATLEAST", "*", "NEWLINE"])
			stack.pop()
			if matches(["TYPE", "ATLEAST", "TYPE"])
				rhsLower = stack.pop()
				stack.pop()
				rhsUpper = stack.pop()
				stack.pop()
				lhs = stack.pop()
				t =
					type: "TYPE-DECL"
					alttypes: ["STATEMENT"]
					lhs: lhs
					rhsUpper: rhsUpper
					rhsLower: rhsLower
					line: lhs.line
					column: lhs.column
				t.stringify = (indent) -> t.lhs.stringify(indent) + ": " + t.rhsUpper.stringify(indent) + strtyp(t,indent)
				t.subtrees = () -> [t.lhs, t.rhs]
				stack.push t
				return true
			else
				expected("TYPE in bounds declaration of #{fromTopOfStack(4).stringify(0)}")

		if matches(["ID", "COLON", "*", "NEWLINE"])
			stack.pop()
			if matches(["TYPE"])
				rhsUpper = stack.pop()
				stack.pop()
				lhs = stack.pop()
				t =
					type: "TYPE-DECL"
					alttypes: ["STATEMENT"]
					lhs: lhs
					rhsUpper: rhsUpper
					rhsLower: Token("ID", "Nothing", rhsUpper.line, rhsUpper.column)  # synthetic lower bound
					line: lhs.line
					column: lhs.column
				t.stringify = (indent) -> t.lhs.stringify(indent) + ": " + t.rhsUpper.stringify(indent) + strtyp(t,indent)
				t.subtrees = () -> [t.lhs, t.rhs]
				stack.push t
				return true
			else
				expected("TYPE in declaration of #{fromTopOfStack(2).stringify(0)}")

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
			typ = stack.pop()
			construct =
				type: "CONSTRUCT"
				alttypes: ["TERM"]
				typ: typ
				line: nw.line
				column: nw.column
			construct.stringify = (indent) -> "#{construct.typ.stringify(indent)}.new" + strtyp(construct,indent)
			construct.subtrees = () -> [construct.typ]
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
		throw "Parse error: Unreduced items on stack at End-of-Input. Stack contents: #{stack_contents}"

	return stack[0]

tokenize = (input) ->
	line = 1
	column = 1

	tokenList = [
		{ name: "NEW", regex: /^new/ }
		{ name: "IS_DEFINED", regex: /^is\s+defined/ }
		{ name: "SPECIALIZES", regex: /^specializes/ }
		{ name: "SPECIALIZED_BY", regex: /^specialized\s+by/ }
		{ name: "ATLEAST", regex: /^at\s+least/ }
		{ name: "GUARD_ARROW", regex: /^=>/ }

		{ name: "id", regex: /^[a-z][a-zA-z0-9_]*/ }
		{ name: "ID", regex: /^[A-Z][a-zA-z0-9_]*/ }

		{ name: "NEWLINE", regex: /^(\n|\r\n|\r)/ }
		{ name: "COMMENT", regex: /^\/\/.*/ }

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
				tk = Token(tok.name, matches[0], line, column)
				tk.stringify = () -> tk.match.replace('\n', '\\n')
				tk.print = () -> "#{tk.type}, \"#{tk.match.replace('\n', '\\n')}\", line #{tk.line}, char #{tk.column}"
				return tk

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
			tokens.push
				type: "NEWLINE"
				match: "\n"
				line: t.line
				column: t.column
				isToken: true
				stringify: () -> "(synthetic \\n)"
				print: () -> "synthetic NEWLINE on line #{t.line}, char #{t.column}"
		tokens.push t
		if t.type == "EOF" then break

	tokens

tabs = (indent) ->
	"    ".repeat(indent)
