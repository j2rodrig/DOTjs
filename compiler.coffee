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

		outputBuffer = []
		[bases, ignore] = linearizedForConstruction(ast, predefCtx)
		genConstructor(bases, ast.ctx, predefCtx, 0, outputBuffer)
		outputBuffer.push(";")
		output = outputBuffer.join("")

		allOutput = [output]
		if channels[types] then allOutput.push("/** Types log:\n\n" + channels[types].join("\n") + "\n**/")
		if channels[stderr] then allOutput.push("/** Stderr log:\n\n" + channels[stderr].join("\n") + "\n**/")

		return allOutput.join("\n\n")

	catch error
		message = if error.message? then error.message else error
		message = if message.toUpperCase().startsWith("ERROR") or message.toUpperCase().startsWith("INTERNAL COMPILER ERROR") then message else "Error: " + message
		output = [message]
		if channels[types] then output.push("Types log:\n\n" + channels[types].join("\n"))
		if channels[stderr] then output.push("Stderr log:\n\n" + channels[stderr].join("\n"))
		if error.stack? then output.push("COMPILER STACKTRACE:\n" + error.stack)
		return output.join("\n\n")


channels = {}

stderr = "stderr"
types = "types"

clearLog = () ->
	channels = {}

log = (ch, msg) ->
	if not channels[ch]
		channels[ch] = [msg]
	else
		channels[ch].push msg

Any =
	type: "ANY"
	stringify: (indent) -> "Any"

Nothing =
	type: "NOTHING"
	stringify: (indent) -> "Nothing"

AndType = (lhsTyp, rhsTyp) ->
	type: "AND-TYPE"
	lhs: lhsTyp
	rhs: rhsTyp
	stringify: (indent) -> lhsTyp.stringify(indent) + " & " + rhsTyp.stringify(indent)

OrType = (lhsTyp, rhsTyp) ->
	type: "OR-TYPE"
	lhs: lhsTyp
	rhs: rhsTyp
	stringify: (indent) -> lhsTyp.stringify(indent) + " | " + rhsTyp.stringify(indent)


### TYPE OPERATIONS ###

shallowCopyTree = (t) ->
	type: t.type
	ctx: t.ctx
	line: t.line
	column: t.column
	annots: t.annots

derivedNameSelect = (t, prefix) ->
	if prefix is t.prefix then t else
		t1 = shallowCopyTree(t)
		t1.id = t.id   # we don't know whether we have an id or ID here, so just do both
		t1.ID = t.ID
		t1.prefix = prefix
		t1

derivedAndOrType = (tree, lhs, rhs) ->
	if lhs is tree.lhs and rhs is tree.rhs
		tree
	else if tree.type is "AND-TYPE"
		AndType(lhs, rhs)
	else if tree.type is "OR-TYPE"
		OrType(lhs, rhs)

derivedTypeDecl = (t, rhsUpper, rhsLower) ->
	if t.rhsUpper is rhsUpper and t.rhsLower is rhsLower then t else
		t1 = shallowCopyTree(t)
		t1.rhsUpper = rhsUpper
		t1.rhsLower = rhsLower
		t1

derivedTermDecl = (t, rhs) ->
	if t.rhs is rhs then t else  #TODO: stringify?
		t1 = shallowCopyTree(t)
		t1.rhs = rhs
		t1

derivedAssignment = (t, guard1, lhs1, rhs1) ->
	if t.guard is guard1 and t.lhs is lhs1 and t.rhs is rhs1 then t else
		t1 = shallowCopyTree(t)
		t1.guard = guard1
		t1.lhs = lhs1
		t1.rhs = rhs1
		t1

derivedConstruction = (t, typTree) ->
	if t.typTree is typTree then t else
		t1 = shallowCopyTree(t)
		t1.typTree = typTree
		t1

simplifyType = (tree) ->

	if tree.type is "TYPE-BOUNDS"   # TODO: we don't have an explicit "TYPE-BOUNDS" type anymore. When we decide to simplify types, redo this.
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

# insideStatement is true if looking at a statement, false if looking at a base type tree
deepCopyTree = (t, mutator, insideStatement) ->

	#
	# Do mutations of subtrees
	#
	t1 =
		if t.type is "TYPE-SELECT" or t.type is "TERM-SELECT"
			prefix1 = deepCopyTree(t.prefix, mutator, insideStatement)
			derivedNameSelect(t, prefix1)

		else if t.type is "STATEMENTS"
			stmt1 = shallowCopyTree(t)
			stmt1.statements = []
			anyDifferent = false
			for st in t.statements
				st1 = deepCopyTree(st, mutator, true)
				if st1 isnt st then anyDifferent = true
				stmt1.statements.push(st1)
			stmt1.stringify = (indent) -> stringifyStatements(stmt1, indent)
			if anyDifferent then stmt1 else t   # only return the copied tree if any subtrees are different

		else if t.type is "AND-TYPE" or t.type is "OR-TYPE"
			lhs1 = deepCopyTree(t.lhs, mutator, insideStatement)
			rhs1 = deepCopyTree(t.rhs, mutator, insideStatement)
			derivedAndOrType(t, lhs1, rhs1)

		else if t.type is "TYPE-DECL"
			rhsUpper = deepCopyTree(t.rhsUpper, mutator, false)
			rhsLower = deepCopyTree(t.rhsLower, mutator, false)
			derivedTypeDecl(t, rhsUpper, rhsLower)

		else if t.type is "TERM-DECL"
			rhs = deepCopyTree(t.rhs, mutator, false)
			derivedTermDecl(t, rhs)

		else if t.type is "TERM-ASSIGN"
			guard1 = if t.guard then deepCopyTree(t.guard, mutator) else undefined
			lhs1 = if t.lhs.type is "id"   # don't do mutation of assignment LHS if we're doing member initialization
				t.lhs
			else
				deepCopyTree(t.lhs, mutator, true)
			rhs1 = deepCopyTree(t.rhs, mutator, true)
			derivedAssignment(t, guard1, lhs1, rhs1)

		else if t.type is "CONSTRUCT"
			typTree1 = deepCopyTree(t.typTree, mutator, false)
			derivedConstruction(t, typTree1)

		else
			t

	mutator(t1, insideStatement)

replaceContextWithPrefix = (typ, ctx, prefix) ->
	deepCopyTree(typ, (t, insideStatement) ->
		#
		# For every id and ID that is defined in the given context, turn it into a select with the given prefix.
		# We need to transform prefix-less identifiers only, since only identifiers are implicitly understood
		# to be prefixed with a self-reference.
		#
		if t.type is "ID"
			startCtx = if insideStatement then t.ctx else t.ctx.outer   # if we're inside a statement, look up in the current context, otherwise enclosing context
			if getDefContext(t.match, startCtx) is ctx
				t1 = shallowCopyTree(t)
				t1.type = "TYPE-SELECT"
				t1.ID = t.match
				t1.prefix = prefix
				t1.stringify = (indent) -> "#{t1.ID}.#{t1.prefix.stringify(indent)}"
				return t1
		if t.type is "id"
			startCtx = if insideStatement then t.ctx else t.ctx.outer
			if getDefContext(t.match, startCtx) is ctx
				t1 = shallowCopyTree(t)
				t1.type = "TERM-SELECT"
				t1.id = t.match
				t1.prefix = prefix
				t1.stringify = (indent) -> "#{t1.id}.#{t1.prefix.stringify(indent)}"
				return t1
		t
	)


replaceContextWithContext = (typ, fromCtx, toCtx) ->
	deepCopyTree(typ, (t, insideStatement) ->
		#
		# For every id and ID that is defined in fromCtx, make a copy of it in toCtx.
		# We need to replace the contexts of prefix-less identifiers only, since only identifiers
		# are implicitly understood to be prefixed with a self-reference.
		#
		if t.type is "ID"
			startCtx = if insideStatement then t.ctx else t.ctx.outer   # if we're inside a statement, look up in the current context, otherwise enclosing context
			if getDefContext(t.match, startCtx) is fromCtx
				t1 = shallowCopyTree(t)
				t1.type = "ID"
				t1.ctx = toCtx
				t1.match = t.match
				t1.stringify = (indent) -> "#{t1.match}"
				return t1
		if t.type is "id"
			startCtx = if insideStatement then t.ctx else t.ctx.outer
			if getDefContext(t.match, startCtx) is fromCtx
				t1 = shallowCopyTree(t)
				t1.type = "id"
				t1.ctx = toCtx
				t1.match = t.match
				t1.stringify = (indent) -> "#{t1.match}"
				return t1
		t
	)


### CONTEXTS AND SYMBOL/MEMBER LOOKUP ###

createPredefContext = () ->
	predefTree =
		type: "STATEMENTS"
		statements: []
	predefTree.stringify = (indent) -> "{ (predefined symbols) }"
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
	ctx.outer = ctx  # circular reference to outermost context (for convenience)
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

	ctx.findMember = (name, returnLowerBound, logIndent) ->
		# Find the actual statement blocks that define the members of this context.
		asConstructed = typeAsConstructed(typTree, ctx.outer)
		# Unlike the above, the context for the call to findMember is undefined.
		# Since the asConstructed tree no longer includes names of base types, the context is never referenced, so we don't pass one.
		findMember(name, asConstructed, undefined, returnLowerBound, logIndent)

	ctx

findMember = (name, typTree, ctx, returnLowerBound, logIndent) ->  # params: name to find, type tree to look into, enclosing context to resolve type/term names in the type tree

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
		[widenedIdCtx, widenedIdTree] = widen(typTree, ctx)
		findMember(name, widenedIdTree, widenedIdCtx, returnLowerBound)

	else if typTree.type is "TYPE-SELECT"
		[widenedCtx, widenedTyp] = widen(typTree, ctx)
		findMember(name, widenedTyp, widenedCtx, returnLowerBound)

	else if typTree.type is "AND-TYPE"
		lhsType = findMember(name, typTree.lhs, ctx, returnLowerBound)
		rhsType = findMember(name, typTree.rhs, ctx, returnLowerBound)
		if (not lhsType) or (lhsType is rhsType)
			rhsType
		else if not rhsType
			lhsType
		else if returnLowerBound
			OrType(lhsType, rhsType)
		else
			AndType(lhsType, rhsType)

	else
		throw new Error("Internal compiler error: Unexpected #{typTree.type} tree in findMember")

# Widen a term or named type to its corresponding type tree.
# For named types or terms, returns the given context.
# For constructors, returns the context for that constructor itself.
widen = (tree, ctx, returnLowerBound, logIndent = 0) ->

	if tree.type is "id"
		log(types, tabs(logIndent) + "Widening #{tree.match} to its declared type" + (if returnLowerBound then " (getting lower bound)" else ""))
		typ = requireMemberInContext(tree.match, ctx, tree, returnLowerBound, logIndent+1)
		#
		# Replace the expanded type's original context with the current context.
		# Identifiers referring to the original context will now refer to the current context.
		#
		log(types, "Replacing context #{typ.ctx.name} with context #{ctx.name}")
		typ = replaceContextWithContext(typ, typ.ctx, ctx)
		log(types, "Result: " + typ.stringify(0))

		#ctx = requireDefContext(tree.match, ctx, tree)  #TODO: do we want this?
		[ctx, typ]

	else if tree.type is "ID"
		log(types, tabs(logIndent) + "Widening #{tree.match} to its declared type" + (if returnLowerBound then " (getting lower bound)" else ""))
		typ = requireMemberInContext(tree.match, ctx, tree, returnLowerBound, logIndent+1)
		#
		# Replace the expanded type's original context with the current context.
		# Replacing the context makes the returned type look as if it were declared right here; as if the named ID was replaced directly with the expansion.
		#
		log(types, "Replacing context #{typ.ctx.name} with context #{ctx.name}")
		typ = replaceContextWithContext(typ, typ.ctx, ctx)
		log(types, "Result: " + typ.stringify(0))

		#ctx = requireDefContext(tree.match, ctx, tree)  #TODO: do we want this?
		[ctx, typ]

	else if tree.type is "TERM-SELECT"
		log(types, tabs(logIndent) + "Widening term selection #{tree.stringify(logIndent+1)} to its declared type" + (if returnLowerBound then " (getting lower bound)" else ""))
		[prefixCtx, prefixTyp] = widen(tree.prefix, ctx, false, logIndent+1)
		typ = requireMemberInType(tree.id, prefixTyp, prefixCtx, tree, returnLowerBound)
		#
		# Replace the expanded type's original context with the current prefix.
		# Replacing the context makes the returned type look as if it were declared right here; as if the named ID was replaced directly with the expansion.
		#
		log(types, "Replacing context #{typ.ctx.name} with prefix #{tree.prefix.stringify(0)}")
		typ = replaceContextWithPrefix(typ, typ.ctx, tree.prefix)
		log(types, "Result: " + typ.stringify(0))

		[prefixCtx, typ]

	else if tree.type is "TYPE-SELECT"
		log(types, tabs(logIndent) + "Widening type selection #{tree.stringify(logIndent+1)} to its declared type" + (if returnLowerBound then " (getting lower bound)" else ""))
		[prefixCtx, prefixTyp] = widen(tree.prefix, ctx, false, logIndent+1)
		typ = requireMemberInType(tree.ID, prefixTyp, prefixCtx, tree, returnLowerBound)
		#
		# Replace the expanded type's original context with the current prefix.
		# Replacing the context makes the returned type look as if it were declared right here; as if the named ID was replaced directly with the expansion.
		#
		log(types, "Replacing context #{typ.ctx.name} with prefix #{tree.prefix.stringify(0)}")
		typ = replaceContextWithPrefix(typ, typ.ctx, tree.prefix)
		log(types, "Result: " + typ.stringify(0))

		[prefixCtx, typ]

	else if tree.type is "CONSTRUCT"
		log(types, tabs(logIndent) + "Widening object #{tree.stringify(logIndent+1)} to its type-as-constructed")
		asConstructed = typeAsConstructed(tree.typTree, ctx)
		[tree.typTree.ctx, asConstructed]  # context is context of self-type

	else
		throw new Error("Unexpected #{tree.type} tree in widen")


findMemberInContext = (name, ctx, returnLowerBound, logIndent) ->
	found = ctx.findMember(name, returnLowerBound, logIndent)
	if found
		found
	else if ctx isnt ctx.outer
		findMemberInContext(name, ctx.outer, returnLowerBound, logIndent)
	else
		undefined

# Finds the context that defines the given name, if it is in ctx or enclosing.
getDefContext = (name, ctx) ->
	if ctx.findMember(name)
		ctx
	else if ctx isnt ctx.outer
		getDefContext(name, ctx.outer)
	else
		undefined

# Throws an error if the given name is not defined in the given or enclosing contexts.
requireMemberInContext = (name, ctx, sourceTree, returnLowerBound, logIndent) ->
	typTree = findMemberInContext(name, ctx, returnLowerBound, logIndent)
	if not typTree
		throw new Error("Name '#{name}' is not defined at line #{sourceTree.line} character #{sourceTree.column}")
	typTree

requireMemberInType = (name, typTree, ctx, sourceTree, returnLowerBound, logIndent) ->
	found = findMember(name, typTree, ctx, returnLowerBound, logIndent)
	if not found
		throw new Error("Member '#{name}' at line #{sourceTree.line} character #{sourceTree.column} could not be found")
	found

requireDefContext = (name, ctx, sourceTree) ->
	found = getDefContext(name, ctx)
	if not found
		throw new Error("Name '#{name}' is not defined at line #{sourceTree.line} character #{sourceTree.column}")
	found


### BASE/CONSTRUCTOR TYPE QUERIES ###

typeAsConstructed = (tree, ctx) ->
	[bases, problemBase, stmts] = linearizedForConstruction(tree, ctx)
	if bases is false
		throw new Error("Cannot construct object at line #{tree.line} character #{tree.column} because base type #{problemBase.stringify(0)} is non-constructible.")
	typ = Any
	for stmt in stmts
		if typ is Any
			typ = stmt
		else
			typ = AndType(typ, stmt)
	typ

typeAsLinearized = (tree, ctx) ->
	[bases, problemBase, stmts] = linearizedForConstruction(tree, ctx)
	if bases is false
		throw new Error("Cannot construct object at line #{tree.line} character #{tree.column} because base type #{problemBase.stringify(0)} is non-constructible.")
	typ = Any
	for base in bases
		if typ is Any
			typ = base
		else
			typ = AndType(typ, base)
	typ

# Finds the sequence of base types needed to construct an object of the given type tree.
# Returns a triple [lin, base, statements].
#   If the type is constructible, lin is an array of base types. If not, lin is false and base is the base type that cannot be constructed.
#   statements is the list of statement blocks that contain member definitions.
linearizedForConstruction = (tree, ctx) ->

	if tree._linearization
		return [tree._linearization, undefined, tree._statements]
	else
		tree._linearization = []
		tree._statements = []

	if tree.type in ["ID", "TYPE-SELECT"]
		tree._linearization.push tree

		# Make sure we can linearize higher base classes
		[wCtx, wTyp] = widen(tree, ctx, true)
		[lin, ignore, stmt] = linearizedForConstruction(wTyp, wCtx)
		if lin is false
			tree._linearization = false
			return [false, tree, undefined]
		tree._statements = tree._statements.concat stmt

	else if tree.type is "AND-TYPE"
		[linLhs, baseLhs, stmtLhs] = linearizedForConstruction(tree.lhs, ctx)
		if linLhs is false
			tree._linearization = false
			return [false, baseLhs, undefined]

		[linRhs, baseRhs, stmtRhs] = linearizedForConstruction(tree.rhs, ctx)
		if linRhs is false
			tree._linearization = false
			return [false, baseRhs, undefined]

		tree._linearization = tree._linearization.concat linLhs
		tree._statements = tree._statements.concat stmtLhs
		tree._linearization = tree._linearization.concat linRhs
		tree._statements = tree._statements.concat stmtRhs

	else if tree.type is "OR-TYPE"
		# Here, we've got to choose which branch of the OrType gets instantiated.
		# The default policy I go with here is to select the leftmost branch unless it is non-constructible.
		# By choosing the leftmost branch, members of types earlier in the linearization order override members later in the order.
		# The result of this policy is that declarations are narrowed from right to left, but assignments are executed from
		#  left to right. This allows the most specific declarations and the earliest-executed terms to be grouped together
		#  in the leftmost base type.
		log(types, "Considering OrType #{tree.stringify(0)}")
		[linLhs, baseLhs, stmtLhs] = linearizedForConstruction(tree.lhs, ctx)
		if linLhs is false
			[linRhs, baseRhs, stmtRhs] = linearizedForConstruction(tree.rhs, ctx)
			if linRhs is false
				tree._linearization = false
				return [false, baseRhs, undefined]
			tree._linearization = tree._linearization.concat linRhs
			tree._statements = tree._statements.concat stmtRhs
		else
			tree._linearization = tree._linearization.concat linLhs
			tree._statements = tree._statements.concat stmtLhs

	else if tree.type is "NOTHING"
		tree._linearization = false
		return [false, tree, undefined]

	else if tree.type is "STATEMENTS"
		tree._linearization.push tree
		tree._statements.push tree

	else if tree.type is "ANY"
		# No action needed

	else
		throw new Error("Internal compiler error: Expected a type tree in linearizedForConstruction, got #{tree.type} tree")

	#TODO: remove duplicates?
	[tree._linearization, undefined, tree._statements]


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
			requireMemberInType(tree.id, tree.prefix.info(), ctx, tree)
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


### TYPE COMPARISONS ###

isSubType = (t0, ctx0, t1, ctx1) ->

	log(types, "#{t0.stringify(0)} <:? #{t1.stringify(0)}")

	if t0 is t1
		true
	else if t0 is Nothing
		true
	else if t1 is Any
		true
	else if t0 is Any
		false
	else if t1 is Nothing
		false

	else if t1.type is "TYPE-SELECT"
		# x.L <: x.L ; same prefix, same type member name
		if t0.type is "TYPE-SELECT" and t0.ID is t1.ID and isSameReference(t0.prefix, ctx0, t1.prefix, ctx1)
			true
		else
			# T <: x.L ; widen x.L to its lower bound ; substitute x for self-references in result type
			[wctx1, wtyp1] = widen(t1.prefix, ctx1, true)
			substThis()
			isSubType(t0, ctx0, wtyp1, wctx1)

	else if t1.type is "ID"
		# x.L <: x.L ; same prefix, same type member name ; the "prefix" x here is the self-reference of the context defining the ID
		if t0.type is "ID" and t0.match is t1.match and isDefinedInSameContext(t0, ctx0, t1, ctx1)
			true
		else
			# T <: x.L ; widen x.L to its lower bound ; x is the context reference ctx1, so substitution of "this" is done by merely returning the right context
			[wctx1, wtyp1] = widen(t1, ctx1, true)
			isSubType(t0, ctx0, wtyp1, wctx1)

	else if t1.type is "AND-TYPE"
		isSubType(t0, ctx0, t1.lhs, ctx1) and isSubType(t0, ctx0, t1.rhs, ctx1)

	else if t1.type is "OR-TYPE"
		isSubType(t0, ctx0, t1.lhs, ctx1) or isSubType(t0, ctx0, t1.rhs, ctx1)

	else if t0.type is "ID"
		# x.L <: T ; widen x.L to its upper bound
		[wctx0, wtyp0] = widen(t0, ctx0, false)
		isSubType(wtyp0, wctx0, t1, ctx1)

	else if t0.type is "TYPE-SELECT"
		# x.L <: T ; widen x.L to its upper bound ; substitute x for self-references in result type
		[wctx0, wtyp0] = widen(t0, ctx0, false)
		isSubType(wtyp0, wctx0, t1, ctx1)

	else if t0.type is "AND-TYPE"
		isSubType(t0.lhs, ctx0, t1, ctx1) or isSubType(t0.rhs, ctx0, t1, ctx1)

	else if t0.type is "OR-TYPE"
		isSubType(t0.lhs, ctx0, t1, ctx1) and isSubType(t0.rhs, ctx0, t1, ctx1)

	else if not (t0.type is "STATEMENTS" and t1.type is "STATEMENTS")
		throw new Error("Internal compiler error: Expected types in isSubType, but attempted to compare a #{t0.type} tree with a #{t1.type} tree")

	else
		# Make sure all declarations in the t1 statement block subsume declarations in t0
		for st1 in t1.statements

			if st1.type is "TYPE-DECL"
				member0upper = findMember(st1.lhs, t0, ctx0, false)
				if not member0upper
					log(types, "Failure to find member #{st.lhs} in type #{t0}")
					return false
				if not isSubType(member0upper, ctx0, st1.rhsUpper, ctx1)
					log(types, "#{member0upper}, the upper bound of #{st1.lhs} in #{t0}, is not compatible with #{st1.rhsUpper}")
					return false

				member0lower = findMember(st1.lhs, t0, ctx0, true)
				if not isSubType(st1.rhsLower, ctx1, member0lower, ctx0)
					log(types, "#{st1.rhsLower} is not compatible with #{member0lower}, the lower bound of #{st1.lhs} in #{t0}")
					return false
			
			else if st1.type is "TERM-DECL"
				member0 = findMember(st1.lhs, t0, ctx0, false)
				if not member0
					log(types, "Failure to find member #{st1.lhs} in type #{t0}")
					return false
				if not isSubType(member0, ctx0, st1.rhs, ctx1)  # TODO: strengthen this condition when variance is added
					log(types, "Type #{member0} declared for field #{st1.lhs} is not compatible with type #{st1.rhs}")
					return false
				if not isSubType(st1.rhs, ctx1, member0, ctx0)  # TODO: strengthen this condition when variance is added
					log(types, "Type #{st1.rhs} declared for field #{st1.lhs} is not compatible with type #{member0}")
					return false

		# All declarations are compatible. Subtype check succeeds.
		true


isSameReference = (tree0, ctx0, tree1, ctx1) ->
	if tree0.type is "id"
		tree1.type is "id" and tree0.match is tree1.match and isDefinedInSameContext(tree0, ctx0, tree1, ctx1)
	else if tree0.type is "TERM-SELECT"
		tree1.type is "TERM-SELECT" and tree0.id is tree1.id and isSameReference(tree0.prefix, ctx0, tree1.prefix, ctx1)
	else
		false

isDefinedInSameContext = (tree0, ctx0, tree1, ctx1) ->
	# assume tree0 and tree1 are both "id" or "ID" tokens
	requireDefContext(tree0.match, ctx0, tree0) is requireDefContext(tree1.match, ctx1, tree1)

requireCompatibility = (t0, ctx0, t1, ctx1, whereTree) ->
	if isSubType(t0, ctx0, t1, ctx1)
		true
	else
		throw new Error("Type error: expected: #{t1.stringify(0)}\n\tGot: #{t0.stringify(0)}\n\tOn line #{whereTree.line} character #{whereTree.column}")

requireTermCompatibility = (tree0, tree1, ctx) ->
	if not (tree0.type in ["id", "TERM-SELECT", "CONSTRUCT"])
		throw new Error("Internal compiler error: Expected term in requireTermCompatibility, got #{tree0.type}")
	if not (tree1.type in ["id", "TERM-SELECT", "CONSTRUCT"])
		throw new Error("Internal compiler error: Expected term in requireTermCompatibility, got #{tree1.type}")
	[ctx0, t0] = widen(tree0, ctx, false)
	[ctx1, t1] = widen(tree1, ctx, false)
	requireCompatibility(t0, ctx0, t1, ctx1, tree1)
	log(types, "Successfully compared type #{t0.stringify(0)} to #{t1.stringify(0)} on line #{tree1.line}")

### CODEGEN ###

gen = (tree, ctx, indent, output) ->

	# On statement ordering

	if tree.type is "STATEMENTS"
		for st in tree.statements
			if st.type is "TYPE-DECL"
				[bases, baseWithProblem] = linearizedForConstruction(st.rhsLower, ctx)
				if bases  # skip generating an initializer if the type is non-constructible
					output.push(tabs(indent))
					defCtx = requireDefContext(st.lhs.match, ctx, tree)
					output.push("if(!#{defCtx.name}.#{st.lhs.match}){")  # define an initializer only if a same-named initializer has not been defined yet
					output.push("#{defCtx.name}.#{st.lhs.match}")
					output.push(" = ")
					genInitializer(bases, st.rhsLower.ctx, ctx, indent, output)
					output.push(";}\n")

		for st in tree.statements
			if st.type is "TERM-ASSIGN"
				requireTermCompatibility(st.rhs, st.lhs, ctx)  # Check for rhs <: lhs compatibility
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
		[bases, baseWithProblem] = linearizedForConstruction(tree.typTree, ctx)
		if bases is false
			throw new Error("Cannot construct the object at line #{tree.line} character #{tree.column} because base type '#{baseWithProblem.stringify(0)}' is non-constructible.")
		genConstructor(bases, tree.typTree.ctx, ctx, indent, output)

	else if tree.type is "id"
		if tree.match is "???"
			output.push("(function(){ throw new Error('Not Implemented'); })()")
		else
			defCtx = requireDefContext(tree.match, ctx, tree)
			output.push("#{defCtx.name}.#{tree.match}")

	else if tree.type is "TERM-SELECT"
		[prefixCtx, prefixType] = widen(tree.prefix, ctx)
		requireMemberInType(tree.id, prefixType, prefixCtx, tree)  # Typecheck: make sure id exists in prefix type
		gen(tree.prefix, ctx, indent, output)
		output.push(".")
		output.push(tree.id)

genInitializer = (bases, ctx, outer, indent, output) ->
	# TODO: hoist type assignments?
	output.push("function(#{ctx.name}){\n")
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
		else
			throw new Error("Internal compiler error: Unexpected base type tree #{base.type} in genConstructor. Line #{tree.line} character #{tree.column}")

	output.push(tabs(indent + 1))
	output.push("return #{ctx.name};\n")
	output.push(tabs(indent))
	output.push("}")

genConstructor = (bases, ctx, outer, indent, output) ->
	output.push("(function(#{ctx.name}){\n")
	for base in bases
		if base.type is "STATEMENTS"
			gen(base, ctx, indent + 1, output)
		else if base.type is "ID"
			if base.match isnt "Any"  # hack: don't generate constructor calls to the predefined type Any
				defCtx = requireDefContext(base.match, outer, base)
				output.push(tabs(indent + 1))
				output.push("#{defCtx.name}.#{base.match}(#{ctx.name});\n")
		else if base.type is "TYPE-SELECT"
			output.push(tabs(indent + 1))
			gen(base.prefix, outer, indent + 1, output)
			output.push(".#{base.ID}(#{ctx.name});\n")
		else if base.type is "ANY"
			# don't need to do anything with Any
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
	if t.lhs.isVal
		WithAnnotation(t, "@final")
	t.stringify = (indent) -> t.lhs.stringify(indent) + ": " + t.rhs.stringify(indent)
	t.subtrees = () -> [t.lhs, t.rhs]
	t

WithAnnotation = (t, annot) ->
	if t.annots
		t.annots.push annot
	else
		t.annots = [annot]

HasAnnotation = (t, annot) -> t.annots && (annot in t.annots)

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
			if fromTopOfStack(0).match is "var"
				fromTopOfStack(0).type = "VAR"
				fromTopOfStack(0).alttypes = undefined
				return true
			if fromTopOfStack(0).match is "val"
				fromTopOfStack(0).type = "VAL"
				fromTopOfStack(0).alttypes = undefined
				return true
			if fromTopOfStack(0).match is "type"
				fromTopOfStack(0).type = "TYPE-KEYWORD"
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

		if matches(["VAR", "id", "COLON"])  # set 'var' flag on id
			c = stack.pop()
			id = stack.pop()
			stack.pop()
			id.isVar = true
			stack.push(id)
			stack.push(c)
			return true

		if matches(["VAL", "id", "COLON"])  # set 'val' flag on id
			c = stack.pop()
			id = stack.pop()
			stack.pop()
			id.isVal = true
			stack.push(id)
			stack.push(c)
			return true

		if matches(["TYPE-KEYWORD", "ID", "COLON"])  # consume 'type' in front of type declaration
			c = stack.pop()
			ID = stack.pop()
			stack.pop()
			stack.push(ID)
			stack.push(c)
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

		# adds an annotation to a type. We do this after &-type and |-type so that the annotation applies to the entire type expression.
		if matches(["AT", "id", "TYPE"])
			t = stack.pop()
			id = stack.pop()
			stack.pop()
			WithAnnotation(t, id)
			prevStringify = t.stringify
			prevSubtrees = t.subtrees
			t.stringify = (indent) -> "@" + t.id.match + " " + prevStringify(indent)
			t.subtrees = () -> prevSubtrees().concat([t.typ])
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
		stmts.stringify = (indent) -> stringifyStatements(stmts, indent)
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
		{ name: "id", regex: /^([a-z][a-zA-z0-9_]*|\?\?\?)/ }
		{ name: "ID", regex: /^[A-Z][a-zA-z0-9_]*/ }

		{ name: "NEWLINE", regex: /^(\n|\r\n|\r)/ }
		{ name: "COMMENT", regex: /^\/\/.*/ }
		{ name: "START-BLOCK-COMMENT", regex: /^\/\*/ }
		{ name: "END-BLOCK-COMMENT", regex: /^\*\// }

		{ name: "DOT", regex: /^\./ }
		{ name: "AND", regex: /^&/ }
		{ name: "OR", regex: /^\|/ }
		{ name: "AT", regex: /^@/ }
		{ name: "EQUALS", regex: /^=/ }
		{ name: "LPAREN", regex: /^\(/ }
		{ name: "RPAREN", regex: /^\)/ }
		{ name: "LBRACE", regex: /^{/ }
		{ name: "RBRACE", regex: /^}/ }
		{ name: "COLON", regex: /^:/ }
		{ name: "SEMI", regex: /^;/ }
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


stringifyStatements = (stmts, indent) ->
	"{\n" +
		(for stmt in stmts.statements
			tabs(indent + 1) + stmt.stringify(indent + 1) + "\n").join("") +
		tabs(indent) + "}"

tabs = (indent) -> "\t".repeat(indent)
