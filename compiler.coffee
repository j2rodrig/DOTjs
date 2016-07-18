window.compile = (input, stopAfter) ->
	try
		clearLog()

		tokens = tokenize(input)

		if stopAfter == "tokens"
			return (for tok in tokens
				tok.print()).join('\n')

		ast = parse(tokens)

		if stopAfter == "trees"
			return stringify(ast)


		enclosing = createPredefTree()
		fresh = ast
		contextify(ast, enclosing, fresh)
		output = genProgram(ast)



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
	stringify: (indent) -> stringify(lhsTyp, indent) + " & " + stringify(rhsTyp, indent)

OrType = (lhsTyp, rhsTyp) ->
	type: "OR-TYPE"
	lhs: lhsTyp
	rhs: rhsTyp
	stringify: (indent) -> stringify(lhsTyp, indent) + " | " + stringify(rhsTyp, indent)


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

derivedTypeDecl = (t, lhs, rhsUpper, rhsLower) ->
	if t.lhs is lhs and t.rhsUpper is rhsUpper and t.rhsLower is rhsLower then t else
		t1 = shallowCopyTree(t)
		t1.lhs = lhs
		t1.rhsUpper = rhsUpper
		t1.rhsLower = rhsLower
		t1

derivedTermDecl = (t, lhs, rhs) ->
	if t.lhs is lhs and t.rhs is rhs then t else
		t1 = shallowCopyTree(t)
		t1.lhs = lhs
		t1.rhs = rhs
		t1

derivedAssignment = (t, guard1, lhs1, rhs1) ->
	if t.guard is guard1 and t.lhs is lhs1 and t.rhs is rhs1 then t else
		t1 = shallowCopyTree(t)
		t1.guard = guard1
		t1.lhs = lhs1
		t1.rhs = rhs1
		t1

derivedGuard = (t, condition) ->
	if t.condition is condition then t else
		t1 = shallowCopyTree(t)
		t1.condition = condition
		t1

derivedConstruction = (t, guard, typTree) ->
	if t.typTree is typTree and t.guard is guard then t else
		t1 = shallowCopyTree(t)
		t1.typTree = typTree
		t1.guard = guard
		t1

# insideStatement is true if looking at a statement, false if looking at a base type tree
deepCopyTree = (t, mutator, insideStatement) ->

	#
	# Do mutations of subtrees.
	# We don't copy any Id trees here because they don't have subtrees. (Side Note: if we did copy Id trees, we would have to make sure the enclosing and definingTree members got copied.)
	# Although technically allowed by syntax, we ignore guards on id and TERM-SELECT trees (because such guards are useless anyway).
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
			if anyDifferent then stmt1 else t   # only return the copied tree if any subtrees are different

		else if t.type is "AND-TYPE" or t.type is "OR-TYPE"
			lhs1 = deepCopyTree(t.lhs, mutator, insideStatement)
			rhs1 = deepCopyTree(t.rhs, mutator, insideStatement)
			derivedAndOrType(t, lhs1, rhs1)

		else if t.type is "TYPE-DECL"
			rhsUpper = deepCopyTree(t.rhsUpper, mutator, false)
			rhsLower = deepCopyTree(t.rhsLower, mutator, false)
			derivedTypeDecl(t, t.lhs, rhsUpper, rhsLower)

		else if t.type is "TERM-DECL"
			rhs = deepCopyTree(t.rhs, mutator, false)
			derivedTermDecl(t, t.lhs, rhs)

		else if t.type is "TERM-ASSIGN"
			guard1 = if t.guard then derivedGuard(t.guard, deepCopyTree(t.guard.condition, mutator)) else undefined
			lhs1 = if t.lhs.type is "id"   # don't do mutation of assignment LHS if we're doing member initialization
				t.lhs
			else
				deepCopyTree(t.lhs, mutator, true)
			rhs1 = deepCopyTree(t.rhs, mutator, true)
			derivedAssignment(t, guard1, lhs1, rhs1)

		else if t.type is "CONSTRUCT"
			guard1 = if t.guard then derivedGuard(t.guard, deepCopyTree(t.guard.condition, mutator)) else undefined
			typTree1 = deepCopyTree(t.typTree, mutator, false)
			derivedConstruction(t, guard1, typTree1)

		else
			t

	mutator(t1, insideStatement)


createPredefTree = () ->
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
	predefTree


findMember = (name, typTree, lowerBound) ->

	if typTree.type is "STATEMENTS"
		for st in typTree.statements
			if st.type is "TYPE-DECL" and st.lhs.match is name
				return if lowerBound then st.rhsLower else st.rhsUpper
			else if st.type is "TERM-DECL" and st.lhs.match is name
				return st.rhs
		undefined

	else if typTree.type is "ID" or typTree.type is "TYPE-SELECT"
		expanded = requireMember(typTree, false)
		findMember(name, expanded, lowerBound)

	else if typTree.type is "AND-TYPE"
		lhsTyp = findMember(name, typTree.lhs, lowerBound)
		rhsTyp = findMember(name, typTree.rhs, lowerBound)
		if lhsTyp and rhsTyp   # the name defined in both sides of the and-type
			if lowerBound
				OrType(lhsTyp, rhsTyp)   # lower bound is an or-type
			else
				AndType(lhsTyp, rhsTyp)  # upper bound is an and-type
		else if lhsTyp
			lhsTyp   # only LHS defines the name
		else
			rhsTyp   # only RHS (or neither side) defines this name

	else if typTree.type is "OR-TYPE"
		lhsTyp = findMember(name, typTree.lhs, lowerBound)
		rhsTyp = findMember(name, typTree.rhs, lowerBound)
		if lhsTyp and rhsTyp   # the name defined in both sides of the or-type
			if lowerBound
				AndType(lhsTyp, rhsTyp)  # lower bound is an and-type
			else
				OrType(lhsTyp, rhsTyp)   # upper bound is an or-type
		else
			undefined  # at least one side does not define the name

	else if typTree.type is "CONSTRUCT"
		findMember(name, fullyInlined(typTree.typTree))

	else if typTree.type is "ANY"
		undefined

	else if typTree.type is "NOTHING"
		# throw new Error("Attempt to find member '#{name}' in type Nothing on line #{typTree.line} character #{typTree.column}, which contains contradictory definitions of '#{name}'.")
		# Don't generate any errors if findMember is called on Nothing.
		# The logic here is this: Since Nothing contains contradictory definitions of the given name, we will assume
		#  the programmer meant the name to refer to some enclosing scope.
		undefined

	else
		throw new Error("Internal compiler error: Expected a type tree in findMember(\"#{name}\"), got '#{typTree.type}' tree")

containsBase = (typTree, base) ->  # tests whether an as-constructed type tree contains the given base tree

	if typTree is base
		true
	else if typTree.type is "AND-TYPE"
		containsBase(typTree.lhs, base) or containsBase(typTree.rhs, base)
	else if typTree.type in ["STATEMENTS", "ANY", "NOTHING", "ID", "TYPE-SELECT"]
		false
	else
		throw new Error("Internal compiler error: Expected a fully-expanded type tree in containsBase, got '#{typTree.type}' tree")

# Takes any type and returns a constructible version without OrTypes. expandName is a boolean function 
condenseBasesForConstruction = (typTree, expandName) ->

	if typTree.type in ["STATEMENTS", "ANY", "NOTHING"]
		typTree

	else if typTree.type is "ID" or typTree.type is "TYPE-SELECT"
		if expandName(typTree)
			expanded = requireMember(typTree, true)
			condenseBasesForConstruction(expanded, expandName)
		else
			typTree

	else if typTree.type is "AND-TYPE"
		AndType(condenseBasesForConstruction(typTree.lhs, expandName), condenseBasesForConstruction(typTree.rhs, expandName))

	else if typTree.type is "OR-TYPE"
		lhsExpanded = condenseBasesForConstruction(typTree.lhs, (t) -> true)   # find the fully-expanded set of base types. Do not memoize!
		if containsBase(lhsExpanded, Nothing)
			condenseBasesForConstruction(typTree.rhs, expandName)   # use right-hand side if left-hand side contains Nothing
		else
			condenseBasesForConstruction(typTree.lhs, expandName)   # otherwise, use left-hand side

	else
		throw new Error("Internal compiler error: Expected a type tree in condenseBasesForConstruction, got '#{typTree.type}' tree")

# Takes any type and returns a constructible version without OrTypes. Memoized.
asConstructed = (typTree) ->
	if not typTree.asConstructed
		typTree.asConstructed = condenseBasesForConstruction(typTree, (t) -> false)
	typTree.asConstructed

# Takes any type and returns a constructible version without OrTypes. All named types are expanded to their definitions. Memoized.
fullyInlined = (typTree) ->
	if not typTree.fullyInlined
		typTree.fullyInlined = condenseBasesForConstruction(typTree, (t) -> true)
	typTree.fullyInlined


# 
lookupMember = (nameTree, lowerBound) ->

	typTree =
		if nameTree.type is "id" or nameTree.type is "ID"
			typ = undefined
			enclosing = nameTree.enclosing
			while enclosing
				typ = findMember(nameTree.match, fullyInlined(enclosing), lowerBound)
				if typ
					nameTree.definingTree = enclosing   # remember which type tree actually defines this name (important for type unpacking)
					if typ.enclosing isnt enclosing
						# replace all instances of (original-context) typ.enclosing with (current-context) enclosing.
						typ = replaceSelfWithSelf(typ, typ.enclosing, enclosing)
					break
				enclosing = enclosing.enclosing
			typ

		else if nameTree.type is "TYPE-SELECT"
			prefixTyp = requireMember(nameTree.prefix, false)
			typ = findMember(nameTree.ID, prefixTyp, lowerBound)
			typ = replaceSelfWithPrefix(typ, typ.enclosing, nameTree.prefix)  # replace all Ids where IdTree.definingTree==typ.enclosing with selection "prefix.Id"
			typ

		else if nameTree.type is "TERM-SELECT"
			prefixTyp = requireMember(nameTree.prefix, false)
			typ = findMember(nameTree.id, prefixTyp, lowerBound)
			typ = replaceSelfWithPrefix(typ, typ.enclosing, nameTree.prefix)  # replace all Ids where IdTree.definingTree==typ.enclosing with selection "prefix.Id"
			typ

		else if nameTree.type is "CONSTRUCT"   # the "named" thing here is anonymous
			nameTree  # return the constructor itself

		else
			throw new Error("Internal compiler error: Expected name tree in lookupMember, got '#{nameTree.type}'")

requireMember = (nameTree, lowerBound) ->
	typTree = lookupMember(nameTree, lowerBound)

	if not typTree
		throw new Error("Error: Unable to find type of '#{stringify(nameTree)}' on line #{nameTree.line} character #{nameTree.column}")
	else
		typTree


definingTree = (tree) ->
	if tree.type is "ID" or tree.type is "id"
		if not tree.definingTree
			requireMember(tree)   # do a lookup to ensure definingTree is set
		tree.definingTree
	else
		throw new Error("Internal compiler error: Expected id/ID tree in definingTree, got '#{tree.type}' tree")


replaceSelfWithPrefix = (typ, enclosing, prefix) ->
	# replace all Ids where IdTree.definingTree == enclosing with TypeSelect(prefix, ID) or TermSelect(prefix, ID)
	deepCopyTree(typ, (t) ->
		if t.type is "ID"
			if definingTree(t) is enclosing
				log(types, "Replacing #{enclosing.selfName}.#{t.match} with #{stringify(prefix)}.#{t.match} where #{enclosing.selfName}:#{stringify(enclosing)}")
				t1 = shallowCopyTree(t)
				t1.type = "TYPE-SELECT"
				t1.ID = t.match
				t1.prefix = prefix
				t1.stringify = (indent) -> "#{stringify(t1.prefix, indent)}.#{t1.ID}"
				return t1
		if t.type is "id"
			if definingTree(t) is enclosing
				log(types, "Replacing #{enclosing.selfName}.#{t.match} with #{stringify(prefix)}.#{t.match} where #{enclosing.selfName}:#{stringify(enclosing)}")
				t1 = shallowCopyTree(t)
				t1.type = "TERM-SELECT"
				t1.id = t.match
				t1.prefix = prefix
				t1.stringify = (indent) -> "#{stringify(t1.prefix, indent)}.#{t1.id}"
				return t1
		t
	)

replaceSelfWithSelf = (typ, enclosing, newEnclosing) ->

	deepCopyTree(typ, (t) ->
		if t.type is "ID" or t.type is "id"
			if definingTree(t) is enclosing
				t1 = shallowCopyTree(t)
				t1.definingTree = newEnclosing
				t1.match = t.match
				return t1
		t
	)

contextify = (tree, enclosingTree, freshTree) ->

	if tree.type is "STATEMENTS"
		freshTree.enclosing = enclosingTree  # allow lookup into outer contexts
		enclosingTree = freshTree   # we've stepped inside the type; the fresh type becomes the enclosing type
		for st in tree.statements
			if st.type is "TERM-DECL"
				contextify(st.rhs, enclosingTree, st.rhs)  # we have a fresh type on the right-hand side
			else if st.type is "TYPE-DECL"
				contextify(st.rhsLower, enclosingTree, st.rhsLower)  # two fresh type trees
				contextify(st.rhsUpper, enclosingTree, st.rhsUpper)
			else if st.type is "TYPE-ASSIGN"
				contextify(st.rhs, enclosingTree, st.rhs)   # we have a fresh type on the right-hand side
			else if st.type is "TERM-ASSIGN"
				if st.guard then contextify(st.guard.condition, enclosingTree, freshTree)
				contextify(st.lhs, enclosingTree, freshTree)
				contextify(st.rhs, enclosingTree, freshTree)
			else
				contextify(st, enclosingTree, freshTree)

	else if tree.type is "ID" or tree.type is "id"
		if tree.guard then contextify(tree.guard.condition, enclosingTree, freshTree)
		tree.enclosing = enclosingTree

	else if tree.type is "TYPE-SELECT" or tree.type is "TERM-SELECT"
		if tree.guard then contextify(tree.guard.condition, enclosingTree, freshTree)
		contextify(tree.prefix, enclosingTree, freshTree)

	else if tree.type is "AND-TYPE" or tree.type is "OR-TYPE"
		contextify(tree.lhs, enclosingTree, freshTree)
		contextify(tree.rhs, enclosingTree, freshTree)

	else if tree.type is "CONSTRUCT"
		if tree.guard then contextify(tree.guard.condition, enclosingTree, freshTree)
		contextify(tree.typTree, enclosingTree, tree.typTree)   # new fresh type tree

	else
		throw new Error("Internal compiler error: Unexpected '#{tree.type}' tree in contextify")


### TYPE COMPARISONS ###

isSubType = (t0, t1) ->

	log(types, "#{stringify(t0)} <:? #{stringify(t1)}")

	#TODO: variance?

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

	else if t1.type is "AND-TYPE"
		isSubType(t0, t1.lhs) and isSubType(t0, t1.rhs)

	else if t1.type is "OR-TYPE"
		isSubType(t0 t1.lhs) or isSubType(t0, t1.rhs)

	else if t0.type is "AND-TYPE"
		isSubType(t0.lhs, t1) or isSubType(t0.rhs, t1)

	else if t0.type is "OR-TYPE"
		isSubType(t0.lhs, t1) and isSubType(t0.rhs, t1)

	else if t1.type is "CONSTRUCT"
		# Unpack constructor types
		isSubType(t0, t1.typTree)

	else if t0.type is "CONSTRUCT"
		# Unpack constructor types
		isSubType(t0.typTree, t1)

	else if t1.type is "TYPE-SELECT" and t0.type is "TYPE-SELECT" and t0.ID is t1.ID and isSameReference(t0.prefix, t1.prefix)
		# x.L <: x.L ; same prefix, same type member name
		true

	else if t1.type is "ID" and t0.type is "ID" and t0.match is t1.match and definingTree(t0) is definingTree(t1)
		# x.L <: x.L ; same prefix, same type member name ; the "prefix" x here is the self-reference of the ID
		true

	else if t0.type is "TYPE-SELECT" or t0.type is "ID"
		# x.L <: T ; widen x.L to its upper bound
		t0upper = requireMember(t0, false)
		isSubType(t0upper, t1)

	else if t1.type is "TYPE-SELECT" or t1.type is "ID"
		# T <: x.L ; widen x.L to its lower bound
		t1lower = requireMember(t1, true)
		isSubType(t0, t1lower)

	else if not (t0.type is "STATEMENTS" and t1.type is "STATEMENTS")
		throw new Error("Internal compiler error: Expected types in isSubType, but attempted to compare a #{t0.type} tree with a #{t1.type} tree")

	else
		# Make sure all declarations in the t1 statement block subsume declarations in t0
		for st1 in t1.statements

			if st1.type is "TYPE-DECL"
				name1 = st1.lhs.match
				st0upper = findMember(name1, t0, false)
				st0lower = findMember(name1, t0, true)
				if not st0upper
					log(types, "isSubType: Failure to find member #{name1} in type #{stringify(t0)}")
					return false
				if not isSubType(st0upper, st1.rhsUpper)
					log(types, "isSubType: #{stringify(st0upper)}, the upper bound of #{name1} in #{stringify(t0)}, is not compatible with #{stringify(st1.rhsUpper)}")
					return false
				if not isSubType(st1.rhsLower, st1lower)
					log(types, "isSubType: #{stringify(st1.rhsLower)} is not compatible with #{stringify(st0lower)}, the lower bound of #{name1} in #{stringify(t0)}")
					return false
			
			else if st1.type is "TERM-DECL"
				name1 = st1.lhs.match
				member0 = findMember(name1, t0)
				if not member0
					log(types, "isSubType: Failure to find member #{name1} in type #{stringify(t0)}")
					return false
				if not isSubType(member0, st1.rhs)  # TODO: strengthen this condition when variance is added
					log(types, "isSubType: Type #{stringify(member0)} declared for field #{name1} is not compatible with type #{stringify(st1.rhs)}")
					return false
				if not isSubType(st1.rhs, member0)  # TODO: strengthen this condition when variance is added
					log(types, "isSubType: Type #{stringify(st1.rhs)} declared for field #{name1} is not compatible with type #{stringify(member0)}")
					return false

		# All declarations are compatible. Subtype check succeeds.
		true

# an approximation of term equivalence
isSameReference = (tree0, tree1) ->
	if tree0.type is "id"
		tree1.type is "id" and tree0.match is tree1.match and definingTree(tree0) is definingTree(tree1)
	else if tree0.type is "TERM-SELECT"
		tree1.type is "TERM-SELECT" and tree0.id is tree1.id and isSameReference(tree0.prefix, tree1.prefix)
	else if tree0.type is "CONSTRUCT"
		tree1.type is "CONSTRUCT" and tree0.typTree is tree1.typTree
	else
		throw new Error("Internal compiler error: Expected a term tree in isSameReference, got '#{tree0.type}' tree")



### CODEGEN ###

genProgram = (ast) ->

	# Create a unique-identifier counter
	uniqueId = -1
	getId = () ->
		uniqueId += 1
		uniqueId

	# Generate a constructor for the entire program.
	output = []
	genCtor(ast, true, getId, 0, output)
	output.push(";")  # an unnecessary semicolon to make the output look more complete
	output.join("")

genBaseCalls = (base, fresh, getId, indent, output) ->

	if base.type is "STATEMENTS"

		# hoist type-member initializers to top of statement block
		for st in base.statements
			if st.type is "TYPE-DECL"
				genTypeInitializer(fresh, st.lhs.match, st.rhsLower, getId, indent + 1, output)

		# generate executable terms
		for st in base.statements
			if st.type is "TERM-ASSIGN"
				output.push(tabs(indent + 1))
				maybeGenGuard(st, getId, indent + 1, output)
				gen(st.lhs, getId, indent + 1, output)
				output.push(" = ")
				gen(st.rhs, getId, indent + 1, output)
				output.push(";\n")

				# typecheck assignment
				upperRhs = lookupMember(st.rhs, false)
				lowerLhs = lookupMember(st.lhs, true)
				if not isSubType(upperRhs, lowerLhs)
					throw new Error("Type mismatch:\n\tExpected: #{stringify(lowerLhs, 1)}\n\tGot: #{stringify(upperRhs, 1)}\n\tLine #{st.line} character #{st.column}")

			else if st.type in ["id", "TERM-SELECT", "CONSTRUCT"]
				output.push(tabs(indent + 1))
				maybeGenGuard(st, getId, indent + 1, output)
				gen(st, getId, indent + 1, output)
				output.push(";\n")

	else if base.type is "ID"
		if base.match isnt "Any"
			requireMember(base, true)  # make sure definingTree is set
			selfName = base.definingTree.selfName
			output.push(tabs(indent + 1))
			output.push("#{selfName}.#{base.match}(#{fresh.selfName});\n")
	else if base.type is "TYPE-SELECT"
		output.push(tabs(indent + 1))
		gen(base.prefix, getId, indent + 1, output)
		output.push(".#{base.ID}(#{fresh.selfName});\n")
	else if base.type is "AND-TYPE"
		genBaseCalls(base.lhs, fresh, getId, indent, output)
		genBaseCalls(base.rhs, fresh, getId, indent, output)
	else if base.type is "ANY"
		# don't need to do anything with Any
	else
		throw new Error("Internal compiler error: Unexpected base type tree #{base.type} in genBaseCalls. Line #{base.line} character #{base.column}")

maybeGenGuard = (tree, getId, indent, output) ->
	if tree.guard
		output.push("if (")
		gen(guard.condition, getId, indent, output)
		output.push(") ")

genCtor = (tree, isConcrete, getId, indent, output) ->

	# assign a unique name for this tree's self-reference
	tree.selfName = "self" + getId()

	cType = asConstructed(tree)
	cannotBeNothing = if isConcrete then fullyInlined(cType) else cType
	if containsBase(cannotBeNothing, Nothing)
		throw new Error("Error: Attempt to initialize an object with a base type of Nothing on line #{tree.line} character #{tree.column}")

	if isConcrete then output.push("(")
	output.push("function(#{tree.selfName}) {\n")
	genBaseCalls(cType, tree, getId, indent, output)
	output.push(tabs(indent + 1))
	output.push("return #{tree.selfName};\n")
	output.push(tabs(indent))
	output.push("}")
	if isConcrete then output.push(")({})")

# Generate a type initializer call. fresh is the type tree containing the type name, typTree defines the bases called by the initializer.
genTypeInitializer = (fresh, name, typTree, getId, indent, output) ->

	if not containsBase(fullyInlined(typTree), Nothing)  # don't bother generating if we would definitely be constructing Nothing

		output.push(tabs(indent))
		output.push("if(!#{fresh.selfName}.#{name})\n")  # define an initializer at runtime only if a same-named initializer has not been defined yet
		output.push(tabs(indent+1))
		output.push("#{fresh.selfName}.#{name}")
		output.push(" = ")
		genCtor(typTree, false, getId, indent+1, output)
		output.push(";\n")

gen = (tree, getId, indent, output) ->

	if tree.type is "id"
		output.push(definingTree(tree).selfName)
		output.push(".")
		output.push(tree.match)

	else if tree.type is "TERM-SELECT"
		gen(tree.prefix, getId, indent, output)
		output.push(".")
		output.push(tree.id)

	else if tree.type is "CONSTRUCT"
		genCtor(tree.typTree, true, getId, indent, output)

	else
		throw new Error("Internal compiler error: Expected term tree in gen function, got #{tree.type} tree")


### PRINTING ###

stringify = (t, indent = 0) ->

	if t.type is "id" or t.type is "ID"
		prefix =
			if t.definingTree
				if t.definingTree.selfName
					t.definingTree.selfName + "."
				else
					"<<unnamed>>."
			else if t.enclosing
				"<<#{t.enclosing.selfName} or enclosing>>."
			else
				""
		"#{prefix}#{t.match}"

	else if t.type is "TERM-SELECT"
		"#{stringify(t.prefix, indent)}.#{t.id}"

	else if t.type is "TYPE-SELECT"
		"#{stringify(t.prefix, indent)}.#{t.ID}"

	else if t.type is "CONSTRUCT"
		stringify(t.typTree, indent) + ".new"

	else if t.type is "TERM-DECL"
		"#{stringify(t.lhs, indent)} : #{stringify(t.rhs, indent)}"

	else if t.type is "TYPE-DECL"
		"#{stringify(t.lhs, indent)} : at least #{stringify(t.rhsLower, indent)} at most #{stringify(t.rhsUpper, indent)}"

	else if t.type is "STATEMENTS"
		stringifyStatements(t, indent)

	else if t.stringify
		t.stringify(indent)

	else
		"<< #{t.type} tree >>"

stringifyStatements = (stmts, indent) ->
	"{\n" +
		(for stmt in stmts.statements
			tabs(indent + 1) + stringify(stmt, indent + 1) + "\n").join("") +
		tabs(indent) + "}"

tabs = (indent) -> "\t".repeat(indent)

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