window.showExample = (exampleName, targetElement) ->

	if exampleName is ""
		# do nothing


	else if exampleName is "Path-dependent Type Selection"
		targetElement.value = "\
			X:{\n\
			\	Y:at most Any\n\
			\	y:Y\n\
			}\n\
			x:X\n\
			y:x.Y\n\
			y = x.y\n\
			"

	else if exampleName is "Method Type Invocation"
		targetElement.value = "\
			// Define method Ident\n\
			Ident: at least {\n\
			\	p: T\n\
			\	result: T\n\
			\	result = p\n\
			}\n\
			\n\
			// Call method Ident\n\
			x: T\n\
			{ p = x } & Ident . new . result\n\
			"

	else if exampleName is "Polymorphic Method Invocation"
		targetElement.value = "\
			// Declare polymorphic method Ident\n\
			Ident: at least {\n\
			\	T: at least Nothing at most Any\n\
			\	param: T\n\
			\	result: T\n\
			\	result = param  // assign result\n\
			}\n\
			\n\
			V: { u: Any }  // declare V with field u\n\
			\n\
			// Call Ident with member T = V\n\
			{\n\
			\	T: V\n\
			\	param = T.new\n\
			} & Ident.new.result.u  // read field u\n\
			"

	else if exampleName is "WIP-1"
		targetElement.value = "\
			X: {\n\
			\	Y: {\n\
			\		x:X\n\
			\		x = Y.new\n\
			\	}\n\
			\	x:X\n\
			}\n\
			\n\
			x:X\n\
			X.new.x = x\n\
			X.new.Y | {\n\
			\	x: X\n\
			\	x\n\
			}.new\n\
			"

	else
		alert("Unknown example name '#{exampleName}'")