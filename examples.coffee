window.showExample = (exampleName, targetElement) ->

	if exampleName is ""
		# do nothing

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