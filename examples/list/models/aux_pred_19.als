fun int32_max[es: set (i320+i321+i322+i323+i324+i325+i326+i327+i328+i329+i3210+i3211+i3212+i3213+i3214+i3215+i3216+i3217+i3218)] : lone (i320+i321+i322+i323+i324+i325+i326+i327+i328+i329+i3210+i3211+i3212+i3213+i3214+i3215+i3216+i3217+i3218) { es - es.(   i321->(i320)   +   i322->(i320+i321)   +   i323->(i320+i321+i322)   +   i324->(i320+i321+i322+i323)   +   i325->(i320+i321+i322+i323+i324)   +   i326->(i320+i321+i322+i323+i324+i325)   +   i327->(i320+i321+i322+i323+i324+i325+i326)   +   i328->(i320+i321+i322+i323+i324+i325+i326+i327)   +   i329->(i320+i321+i322+i323+i324+i325+i326+i327+i328)   +   i3210->(i320+i321+i322+i323+i324+i325+i326+i327+i328+i329)   +   i3211->(i320+i321+i322+i323+i324+i325+i326+i327+i328+i329+i3210)   +   i3212->(i320+i321+i322+i323+i324+i325+i326+i327+i328+i329+i3210+i3211)   +   i3213->(i320+i321+i322+i323+i324+i325+i326+i327+i328+i329+i3210+i3211+i3212)   +   i3214->(i320+i321+i322+i323+i324+i325+i326+i327+i328+i329+i3210+i3211+i3212+i3213)   +   i3215->(i320+i321+i322+i323+i324+i325+i326+i327+i328+i329+i3210+i3211+i3212+i3213+i3214)   +   i3216->(i320+i321+i322+i323+i324+i325+i326+i327+i328+i329+i3210+i3211+i3212+i3213+i3214+i3215)   +   i3217->(i320+i321+i322+i323+i324+i325+i326+i327+i328+i329+i3210+i3211+i3212+i3213+i3214+i3215+i3216)   +   i3218->(i320+i321+i322+i323+i324+i325+i326+i327+i328+i329+i3210+i3211+i3212+i3213+i3214+i3215+i3216+i3217) )}fun int32_prevs[e: i320+i321+i322+i323+i324+i325+i326+i327+i328+i329+i3210+i3211+i3212+i3213+i3214+i3215+i3216+i3217+i3218] :set (i320+i321+i322+i323+i324+i325+i326+i327+i328+i329+i3210+i3211+i3212+i3213+i3214+i3215+i3216+i3217+i3218) { e.(   i321->(i320)   +   i322->(i320+i321)   +   i323->(i320+i321+i322)   +   i324->(i320+i321+i322+i323)   +   i325->(i320+i321+i322+i323+i324)   +   i326->(i320+i321+i322+i323+i324+i325)   +   i327->(i320+i321+i322+i323+i324+i325+i326)   +   i328->(i320+i321+i322+i323+i324+i325+i326+i327)   +   i329->(i320+i321+i322+i323+i324+i325+i326+i327+i328)   +   i3210->(i320+i321+i322+i323+i324+i325+i326+i327+i328+i329)   +   i3211->(i320+i321+i322+i323+i324+i325+i326+i327+i328+i329+i3210)   +   i3212->(i320+i321+i322+i323+i324+i325+i326+i327+i328+i329+i3210+i3211)   +   i3213->(i320+i321+i322+i323+i324+i325+i326+i327+i328+i329+i3210+i3211+i3212)   +   i3214->(i320+i321+i322+i323+i324+i325+i326+i327+i328+i329+i3210+i3211+i3212+i3213)   +   i3215->(i320+i321+i322+i323+i324+i325+i326+i327+i328+i329+i3210+i3211+i3212+i3213+i3214)   +   i3216->(i320+i321+i322+i323+i324+i325+i326+i327+i328+i329+i3210+i3211+i3212+i3213+i3214+i3215)   +   i3217->(i320+i321+i322+i323+i324+i325+i326+i327+i328+i329+i3210+i3211+i3212+i3213+i3214+i3215+i3216)   +   i3218->(i320+i321+i322+i323+i324+i325+i326+i327+i328+i329+i3210+i3211+i3212+i3213+i3214+i3215+i3216+i3217) )}pred myseq_card[s: JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue, res: JavaPrimitiveIntegerValue] {	let dom = s.JavaPrimitiveIntegerValue |		(no dom and res = i320) or 		(some dom and res = fun_java_primitive_integer_value_add[int32_max[dom],i321])}