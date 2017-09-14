# Arguments

Classes and other constructs such as methods can take regular arguments:

    (abc, xyz)

It is also possible to provide optional arguments, but they must be named and
always passed from their names:

    (abc, xyz, jkl: none)

When defining such arguments, it is required to define a default value.

You can also define a list of arguments with an ellipsis:

    (abc, xyz, arg: something, ...)

You can then access those arguments with the `ellipsis` value. It will be
