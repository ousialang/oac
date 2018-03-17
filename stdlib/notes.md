* _ for short functions, es:

        1+_
        _>_
        _ is_prime

* parentheses in apply can be omitted if there's only one argument and if the
  message and the argument are not both words. Es.

        1 + two
        1 + 2
        "wabba lubba dub dub" split " "
        "wabba lubba dub dub" split space # WRONG

* Use of literals ala Elixir. Es.

        list sort (algo: $MERGESORT)

		print "qwerty"
		STDOUT print "FATAL!"
		let sum = foldr '+
		let product = foldr '*

		for 5 times do {}
		for a in x do {}
		for A in X, B in Y do {}
		for N in 2..10 by 3 {}
		if condition do {}
		unless condition do {}
		while condition do {}

		N as $STRING
		flip
		group_by [3]
		flip
		zip_with_index
		map {
			(x, i) => (x, )
		}
		map []

* Strong metaprogramming capabiities
* I first couldn't decide Ousia's stand in the expressions VS statements
  debates. Now I know. There won't be any difference. Instead, "statements"
  (e.g. class, def, val, var) will just be well-engineered macros. This way, I
  can focus on the macro system, which needs to be very powerful and well
  written (see Racket), and everyone can create powerful macros. I need to be
  careful though, I don't want macros to turn the code into an unreadable mess.
  => IDIOMATIC MACROS. I allow powerful macros yet disallow non-idiomatic
  syntax. This way the code will even be homiconic at a semantic level (and
  not syntactical, contrary to Lisp) and I can create the metaprogramming
  utilies that I wanted, but always at COMPILE TIME.
* In order to make code more readable, I can allow only one macro per statement,
  which will be defined by the first word. Nope. Bad idea.
* Some macros:

        if condition then this else that
        while condition do this
        until condition do this
        for (A, N from 1) for list if A > 2
        do this while condition
        do this until condition
        def ...

        subclass SUPER_BOOSTER {
        }

        extend VEHICLE with (PLUGIN match {
          $BOOSTER: SUPER_BOOSTER
          $WEAPONS: MACHINE_GUN
          $AUTOMATIC: AUTO_PILOT
        })
* One of the few untyped functional languages
* Focus on interface design. I am not satisfied with how existing languages
  handle interface design; i.e. they make poor design choices.
* "Well-designed programs treat the user's attention and concentration as a precious and limited resource, only to be claimed when necessary."
* See http://www.faqs.org/docs/artu/ch01s06.html
* I had a beautiful idea: replace much of the ALGOL-like noisy syntax with
  case-sensitivity. Programming languages are already case-sensitive, but we'll
  make it a part of the syntax. Expressions can have "syntax goodies" with
  symbols and undercase letters, but semantically significant code must be in
  uppercase. Es.:
    import FOO as BAR
    let ABC = XYZ length + 5 abs
    class FOO_BAR extends FOO
