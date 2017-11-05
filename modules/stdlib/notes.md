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
  which will be defined by the first word.
