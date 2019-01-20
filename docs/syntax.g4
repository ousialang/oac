grammar OUSIA;

EXPRESSIONS
	: EXPRESSIONS*
	;



ATOM
	: NUMBER
	| IDENTIFIER
	| SYMBOL
	;

NESTED_EXPRESSION
	: '(' EXPRESSION ')'
	| '[' EXPRESSION ']'
	| '{' EXPRESSION '}'
	;

identifier
	: '_'? (Letter '-'*)* Letter
	;

symbol
	:
	;

comment
	: '#' .*?
	;
