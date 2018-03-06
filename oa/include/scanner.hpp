#ifndef SCANNER_H_
#define SCANNER_H_
/*
#include <stdint.h>

typedef struct token token;

typedef struct {
	bool is_alpha;
} token_word;

typedef struct {
	uint8_t base;
	char* digits;
} token_number;

typedef enum {
	ROUND,
	SQUARE,
	CURLY,
} token_bracket;

typedef struct {
	char bracket;
	token** tokens;
} token_block;

typedef enum {
	WORD,
	INTEGER,
	DECIMAL,
	BLOCK,
} token_type;

typedef union {
	token_number number;
	token_block block;
} token_info;

typedef struct {
	token_type type;
	token_info* info;
	size_t index;
	unsigned short length;
} token;
*/
#endif
