#ifndef SCANNER_H
#define SCANNER_H

struct token_t;

typedef struct {
  bool is_alpha;
} token_word_t;

typedef struct {
  uint8_t base;
  char *digits;
} token_integer_t;

typedef struct {
  char *integer_digits;
  char *decimal_digits;
} token_decimal_t;

typedef enum {
  ROUND,
  SQUARE,
  CURLY,
} bracket_t;

typedef struct {
  char bracket;
  struct token_t **tokens;
} token_block_t;

typedef enum {
  WORD,
  INTEGER,
  DECIMAL,
  BLOCK,
} token_type_t;

typedef union {
  token_integer_t integer;
  token_decimal_t decimal;
  token_block_t block;
} token_info_t;

typedef struct {
  token_type_t type;
  token_info_t *info;
  uint64_t index;
  uint16_t length;
} token_t;

#endif
