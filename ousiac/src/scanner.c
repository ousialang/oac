#include <ctype.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include "scanner.h"

#define BUFFER_SIZE 4096

unsigned long strlen (const char *);
char* strchr (const char *, int);
char *strncpy(char *, const char *, unsigned long);

char* tokens_from_file (char filename[]) {
  FILE *file = fopen(filename, "r");
  size_t size;
  char *buffer;
  if (file) {
    fseek(file, 0, SEEK_END);
    size = ftell(file);
    buffer = malloc(sizeof(char) * (size + 1));
    fread(buffer, sizeof(char), size, file);
    buffer[size] = '\0';
    fclose(file);
  }
  return buffer;
}
/*
token_bracket_t bracket_type (char *bracket) {
  switch (*bracket) {
    case '(':
      return token_bracket_t.
  }
}*/

bool is_bracket_left (char bracket) {
  return strchr("([{", bracket);
}

char matching_bracket(char bracket) {
  switch (bracket) {
    case '(':
      return ')';
    case ')':
      return '(';
    case '[':
      return ']';
    case ']':
      return '[';
    case '{':
      return '}';
    case '}':
      return '{';
    default:
      return '?';
  }
}

token_t** tokens_from_string (char source[]) {
  token_t **tokens;
  token_t token;
  token_info_t info;
  char *lexeme;
  int index_lexeme;
  int index_char;
  int index_current_token;
  int index_current_statement;
  int length = strlen(source);
  bool is_new_token = true;
  int brackets = 0;
  while (index_char < length) {
    index_lexeme = index_char;
    if (isalpha(source[index_char])) {
      do {
        index_char++;
      } while (!isalpha(source[index_char]));
      tokens[index_current_token] = &(token_t) {
        WORD,
        &(token_info_t) {},
        index_lexeme,
        index_char-index_lexeme
      };
      //token.info =
      token.length = index_char - index_lexeme;
    } else if (';' == source[index_char] || '\n' == source[index_char]) {
      index_current_statement++;
    } else if ('$' == source[index_char]) {
      tokens[index_current_token] = &(token_t) {
        WORD,
        &(token_info_t) {},
        index_lexeme,
        index_char
      };
      tokens[index_current_token] = &(token_t) {WORD, &info, index_lexeme, index_char};
      do {
        index_char++;
      } while (!isalpha(source[index_char]));
      //tokens[index_current_token]->info =
      tokens[index_current_token]->length = index_char - index_lexeme;
    } else if (isdigit(source[index_char])) {
      do {
        index_char++;
      } while (!isdigit(source[index_char]));
      /*if (source[index_char] == '.') {
        while (!isdigit(source[index_char])) {
          index_char++;
        }
      }*/
      lexeme = malloc(sizeof(char) * (index_char-index_lexeme+1));
      tokens[index_current_token] = &(token_t) {
        WORD,
        &(token_info_t) {
          .integer = (token_integer_t) {10}
        },
        index_lexeme,
        index_char-index_lexeme
      };
      //token.info =
      token.length = index_char - index_lexeme;
    } else if (source[index_char] == '(') {
      //brackets = brackets << 2;
    } else if (source[index_char] == ')') {
      //if (brackets ^ 3 == 3)
    } else if ('"' == source[index_char]) {
      index_lexeme++;
     }
    index_current_token++;
  }
  return tokens;
}
