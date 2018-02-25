#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>
#include <sysexits.h>
#include "scanner.h"
//#define TREE_TYPE token*
#include "utils/tree.h"
#include "utils/stack.h"

#define BUFFER_SIZE 4096
#define MAX_TOKEN_SIZE 16

unsigned long strlen(const char*);
char* strchr(const char*, int);
char* strncpy(char*, const char*, unsigned long);

char* tokens_from_file(char filename[]) {
	FILE* file = fopen(filename, "r");
	size_t size;
	char* buffer;
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
token_bracket bracket_type (char *bracket) {
  switch (*bracket) {
    case '(':
      return token_bracket.
  }
}*/

bool is_bracket_left(char bracket) { return strchr("([{", bracket); }

char matching_bracket(char bracket) {
	switch (bracket) {
	case '(':
		return ')';
	case '{':
		return '}';
	case '[':
		return ']';
	case ')':
		return '(';
	case '}':
		return '{';
	case ']':
		return '[';
	default:
		exit(EX_SOFTWARE);
	}
}

tree* tokens_from_string(char source[]) {
	/*token token;
	token_info info;
	char* lexeme = malloc(MAX_TOKEN_SIZE);
	int i = 0;
	int i_lexeme = 0;
	tree* ast = tree_init();
	stack* brackets = stack_init();
	while (source[i] != '\0') {
		i_lexeme = i;
		if (isalpha(source[i])) {
			do { i++; } while (!isalpha(source[i]));
			tree_add_sibling(ast,
			        &(token){ WORD, &(token_info){}, i_lexeme,
				                  i - i_lexeme });
			// token.info =
			token.length = i - i_lexeme;
		} else if (';' == source[i] || '\n' == source[i]) {
			tree_add_sibling_empty(ast);
			ast = ast->rsibling;
		} else if (isdigit(source[i])) {
			do { i++; } while (!isdigit(source[i]));
			/*if (source[i] == '.') {
			  while (!isdigit(source[i])) {
			    i++;
			  }
			}*//*
			tree_add_sibling(ast, &(token){
				WORD, &(token_info){ .number = (token_number){ 10 } },
				i_lexeme, i - i_lexeme
			});
			// token.info =
			token.length = i - i_lexeme;
		} else if (source[i] == '(' || source[i] == '{' || source[i] == '[') {
			stack_push(brackets, source[i]);
		} else if (source[i] == ')' || source[i] == '}' || source[i] == ']') {
			if (source[i] == matching_bracket(stack_top(brackets))) {
				stack_pop(brackets);
			} else {
				assert(0);
			}
		} else if ('"' == source[i]) {
			//tree_add_sibling_empty(ast, '"');
		}
		tree_add_sibling_empty(ast);
	}
	return tokens;*/
	return NULL;
}
