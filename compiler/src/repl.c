#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sysexits.h>
#include "repl/repl.h"
#include "version/version.h"

#define PROMPT_STRING "> "
#define INPUT_BUF_SIZE 128

void repl_prompt(char* buf);

char* repl_read_line(void) {
	char* line = malloc(INPUT_BUF_SIZE);
	if (!line) {
		return NULL;
	}
	size_t i = 0;
	char c;
	while ((c = getchar()) != '\n') {
		if (i == INPUT_BUF_SIZE && !realloc(line, i << 1)) {
			char* new_line = malloc(i << 1);
			if (!new_line) {
				return NULL;
			}
			strcpy(new_line, line);
			free(line);
			line = new_line;
		}
		line[i++] = c;
	}
	line[i] = '\0';
	return line;
}

int repl_main(int argc, char* argv[]) {
	printf("ousia %i.%i\n", VERSION_MAJOR, VERSION_MINOR);
	char buf[INPUT_BUF_SIZE];
	for (;;) {
		repl_prompt(buf);
	}
	return EX_OK;
}

void repl_prompt(char* buf) {
	printf(PROMPT_STRING);
	char* line = repl_read_line();
	free(line);
}
