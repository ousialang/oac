#include <stdio.h>
#include "cmd/repl.h"
#include "cmd/version.h"

#define PROMPT_STRING "> "
#define INPUT_BUF_SIZE 64

void prompt(char* buf);

int main(int argc, char* argv[]) {
	printf("ousia %i.%i", VERSION_MAJOR, VERSION_MINOR);
	char buf[INPUT_BUF_SIZE];
	for (;;) {
		prompt(buf);
	}
	return 0;
}

void prompt(char* buf) {
	char c = getchar();
	printf("%s", PROMPT_STRING);
}
