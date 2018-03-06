#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sysexits.h>
#include "repl.hpp"
#include "version.hpp"

#define PROMPT_STRING "> "
#define INPUT_BUF_SIZE 128

void repl_prompt(char* buf);

char* repl_read_line(void) {
	std::string line = "";
	while ((c = getchar()) != '\n') { line += c; }
	return line;
}

int repl_main(int argc, char* argv[]) {
	std::cout << "Zenzi"
		      << version_major
			  << "."
			  << version_minor
			  << "-"
			  << version_tags
			  << std::endl;
	return repl_loop();
}

int repl_loop() {
	print_prompt();
	std::string line = repl_read_line();
}

void print_promp() {
#if PLATFORM_IS_NIX
	std::cout << ansi_bold << "=> " << ansi_reset;
#else
	std::cout << "=> ";
#endif
}
