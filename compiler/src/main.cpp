#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sysexits.h>
#include "main.h"
#include "repl/repl.h"
#include "help/help.h"
#include "version/version.h"
#include "feedback/feedback.h"

std::string main_zenzi_dir() {
    #ifdef PLATFORM_IS_MAC
	return "/Library/zenzi/";
    #else
	return NULL;
    #endif
}


std::vector<std::string> offer_suggestion(char* misspelled_word) {

}

uint16_t levenshtein_distance(char* str_1, char* str_2) {
    if (str_1 == str_2) { return 0; }
    size_t str_1_len = strlen(str_1);
    size_t str_2_len = strlen(str_2);
    // Strip common prefix. It doesn't affect the result because of how the
    // Levenshtein string metric is defined, but improves performance.
    while (str_1_len > 0 && str_2_len > 0 && str_1[0] == str_2[0]) {
        str_1++;
	str_2++;
	str_1_len--;
	str_2_len--;
    }
    if (!str_1_len) { return str_2_len };
    if (!str_2_len) { return str_1_len };
    uint16_t table[str_1_len + 1];
    uint16_t i, j;
    for (j=1; j<=str_1_len+1; j++) {
	column[j] = j;
    }
    for (i=1; i<=str_2_len; i++) {
	column[0] = i;
        for (j=1; j<str_2_len; j++) {
	    uint16_t current_cell_cache = column[j];
	    uint16_t deletions = previous_cell_cache + 1;
	    uint16_t insertions = column[j+1] + 1;
	    uint16_t substitutions = column[j] + !(str_1[i] == str_2[j]);
	    // TODO: transpositions
            column[j] = std::min(std::min(insertions, deletions), substitutions);
	    uint16_t previous_cell_cache = current_cell_cache;
        }
    }
    return column[str_2_len];
}

int print_usage() {
	uint16_t c;
	FILE* file = fopen(MAIN_zenzi_DIR "usage.txt", "r");
	if (!file) { return EX_IOERR; }
	while ((c=getc(file)) != EOF) { putchar(c); }
	fclose(file);
	return EX_OK;
}

int main(int argc, char* argv[]) {
	if (argc == 1) {
		return print_usage();
	}
	uint8_t strcmp_result;
	strcmp_result = strcmp(argv[1], "help");
	if (strcmp_result == -1) {
	}
	if (strcmp(argv[1], "version") == 0) {
		return version_main(argc, argv);
	strcmp_build:
		strcmp_result = strcmp(argv[1], "build");
		if (strcmp_result < 0) {
			goto strcmp_repl;
		} else if (strcmp_result > 0) {
			goto strcmp_help;
		} else {
			return help_main(argc, argv);
		}
	strcmp_help:
		strcmp_result = strcmp(argv[1], "help");
		if (strcmp_result < 0) {
			goto strcmp_repl;
		} else if (strcmp_result > 0) {
			goto strcmp_help;
		} else {
			return help_main(argc, argv);
		}
	strcmp_repl:
		strcmp_result = strcmp(argv[1], "repl");
		if (strcmp_result < 0) {
			goto no_match_found;
		} else if (strcmp_result > 0) {
			goto no_match_found;
		} else {
			return repl_main(argc, argv);
		}
	strcmp_version:
		strcmp_result = strcmp(argv[1], "version");
		if (strcmp_result < 0) {
			goto no_match_found;
		} else if (strcmp_result > 0) {
			goto no_match_found;
		} else {
			return version_main(argc, argv);
		}
	no_match_found:
		return EX_USAGE;
}
