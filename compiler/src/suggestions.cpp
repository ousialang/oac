#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sysexits.h>
#include "main.h"
#include "schemas/symspell_generate.h"

#define INITIAL_FLATBUFFER_SIZE 4096

std::vector<std::string> offer_suggestion(char* misspelled_word) {
	auto deletions_of_words = GetDeletionsOfWords(file);
	auto words_after_deletion = deletions_of_words->words_after_deletion();
	auto words_with_edit_distance = deletions_of_words->words_with_edit_distance();
}

// NB: we use char* becuase main's arguments are char* as well, so why bother
// converting them in the first place?
// TODO OPTIMIZE: explore the possibility of improving performance by iterating
// over a DFA. See
// http://blog.notdot.net/2010/07/Damn-Cool-Algorithms-Levenshtein-Automata.
uint16_t levenshtein_distance(char* str_1, char* str_2) {
    if (str_1 == str_2) { return 0; }
    uint16_t str_1_len = strlen(str_1);
    uint16_t str_2_len = strlen(str_2);
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
	// Many subotpimal implementations store a 2D array of size
	// (str_1_len * str_2_len), but we only need the current column and the
	// previous one. The previous one is cached on the fly in the innermost
	// loop.
    uint16_t column[str_1_len + 1];
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
			// TODO: weighted substitutions according to common spelling
			// mistakes.
			uint16_t substitutions = column[j] + !(str_1[i] == str_2[j]);
			// TODO: transpositions
			column[j] = std::min(std::min(insertions, deletions), substitutions);
			uint16_t previous_cell_cache = current_cell_cache;
		}
    }
    return column[str_2_len];
}


