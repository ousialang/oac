#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sysexits.h>
#include "schemas/radix_tree.hpp"
#include "levenshtein.hpp"

// int total_hours_wasted_here = 18

namespace utils::levenshtein {

// This algorithm for fuzzy string matching is obscure (1) and infamous (2)
//
//
// Original paper: "Fast String Correction with Levenshtein-Automata" (Schulz,
// K. & Mihov, S. IJDAR (2002) 5: 67. https://doi.org/10.1007/s10032-002-0082-8).
//
// 1. http://julesjacobs.github.io/2015/06/17/disqus-levenshtein-simple-and-fast.html
// 2. http://blog.mikemccandless.com/2011/03/lucenes-fuzzyquery-is-100-times-faster.html

class LevenshteinAutomaton {
	string word;
	std::vector<std::tuple<int,int>> positions;

public:
	LevenshteinAutomaton(std::string word)
		: positions {};

	void next(char x) {
		for (std::tuple<int,int>& position : this->positions) {

		}
	}
}

std::vector<bool> characteristic_vector(char c, std::string word) {
	std::vector<bool> characteristic_vector;
	for (char& current_char : word) {
		characteristic_vector.push_back(current_char == c);
	}
	return characteristic_vector;
}

std::vector<int> profile_sequence(std::string word) {
	std::map<char,int> profile_id_by_character;
	std::vector<int> profile_sequence;
	int id_counter = 1;
	for (char& c : word) {
		if (profile_id_by_character.find(c) == profile_id_by_character.end()) {
			profile_sequence.push_back(profile_id_by_character[c]);
		} else {
			profile_sequence.push_back(id_counter);
			profile_id_by_character[c] = id_counter++;
		}
	}
	return profile_sequence;
}

std::vector<int> profile_subsequences(std::string word, int subsequence_length) {
	std::vector<int> subsequences;
	if (subsequnce_length < 1) { return subsequences; }
	int i = subsequence_length;
	int i_upper_bound = word.length() - sequence_length;
	while (i < i_upper_bound) {
		int j = i - subsequence_length;
		while (j < i) {
			std::map<char,int> profile_id_by_character;
			int id_counter = 1;
			if (profile_id_by_character.find(word[j]) == profile_id_by_character.end()) {
				subsequences.push_back(profile_id_by_character[word[j]]);
			} else {
				subsequences.push_back(id_counter);
				profile_id_by_character[word[j]] = id_counter++;
			}
			j++;
		}
		i++;
	}
	return subsequences;
}

std::tuple<int,int> next_position(std::tuple<int,int> position, string word) {
	if () {
		i++;
	} else if () {
		e++;
	}
}

int maximum_levenshtein_distance(int word_length) {
	return log2(word_length);
}

// NB: we use char* becuase main's arguments are char* as well, so why bother
// converting them in the first place?
// TODO OPTIMIZE: explore the possibility of improving performance by iterating
// over a DFA. See
// http://blog.notdot.net/2010/07/Damn-Cool-Algorithms-Levenshtein-Automata.
uint16_t distance(char* str_1, char* str_2) {
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
	// previous one.
	uint16_t column[2][str_1_len + 1];
	uint8_t current_column = 0;
	uint16_t i, j;
	for (j = 1; j <= str_1_len + 1; j++) { column[current_column][j] = j; }
	for (i = 1; i <= str_2_len; i++, current_column ^= 1) {
		column[current_column] = i;
		for (j = 1; j < str_2_len; j++) {
			uint16_t deletions = column[current_column ^ 1][j] + 1;
			uint16_t insertions = column[current_column][j + 1] + 1;
			// TODO: weighted substitutions according to common spelling
			// mistakes.
			uint16_t substitutions = column[current_column] + !(str_1[i] == str_2[j]);
			// TODO: transpositions
			column[j] = std::min(std::min(insertions, deletions), substitutions);
		}
	}
	return column[current_column][str_2_len];
}

}
