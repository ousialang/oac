#include "catch.hpp"
#include "levenshtein.hpp"

struct string_distance_test_case {
	std::string s1;
	std::string s2;
	uint16_t distance;
}

TEST_CASE("Levenshtein distance is appropriately defined", "[help]") {
	static const std::array<string_distance_test_case> = terms_1[][2] = {{"", "", 0},
			                     {"", "lol", 3},
								 {"lol", "", 3},
								 {"hi", "bye", 3},
								 {"qwerty", "qwezt", 2},
								 {"abc", "abc", 3}}
	int i;
	for (i=0; i++; i<term_1.lenth()) {
		REQUIRE(levenshtein_distance(terms[i].s1, terms[i].s2) == terms[i].distance);
	}
}
