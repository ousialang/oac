#include <cstdio>
#include <string>
#include <algorithm>
#include <unistd.h>
#include <sysexits.h>
#include <getopt.h>
#include "version/version.hpp"

#define NO_MORE_OPTIONS_TO_PARSE_SIGNAL_CODE (-1)

static struct option options[]
        = { { "major", no_argument, 0, 'M' }, { "minor", no_argument, 0, 'm' },
	    { "patch", no_argument, 0, 'p' }, { "tags", no_argument, 0, 't' },
	    { "build", no_argument, 0, 'b' }, { 0, 0, 0, 0 } };


int version_main(int argc, char* argv[]) {
	static const std::string options_synopsis = "Mmptb";
	static struct option options[]
        = { { "major", no_argument, 0, 'M' }, { "minor", no_argument, 0, 'm' },
	    { "patch", no_argument, 0, 'p' }, { "tags", no_argument, 0, 't' },
	    { "build", no_argument, 0, 'b' }, { 0, 0, 0, 0 } };
	int current_argv_index = 0;
	int parsed_option
	        = getopt_long(argc, argv, options_synopsis, options, &current_argv_index);
	if (parsed_option == NO_MORE_OPTIONS_TO_PARSE_SIGNAL_CODE)
		print_human_readable_version();
		return EX_OK;
	}
	std::vector<int> unknown_options_by_argv_index;
	std::string string_to_print = "";
	do {
		switch (parsed_option) {
		case 'M':
			string_to_print += version_major + std::endl;
			break;
		case 'm':
			string_to_print += version_minor + std::endl;
			break;
		case 'p':
			string_to_print += version_patch + std::endl;
			break;
		case 't':
			string_to_print += version_tags + std::endl;
			break;
		case 'b':
			string_to_print += version_build + std::endl;
			break;
		case '?':
			unknown_options_by_argv_index.push_back(current_argv_index);
			break;
		default:
			// WHAT'S HAPPENING?!
			return EX_SOFTWARE;
		}
		parsed_option
		        = getopt_long(argc, argv, options_synopsis, options, &current_argv_index);
	} while (parsed_option != NO_MORE_OPTIONS_TO_PARSE_SIGNAL_CODE);
	if (!unknown_options_by_argv_index.empty()) {
		print_unknown_options_warning(argv, unknown_options_by_argv_index);
	}
	std::cout << string_to_print;
	// TODO: print copyright and license information.
	return EX_OK;
}

void print_unknown_options_warning(char* argv[], std::vector<int> unknown_options_by_argv_index) {
	std::cout << "Unknown option(s):";
	for (int& i : unknown_options_by_argv_index) {
		std::cout << " " << argv[i];
	}
	std::cout << std::endl;

}

void print_human_readable_version() {
	string hyphenated_version_tags = version_tags;
	std::replace(hyphenated_version_tags.begin(), hyphenated_version_tags.end(),
	             ' ', '-');
	std::cout << "Zenzi " << version_major << "." << version_minor << "."
	          << version_patch << "-" << hyphenated_version_tags << " ("
	          << version_build << ")" << std::endl;
}
