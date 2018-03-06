#include <iostream>
#include <sysexits.h>

int help_main(int argc, char* argv[]) {
	if (argc == 0) {
		return print_usage_information();
	}
	return EX_OK;
}

int print_usage_information() {
	std::ifstream f(resource_name_to_file_name("usage.txt"));
	if (f.is_open()) {
		std::cout << f.rdbuf();
		return EX_OK;
	}
	return EX_UNAVAILABLE;
}
