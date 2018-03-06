#include <cstdio>
#include <string>
#include <algorithm>
#include <unistd.h>
#include <sysexits.h>
#include <getopt.h>
#include "version.hpp"

std::string program_files_location() {
#if PLATFORM_IS_DARWIN
	return "/Library/ousia/";
#elif PLATFORM_IS_LINUX
	return "/usr/share/";
#elif PLATFORM_IS_WINDOWS
	return env("%ProgramFiles%");
#else
	return ""; // You're fucked :)
#endif
}

std::string executable_location() {
#if PLATFORM_IS_UNIX
	return "/usr/bin/ousia";
#endif
}
