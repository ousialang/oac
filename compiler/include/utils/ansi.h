#ifndef ANSI_H_
	#define ANSI_H_
	#define ANSI_RESET "\033[00m"
	#define ANSI_BOLD "\033[01m"
	#define ANSI_ITALIC "\033[03m"
	#define ANSI_UNDERLINE "\033[04m"
	#define ANSI_BLACK "\033[30m"
	#define ANSI_RED "\033[31m"
	#define ANSI_GREEN "\033[32m"
	#define ANSI_YELLOW "\033[33m"
	#define ANSI_BLUE "\033[34m"
	#define ANSI_MAGENTA "\033[35m"
	#define ANSI_CYAN "\033[36m"
	#define ANSI_WHITE "\033[37m"
	// The length of all escape sequences. Used for some string length
	// calculations.
	#define ANSI_ESCAPE_CODE_LENGTH 5
#endif
