#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <dirent.h>
#include "log.h"
#include "main.h"

char* home_dir(void) {
	char* home = getenv("HOME");
	if (home) {
		return home;
	}
	return NULL;
}

int ousia(void) { return 0; }

int main(int argc, char* argv[]) {
	if (argc == 1) {
		return ousia();
	}
	char* home = home_dir();
	char* cmd = malloc(strlen(home) + strlen("/.ousia/plugins")
	                   + strlen(argv[1]));
	strcpy(cmd, home);
	strcat(cmd, "/.ousia/plugins/");
	strcat(cmd, argv[1]);
	// system(cmd);
	return 0;
}
