#include <stdio.h>
#include <sysexits.h>
#include "cmd/version.h"

int main(int argc, char* argv[]) {
	if (argc > 2) {
		return EX_USAGE;
	}
	printf("Ousia %i.%i.%i-%s", VERSION_MAJOR, VERSION_MINOR, VERSION_PATCH,
	       VERSION_BUILD);
	return EX_OK;
}
