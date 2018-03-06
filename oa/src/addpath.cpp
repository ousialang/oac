/*#include <errno>
#include <filesystem>
#include "tinydir.h"

namespace fs = std::filesystem;

int refresh_files_main(int argc, char* argv[]) {
	tinydir_dir dir;
	if (argc) {
		dir = given_dir(argv[1]);
	} else {
		dir = current_dir();
	}
	while (dir.has_next) {
		tinydir_file file;
		if (file.is_dir) {

		}
		if (tinydir_next(&dir) == -1) {

		}
	}
}

tinydir_dir given_dir(char* path) {
	tinydir_dir dir;
	tinydir_open(dir, path);
	return dir;
}

tinydir_dir current_dir() {
	char* path = NULL;
	if (!(getcwd(path, 0))) {
		return NULL;
	}
	tinydir_dir dir;
	tinydir_open_sorted(&dir, path);
	return dir;
}

Directory */
