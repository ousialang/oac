#include "install.h"
#include <curl/curl.h>
#include <getopt.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define GIT_DEFAULT_BRANCH "master"
#define URL_GITHUB_ZIPBALL "https://github.com/%s/%s/archive/%s.zip"
#define URL_GITLAB_ZIPBALL "https://gitlab.org/%s/%s/repository/archive.zip?ref=%s"
#define URL_BITBUCKET_ZIPBALL "https://bitbucket.org/%s/%s/get/%s.zip"
#define URL_NOTABUG_ZIPBALL "https://notabug.org/%s/%s/archive/%s.zip"
#define URL_SOURCEFORGE_ZIPBALL "https://downloads.sourceforge.net/proejct/%s/%s/%s/%s-%s.zip"
#define PARAM_NUM_VERSION 1
#define PARAM_NUM_BRANCH 2

struct parameter {
	char opt;
	char* arg;
};

int subcmd_install(int argc, char* argv[]) {
	static struct option options[] = {
	    {"version", required_argument, 0, 'v'}, {"branch", required_argument, 0, 'b'}, {0, 0, 0, 0},
	};
	int i = 0;
	int opt;
	struct parameter params[argc];
	while (opt = getopt_long(argc, argv, "v:b:", options, NULL), opt != -1) {
		params[i] = (struct parameter){opt, optarg};
		i++;
	}
	// if (strcmp(subcmd, "github") == 0) {
	//  printf("%s", url_github("neysofu", "ousia", NULL));
	//}
	return 0;
}

char* url_github(char* user, char* repo, char* version) {
	if (!version) {
		version = malloc(strlen(GIT_DEFAULT_BRANCH));
		strcpy(version, GIT_DEFAULT_BRANCH);
	}
	size_t url_size = (+strlen(URL_GITHUB_ZIPBALL) + strlen(user) + strlen(repo) + strlen(version)
	                   - 6  // 3 * strlen("%s")
	                   + 1  // '\0'
	);
	char* url = malloc(url_size);
	snprintf(url, url_size, URL_GITHUB_ZIPBALL, user, repo, version);
	free(version);
	return url;
}

char* url_gitlab(char* user, char* repo, char* version) {
	// printf("https://gitlab.org/%s/%s");
}

char* url_bitbucket(char* user, char* repo, char* version) {
	// printf("https://bitbucket.org/%s/%s/src");
}

char* url_sourceforge(char* sourceforge, char* version) {
}
