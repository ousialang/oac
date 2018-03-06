#include <cstdio>
#include <cstdlib>
#include <string>
#include <getopt.h>
#include <curl/curl.h>
#include <sysexits.h>
#include "install.hpp"
/*
static const std::string git_default_branch_name = "master";
static const std::string github_zipball_url
        = "https://github.com/%s/%s/archive/%s.zip";
static const std::string gitlab_zipball_url
        = "https://gitlab.org/%s/%s/repository/archive.zip?ref=%s";
#define URL_BITBUCKET_ZIPBALL "https://bitbucket.org/%s/%s/get/%s.zip"
#define URL_NOTABUG_ZIPBALL "https://notabug.org/%s/%s/archive/%s.zip"
#define URL_SOURCEFORGE_ZIPBALL                                                \
	"https://downloads.sourceforge.net/project/%s/%s/%s/%s-%s.zip"
#define PARAM_NUM_VERSION 1
#define PARAM_NUM_BRANCH 2

struct parameter {
	char opt;
	char* arg;
};
int install_main(int argc, char* argv[]) {
	static struct option options[] = { { "version", required_argument, 0, 'v' },
		                               { "branch", required_argument, 0, 'b' },
		                               { 0, 0, 0, 0 } };
	const std::string options_synopsis = "v:b:";
	int argv_current_index = 0;
	int opt;
	struct parameter params[argc];
	while (opt = getopt_long(argc, argv, options_synopsis, options,
	                         &argv_current_index),
	       opt != -1) {
		params[i] = (struct parameter){ opt, optarg };
		i++;
	}
	return EX_OK;
}

char* url_github(char* user, char* repo, char* version) {
	if (!version) {
		version = malloc(strlen(GIT_DEFAULT_BRANCH));
		strcpy(version, GIT_DEFAULT_BRANCH);
	}
	size_t url_size = (+strlen(URL_GITHUB_ZIPBALL) + strlen(user) + strlen(repo)
	                   + strlen(version) - 6 // 3 * strlen("%s")
	                   + 1 // '\0'
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

char* url_sourceforge(char* sourceforge, char* version) {}*/
