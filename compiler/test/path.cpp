#include "catch.hpp"
extern "C" {
#include "utils/path.h"
}

TEST_CASE("File paths shortening works as expected.", "[feedback]") {
	char* s1 = "src/abc/foobar_123/spam/ousia.oa:1337:42";
	char* s2 = "";
	char* s3 = "x";
	char* s4 = "a/b/c/d.oa:1:2";
}
