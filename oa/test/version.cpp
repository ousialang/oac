#include "catch.hpp"
#include "version.hpp"

TEST_CASE("'version_build' has been replaced with a random alphanumeric string.", "[build]") {
	REQUIRE(version_build[0] != '@');
	REQUIRE(version_tags[0] != '@');
}

// TODO
TEST_CASE("The 'version' command works as intented.") {
}
