#include <cstdio>
#include "catch.hpp"
extern "C" {
#include "tree.h"
}

using namespace std;

TEST_CASE("Tree operations work as expected.", "[tree][AST][parser]") {
	tree* t = tree_init(123);
	REQUIRE(t);
	SECTION("A newly created tree is a leaf.") { REQUIRE(tree_is_leaf(t)); }
	SECTION("A newly created tree is a root.") { REQUIRE(tree_is_root(t)); }
	SECTION("A newly created tree is orphan, child-free and an only-child.") {
		REQUIRE(!t->parent);
		REQUIRE(tree_count_children(t) == 0);
		REQUIRE(tree_count_siblings(t) == 0);
	}
	SECTION("The common ancestor of two identical trees is also identical.") {
		// TODO: REQUIRE(tree_common_ancestor(t, t) == t);
	}
}
