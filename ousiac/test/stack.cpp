#include "catch.hpp"
extern "C" {
#include "log.h"
#include "stack.h"
}

#define NUM_TRIALS 100

TEST_CASE("Stack operations work as expected.", "[stack]") {
	stack* s = stack_init();
	REQUIRE(s);
	SECTION("A newly created stack has no elements in it.") {
		REQUIRE(stack_size(s) == 0);
	}
	SECTION("Pushing an element into a stack increments its size.") {
		size_t size = stack_size(s);
		stack_push(s, 42);
		REQUIRE(++size == stack_size(s));
	}
	SECTION("Popping a stack decrements its size.") {
		stack_push(s, 1337);
		size_t size = stack_size(s);
		stack_pop(s);
		REQUIRE(--size == stack_size(s));
	}
	SECTION("Fetching the topmost element of a stack has no side effects.") {
		stack_push(s, 123);
		size_t size = stack_size(s);
		stack_top(s);
		REQUIRE(stack_size(s) == size);
	}
	SECTION("Push & pop is idempotent.") {
		stack_push(s, 123);
		size_t size = stack_size(s);
		stack_push(s, 0);
		stack_pop(s);
		REQUIRE(stack_size(s) == size);
		REQUIRE(stack_top(s) == 123);
	}
	SECTION("Killing a big stack doesn't throw errors.") {
		for (int i = 0; i < NUM_TRIALS; i++) {
			stack_push(s, i);
		}
		stack_kill(s);
	}
	SECTION("Pushing, popping, and fetching work even with large stacks.") {
		for (int i = 0; i < NUM_TRIALS; i++) {
			REQUIRE(stack_size(s) == i);
			REQUIRE(stack_push(s, 0));
			REQUIRE(stack_push(s, i));
			REQUIRE(stack_top(s) == i);
			REQUIRE(stack_pop(s) == i);
		}
	}
}
