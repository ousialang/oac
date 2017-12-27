#include <stdlib.h>
#include "log.h"
#include "stack.h"

struct stack_batch {
	struct stack_batch* pprev;
	STACK_TYPE data[];
};

struct stack {
	size_t head_size;
	size_t head_capacity;
	struct stack_batch* phead;
};

struct stack_batch* stack_batch_init(size_t capacity, struct stack_batch* pprev) {
	log_trace("Initialize a new stack batch of size %i.", capacity);
	struct stack_batch* sb = malloc(sizeof(struct stack_batch) + capacity * sizeof(STACK_TYPE));
	sb->pprev = pprev;
	log_trace("The stack batch is at %p.", sb);
	return sb;
}

stack* stack_init(void) {
	log_trace("Initialize a new stack.");
	struct stack_batch* phead = stack_batch_init(STACK_INIT_SIZE, NULL);
	stack* s = malloc(sizeof(stack));
	log_trace("The stack is at %p.", s);
	if (!s) {
		return NULL;
	}
	s->head_size = 0;
	s->head_capacity = STACK_INIT_SIZE;
	s->phead = phead;
	return s;
}

size_t stack_size(stack* s) {
	log_trace("Calculate the stack's size.");
	return (STACK_GROWTH_CONSTANT - 1) * s->head_capacity - STACK_INIT_SIZE + s->head_size;
}

bool stack_push(stack* s, STACK_TYPE x) {
	log_trace("Push an element into the stack at %p.", s);
	if (s->head_size == s->head_capacity) {
		size_t capacity = s->head_capacity * STACK_GROWTH_CONSTANT;
		struct stack_batch* sb = stack_batch_init(capacity, s->phead);
		if (!sb) {
			return 0;
		}
		s->phead = sb;
		s->head_size = 0;
		s->head_capacity = capacity;
	}
	s->phead->data[(s->head_size)++] = x;
	return 1;
}

STACK_TYPE stack_top(stack* s) {
	if (s->head_size == 0) {
		return s->phead->pprev->data[s->head_capacity / STACK_GROWTH_CONSTANT - 1];
	} else {
		return s->phead->data[s->head_size - 1];
	}
}

STACK_TYPE stack_pop(stack* s) {
	log_trace("Pop an element off the stack at %p.", s);
	if (s->head_size == 0) {
		struct stack_batch* pprev = s->phead->pprev;
		free(s->phead);
		s->head_capacity /= STACK_GROWTH_CONSTANT;
		s->head_size = s->head_capacity;
		s->phead = pprev;
	}
	return s->phead->data[--(s->head_size)];
}

void stack_kill(stack* s) {
	log_trace("Kill 'em with kindness (stack is at %p).", s);
	struct stack_batch* phead = s->phead;
	do {
		log_trace("Free the stack batch at %p.", phead);
		struct stack_batch* pprev = phead->pprev;
		free(phead);
		phead = pprev;
	} while (phead);
	free(s);
}
