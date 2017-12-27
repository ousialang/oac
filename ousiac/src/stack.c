#include "log.h"

struct stack_batch {
struct stack_batch* pprev;
STACK_TYPE data[];
}

typedef struct {
size_t head_size;
size_t head_capacity;
struct stack_batch* phead;
} stack;

struct stack_batch* stack_batch_init(size_t capacity, struct stack_batch* pprev) {
  struct stack_batch* sb = malloc(
      sizeof(struct stack_batch)+capacity*sizeof(STACK_TYPE));
  sb->pprev = pprev;
}

stack* stack_init(void) {
  struct stack_batch* phead = stack_batch_init(STACK_INIT_SIZE, NULL);
  stack* s = malloc(sizeof(stack));
  if (!s) { return NULL; }
  s->head_size = 0;
  s->head_capacity = STACK_INIT_SIZE;
  s->phead = phead;
  return s;
}

bool stack_is_empty(stack* s) {
  return !(s->phead->pprev || s->phead_size);
}

bool stack_push(stack* s, stack_type x) {
  s->phead->data[(s->head_size)++] = x;
  return x;
}

STACK_TYPE stack_pop(stack* s) {
  if (s->head_size == 0) {
    s->head_capacity /= STACK_GROWTH_CONSTANT;
    s->head_size = head_capacity;
    s->phead = s->phead->pprev;
  }
  return s->phead->data[--(s->head_size)];
}

void stack_kill(stack* s) {
  struct stack_batch* phead = s->phead;
  do {
	pprev = phead->pprev;
	free(phead);
	phead = pprev;
  } while (phead);
  free(s);
}
