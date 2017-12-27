#ifndef STACK_H_
#define STACK_H_

#include <stdbool.h>

#define STACK_INIT_SIZE 8
#define STACK_GROWTH_CONSTANT 2
#ifndef STACK_TYPE
#define STACK_TYPE int
#endif

typedef struct stack stack;

stack* stack_init(void);
size_t stack_size(stack* s);
bool stack_push(stack* s, STACK_TYPE x);
STACK_TYPE stack_top(stack* s);
STACK_TYPE stack_pop(stack* s);
void stack_kill(stack* s);

#endif
