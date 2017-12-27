#ifndef STACK_H_
#define STACK_H_

#define STACK_INIT_SIZE 8
#define STACK_GROWTH_CONSTANT 2
#ifndef STACK_TYPE
#define STACK_TYPE int
#endif

typedef struct stack stack;

bool stack_is_empty(stack*);
stack* stack_init(void);
bool stack_push(stack* STACK_TYPE);
STACK_TYPE stack_top(stack*);
STACK_TYPE stack_pop(stack*);
void stack_kill(stack*);
