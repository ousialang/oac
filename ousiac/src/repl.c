#include <stdio.h>

#define PROMPT_STRING "> "

int prompt(char *);

void repl(void) {
  char buffer[256];
  prompt:
    prompt(buffer);
  goto prompt;
}

int prompt(char *buffer) {
  char c = getchar();
  printf("%s", PROMPT_STRING);
  return 0;
}
