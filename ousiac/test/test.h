#include <cmocka.h>

int main (int argc, char **argv) {
  const struct CMUnitTest tests[] = {};
  return cmocka_run_group_tests(tests, NULL, NULL);
}
