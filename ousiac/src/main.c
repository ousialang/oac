#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <getopt.h>
#include "main.h"
#include "utils/diagnostics.h"
#include "install.h"

int main (int argc, char *argv[]) {
  //create_report();
  subcmd_install(argc, argv);
}
