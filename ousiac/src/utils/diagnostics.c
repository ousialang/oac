#include <stdio.h>
#include <stdlib.h>

#ifdef __unix__
  #include <sys/param.h>
#endif

#define BITS_PER_BYTE 8
#define CMD_SW_VERS "sw_vers"
#define CMD_SW_VERS_PRODUCT_NAME "sw_vers -productName"
#define CMD_SW_VERS_PRODUCT_VERSION "sw_vers -productVersion"
#define CMD_SW_VERS_BUILD_VERSION "sw_vers -buildVersion"
#define CMD_LSB_RELEASE "lsb_release -a"
#define REPORT_KEY_COMPILER "COMPILER"
#define REPORT_KEY_OS "OS"
#define REPORT_KEY_OS_VERSION "OS_VERSION"
#define REPORT_KEY_ARCH_BITS "ARCH_BITS"
#define REPORT_FILENAME "ousia-env-report"
#define PLATFORM_NAME_WINDOWS "Windows"
#define PLATFORM_NAME_GNU_LINUX "GNU/Linux"
#define PLATFORM_NAME_LINUX "Linux"
#define PLATFORM_NAME_IPHONE_SIMULATOR "iPhone simulator"
#define PLATFORM_NAME_IPHONE "iPhone"
#define PLATFORM_NAME_MAC "Mac"
#define PLATFORM_NAME_APPLE "Apple-made"
#define PLATFORM_NAME_FREEBSD "FreeBSD"
#define PLATFORM_NAME_DRAGONFLY "DragonFly BSD"
#define PLATFORM_NAME_NETBSD "NetBSD"
#define PLATFORM_NAME_OPENBSD "OpenBSD"
#define PLATFORM_NAME_HPUX "HP-UX"
#define PLATFORM_NAME_AIX "IBM AIX"
#define PLATFORM_NAME_SOLARIS "Solaris"
#define PLATFORM_NAME_UNIX "Unix"
#define PLATFORM_NAME_UNKNOWN "?"

#if defined _WIN32 || defined _WIN64 || defined __CYGWIN__
  #define PLATFORM_NAME PLATFORM_NAME_WINDOWS
#elif defined __gnu_linux
  //  I'd just like to interject for a moment. What you’re referring to as
  // Linux, is in fact, GNU/Linux, or as I’ve recently taken to calling it, GNU
  // plus Linux. Linux is not an operating system unto itself, but rather
  // another free component of a fully functioning GNU system made useful by the
  // GNU corelibs, shell utilities and vital system components comprising a full
  // OS as defined by POSIX.
  //  Many computer users run a modified version of the GNU system every day,
  // without realizing it. Through a peculiar turn of events, the version of GNU
  // which is widely used today is often called “Linux”, and many of its users
  // are not aware that it is basically the GNU system, developed by the GNU
  // Project. There really is a Linux, and these people are using it, but it is
  // just a part of the system they use.
  //  Linux is the kernel: the program in the system that allocates the
  // machine’s resources to the other programs that you run. The kernel is an
  // essential part of an operating system, but useless by itself; it can only
  // function in the context of a complete operating system. Linux is normally
  // used in combination with the GNU operating system: the whole system is
  // basically GNU with Linux added, or GNU/Linux. All the so-called “Linux”
  // distributions are really distributions of GNU/Linux.
  #define PLATFORM_NAME PLATFORM_NAME_GNU_LINUX
#elif defined __linux
  #define PLATFORM_NAME PLATFORM_NAME_LINUX
#elif defined __APPLE__ && defined __MACH__
  #include <TargetConditionals.h>
  #if TARGET_IPHONE_SIMULATOR == 1
    #define PLATFORM_NAME PLATFORM_NAME_IPHONE_SIMULATOR
  #elif TARGET_OS_IPHONE
    #define PLATFORM_NAME PLATFORM_NAME_IPHONE
  #elif TARGET_OS_MAC
    #define PLATFORM_NAME PLATFORM_NAME_MAC
  #else
    #define PLATFORM_NAME PLATFORM_NAME_APPLE
  #endif
#elif defined BSD
  #ifdef __FreeBSD__
    #define PLATFORM_NAME PLATFORM_NAME_FREEBSD
  #elif defined __DragonFly__
    #define PLATFORM_NAME PLATFORM_NAME_DRAGONFLY
  #elif defined __NetBSD__
    #define PLATFORM_NAME PLATFORM_NAME_NETBSD
  #elif defined __OpenBSD__
    #define PLATFORM_NAME PLATFORM_NAME_OPENBSD
  #else
    #define PLATFORM_NAME PLATFORM_NAME_BSD
  #endif
#elif defined __hpux
  #define PLATFORM_NAME PLATFORM_NAME_HPUX
#elif defined _AIX
  #define PLATFORM_NAME PLATFORM_NAME_AIX
#elif defined __sun && defined __SVR4
  #define PLATFORM_NAME PLATFORM_NAME_SOLARIS
#elif defined unix
  #define PLATFORM_NAME PLATFORM_NAME_UNIX
#else
  #define PLATFORM_NAME PLATFORM_NAME_UNKNOWN
#endif

char* read_popen_into_string (const char *);
int strcmp (const char *, const char *);

char* read_cmd_into_str(const char *command) {
  FILE *fstream = popen(command, "r");
  size_t size;
  char *buffer;
  if (fstream) {
    fseek(fstream, 0, SEEK_END);
    size = ftell(fstream);
    rewind(fstream);
    buffer = malloc(sizeof(char) * (size + 1));
    fread(buffer, sizeof(char), size, fstream);
    buffer[size] = '\0';
    pclose(fstream);
  }
  return buffer;
}

uint8_t diagnostics_arch_bits(void) {
  return sizeof(void*) * BITS_PER_BYTE;
}

int create_report() {
  FILE *file = fopen("report.txt", "wa");
  if (!file) {
    return 1;
  }
  if (strcmp(PLATFORM_NAME, PLATFORM_NAME_MAC) == 0) {
    fprintf(file, "%s: %s", REPORT_KEY_OS, read_cmd_into_str(CMD_SW_VERS_PRODUCT_NAME));
    char *product_version = read_cmd_into_str(CMD_SW_VERS_PRODUCT_VERSION);
    size_t product_version_size = sizeof(product_version) / sizeof(product_version[0]);
    product_version[product_version_size-1] = '\0';
    fprintf(file, "%s: %s %s", REPORT_KEY_OS_VERSION, product_version, read_cmd_into_str(CMD_SW_VERS_BUILD_VERSION));
  } else {
    fprintf(file, "%s: %s\n", REPORT_KEY_OS, PLATFORM_NAME);
  }
  #ifdef __VERSION__
    fprintf(file, "%s: %s\n", REPORT_KEY_COMPILER, __VERSION__);
  #endif
  fprintf(file, "%s: %d\n", REPORT_KEY_ARCH_BITS, diagnostics_arch_bits());
  fclose(file);
  return 0;
}
