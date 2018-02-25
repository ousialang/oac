#ifndef DIAGNOSTICS_H_
  #define DIAGNOSTICS_H_

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

  #define ARCH_NAME_AMD64 "AMD64"
  #define ARCH_NAME_I386 "i386"
  #define ARCH_NAME_ARM "ARM"
  #define ARCH_NAME_ITANIUM "Itanium"

  #define NAME_UNKNOWN "?"

  #if _WIN32 || _WIN64 || __CYGWIN__
    #define PLATFORM_IS_WINDOWS
  #elif __gnu_linux
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
    #define PLATFORM_IS_GNU_LINUX
  #elif __linux
    #define PLATFORM_IS_LINUX
  #elif __APPLE__ && __MACH__
    #include <TargetConditionals.h>
    #if TARGET_IPHONE_SIMULATOR == 1
	  #define PLATFORM_IS_IPHONE_SIMULATOR
    #elif TARGET_OS_IPHONE
	  #define PLATFORM_IS_IPHONE
    #elif TARGET_OS_MAC
	  #define PLATFORM_IS_MAC
    #endif
    #define PLATFORM_IS_APPLE
  #elif BSD
    #if __FreeBSD__
	  #define PLATFORM_IS_FREEBSD
    #elif __DragonFly__
	  #define PLATFORM_IS_DRAGONFLY
    #elif __NetBSD__
	  #define PLATFORM_IS_NETBSD
    #elif __OpenBSD__
	  #define PLATFORM_IS_OPENBSD
    #endif
    #define PLATFORM_IS_BSD
  #elif __hpux
    #define PLATFORM_IS_HPUX
  #elif _AIX
    #define PLATFORM_IS_AIX
  #elif __sun && __SVR4
    #define PLATFORM_IS_SOLARIS
  #elif unix
    #define PLATFORM_IS_UNIX
  #else
    #define PLATFORM_IS_UNKNOWN
  #endif

  #if __amd64__ || __x86_64__ || _M_X64
    #define ARCH_IS_AMD64
  #elif __i386 || _M_IX86
    #define ARCH_IS_I386
  #elif __ia64 || __itanium__ || _M_IA64
    #define ARCH_IS_ITANIUM
  #else
    #define ARCH_IS_UNKNOWN
  #endif

#endif
