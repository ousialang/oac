#ifndef DIAGNOSTICS_H_
#define DIAGNOSTICS_H_

#if _WIN32 || _WIN64 || __CYGWIN__
#define PLATFORM_IS_WINDOWS
#define PLATFORM_NAME "Windows"
#elif __linux
#define PLATFORM_IS_LINUX
#define PLATFORM_NAME "Linux"
#if __gnu || __gnu_linux
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
#endif
#elif __APPLE__ && __MACH__
#include <TargetConditionals.h>
#if TARGET_IPHONE_SIMULATOR == 1
#define PLATFORM_IS_IPHONE_SIMULATOR
#define PLATFORM_NAME "iPhone simulator"
#elif TARGET_OS_IPHONE
#define PLATFORM_IS_IPHONE
#define PLATFORM_NAME "iPhone"
#elif TARGET_OS_MAC
#define PLATFORM_IS_MAC
#define PLATFORM_NAME "Mac"
#else
#define PLATFORM_NAME "Apple-made"
#endif
#define PLATFORM_IS_APPLE
#elif BSD
#if __FreeBSD__
#define PLATFORM_IS_FREEBSD
#define PLATFORM_NAME "FreeBSD"
#elif __DragonFly__
#define PLATFORM_IS_DRAGONFLY
#define PLATFORM_NAME "DragonFly BSD"
#elif __NetBSD__
#define PLATFORM_IS_NETBSD
#define PLATFORM_NAME "NetBSD"
#elif __OpenBSD__
#define PLATFORM_IS_OPENBSD
#define PLATFORM_NAME "OpenBSD"
#else
#define PLATFORM_NAME "BSD"
#endif
#define PLATFORM_IS_BSD
#elif __hpux
#define PLATFORM_IS_HPUX
#define PLATFORM_NAME "HP-UX"
#elif _AIX
#define PLATFORM_IS_AIX
#define PLATFORM_NAME "IBM AIX"
#elif __sun && __SVR4
#define PLATFORM_IS_SOLARIS
#define PLATFORM_NAME "Solaris"
#elif unix
#define PLATFORM_NAME "Unix"
#else
#define PLATFORM_IS_UNKNOWN
#define PLATFORM_NAME "Unknown OS"
#endif

#ifdef unix
#define PLATFORM_IS_UNIX
#endif

#if __amd64__ || __x86_64__ || _M_X64
#define ARCH_IS_AMD64
#define ARCH_NAME "AMD64"
#elif __i386 || _M_IX86
#define ARCH_IS_I386
#define ARCH_NAME "i386"
#elif __ia64 || __itanium__ || _M_IA64
#define ARCH_IS_ITANIUM
#define ARCH_NAME "Itanium"
#else
#define ARCH_IS_UNKNOWN
#define ARCH_NAME "Unknown CPU"
#endif

#endif
