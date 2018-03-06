#ifndef DIAGNOSTICS_H_
#define DIAGNOSTICS_H_

#include <string>

#if _WIN32 || _WIN64 || __CYGWIN__
#define PLATFORM_IS_WINDOWS
static const std::string platform_name = "Windows";
#elif __linux
#define PLATFORM_IS_LINUX
#define PLATFORM_IS_NIX
static const std::string platform_name = "Linux";
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
static const std::string platform_name = "iPhone simulator";
#elif TARGET_OS_IPHONE
#define PLATFORM_IS_IPHONE
static const std::string platform_name = "iPhone";
#elif TARGET_OS_MAC
#define PLATFORM_IS_MAC
#define PLATFORM_IS_UNIX
static const std::string platform_name = "Mac";
#else
static const std::string platform_name = "Apple-made";
#endif
#define PLATFORM_IS_APPLE
#elif BSD
#if __FreeBSD__
#define PLATFORM_IS_FREEBSD
static const std::string platform_name = "FreeBSD";
#elif __DragonFly__
#define PLATFORM_IS_DRAGONFLY
static const std::string platform_name = "DragonFly BSD";
#elif __NetBSD__
#define PLATFORM_IS_NETBSD
static const std::string platform_name = "NetBSD";
#elif __OpenBSD__
#define PLATFORM_IS_OPENBSD
static const std::string platform_name = "OpenBSD";
#else
static const std::string platform_name = "BSD";
#endif
#define PLATFORM_IS_BSD
#define PLATFORM_IS_UNIX
#elif __hpux
#define PLATFORM_IS_HPUX
static const std::string platform_name = "HP-UX";
#elif _AIX
#define PLATFORM_IS_AIX
static const std::string platform_name = "IBM AIX";
#elif __sun && __SVR4
#define PLATFORM_IS_SOLARIS
#define PLATFORM_IS_UNIX
static const std::string platform_name = "Solaris";
#elif unix
static const std::string platform_name = "Unix";
#else
#define PLATFORM_IS_UNKNOWN
static const std::string platform_name = "Unknown OS";
#endif

#ifdef unix
#define PLATFORM_IS_UNIX
#endif

#if __amd64__ || __x86_64__ || _M_X64
#define ARCH_IS_AMD64
static const std::string arch_name = "AMD64";
#elif __i386 || _M_IX86
#define ARCH_IS_I386
static const std::string platform_name = "i386";
#elif __ia64 || __itanium__ || _M_IA64
#define ARCH_IS_ITANIUM
static const std::string platform_name = "Itanium";
#else
#define ARCH_IS_UNKNOWN
static const std::string platform_name = "Unknown CPU";
#endif

#endif
