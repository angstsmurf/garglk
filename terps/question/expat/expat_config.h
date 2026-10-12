/* Hand-written configuration for the copy of Expat bundled with Question,
 * used only when no system Expat is found (see terps/CMakeLists.txt, which
 * also defines BYTEORDER). */
#ifndef EXPAT_CONFIG_H
#define EXPAT_CONFIG_H 1

#define XML_CONTEXT_BYTES 1024
#define XML_DTD 1
#define XML_GE 1
#define XML_NS 1

#if !defined(_WIN32)
/* Windows uses rand_s(); everywhere else read /dev/urandom. */
#define XML_DEV_URANDOM 1
#endif

#ifdef _MSC_VER
#define __func__ __FUNCTION__
#endif

#endif
