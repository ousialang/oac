cmake_minimum_required (VERSION 3.4.3)
project (ousia)

include (ExternalProject)

function (add_target_from_url TARGET URL DIR)
	if (${ARG4})
		set (URL_MD5_SETTING URL_MD5 ${ARG4})
	else ()
		set (URL_MD5_SETTING)
	endif ()
	ExternalProject_Add (
		${TARGET}
		URL ${URL}
		${URL_MD5_SETTING}
		DOWNLOAD_DIR ${DIR}
		DOWNLOAD_NO_PROGRESS 1
		DOWNLOAD_NO_EXTRACT 1
		CONFIGURE_COMMAND ""
		BUILD_COMMAND ""
		INSTALL_COMMAND "" )
endfunction ()

set (VERSION_MAJOR 0)
set (VERSION_MINOR 1)
set (VERSION_PATCH 0)
string (RANDOM LENGTH 8 VERSION_BUILD)

set (C_STANDARD 99)
set (CMAKE_CXX_STANDARD 17)
set (BUILD_TESTING ON)
set (CMAKE_MODULE_PATH "${CMAKE_CURRENT_SOURCE_DIR}/CMake")

# logc
set (LOGC_HEADER_URL "https://raw.githubusercontent.com/rxi/log.c/b7414f3468d2fea25c9039d05822e5053e95e885/src/log.h")
set (LOGC_SOURCE_URL "https://raw.githubusercontent.com/rxi/log.c/b7414f3468d2fea25c9039d05822e5053e95e885/src/log.c")
set (LOGC_HEADER_DIR "${CMAKE_CURRENT_BINARY_DIR}/logc")
set (LOGC_SOURCE_DIR ${CMAKE_CURRENT_BINARY_DIR})
set (LOGC_HEADER "${LOGC_HEADER_DIR}/log.h")
set (LOGC_SOURCE "${LOGC_SOURCE_DIR}/log.c")
add_target_from_url (logc_header ${LOGC_HEADER_URL} ${LOGC_HEADER_DIR})
add_target_from_url (logc_source ${LOGC_SOURCE_URL} ${LOGC_SOURCE_DIR})
set_source_files_properties (
	${LOGC_HEADER} ${LOGC_SOURCE}
	PROPERTIES GENERATED 1 )
add_library (logc ${LOGC_SOURCE})
add_dependencies (logc logc_header logc_source)
include_directories (${LOGC_HEADER_DIR})

# catch
set (CATCH_URL "https://raw.githubusercontent.com/catchorg/Catch2/v2.0.1/single_include/catch.hpp")
set (CATCH_DIR "${CMAKE_CURRENT_BINARY_DIR}/catch")
add_target_from_url (catch ${CATCH_URL} ${CATCH_DIR})
include_directories (${CATCH_DIR})

# tinydir
ExternalProject_Add (
	tinydir
	URL "https://github.com/cxong/tinydir/archive/1.2.3.tar.gz"
	URL_MD5 "ed4bf9f73e385dbb00f7d5ce5b944785"
	DOWNLOAD_NO_PROGRESS 1
	CONFIGURE_COMMAND ""
	BUILD_COMMAND ""
	INSTALL_COMMAND "" )
ExternalProject_Get_Property (tinydir SOURCE_DIR)
include_directories (${SOURCE_DIR})

# FlatBuffers
ExternalProject_Add (
	flatbuf
	URL "https://github.com/google/flatbuffers/archive/v1.8.0.tar.gz"
	URL_MD5 "276cab8303c4189cbe3b8a70e0515d65"
	DOWNLOAD_NO_PROGRESS 1
	INSTALL_COMMAND ""
	CMAKE_ARGS -DCMAKE_BUILD_TYPE=${CMAKE_BUILD_TYPE} )
ExternalProject_Get_Property (flatbuf BINARY_DIR)
ExternalProject_Get_Property (flatbuf SOURCE_DIR)
set (FLATC "${BINARY_DIR}/${CMAKE_CFG_INTDIR}/flatc")
include_directories ("${SOURCE_DIR}/include")

# FlatBuffers schemas generation
set (FLATBUF_SCHEMAS_DIR "${CMAKE_CURRENT_BINARY_DIR}/schemas")
file (MAKE_DIRECTORY ${FLATBUF_SCHEMAS_DIR})
add_custom_target (
	flatbuf_schemas_gen
	DEPENDS flatbuf
	COMMAND ${FLATC} --cpp "${CMAKE_CURRENT_SOURCE_DIR}/src/schemas/tree.fbs"
	WORKING_DIRECTORY ${FLATBUF_SCHEMAS_DIR} )
include_directories (${FLATBUF_SCHEMAS_DIR})

# Source
set (INCLUDES_DIR "${CMAKE_CURRENT_SOURCE_DIR}/include")
include_directories (${INCLUDES_DIR})
file (GLOB_RECURSE SOURCES "src/*.c" "src/*.cpp")
add_library (ousiac_lib ${SOURCES})
target_link_libraries (ousiac_lib logc)
add_dependencies (ousiac_lib flatbuf_schemas_gen)
add_executable (ousiac ${SOURCES})
target_link_libraries (ousiac ousiac_lib)
set (VERSION_H_IN "${CMAKE_CURRENT_SOURCE_DIR}/include/cmd/version.h.in")
set (VERSION_H "${CMAKE_CURRENT_BINARY_DIR}/include/cmd/version.h")
configure_file ("${VERSION_H_IN}" ${VERSION_H})
include_directories ("${CMAKE_CURRENT_BINARY_DIR}/include")

# Tests
enable_testing ()
file (GLOB_RECURSE TESTS "test/*.*")
add_executable (ousiac_tests ${TESTS})
target_link_libraries (ousiac_tests logc ousiac_lib)
add_dependencies (ousiac_tests catch)
add_test (ousiac_tests ousiac_tests)
