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
		URL_MD5 ${URL_MD5_SETTING}
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

set (C_STANDARD 99)
set (CMAKE_CXX_STANDARD 17)
set (BUILD_TESTING ON)
set (CMAKE_MODULE_PATH "${CMAKE_SOURCE_DIR}/CMake")

# logc
set (LOGC_HEADER_URL "https://raw.githubusercontent.com/rxi/log.c/b7414f3468d2fea25c9039d05822e5053e95e885/src/log.h")
set (LOGC_SOURCE_URL "https://raw.githubusercontent.com/rxi/log.c/b7414f3468d2fea25c9039d05822e5053e95e885/src/log.c")
set (LOGC_HEADER_DIR "${CMAKE_BINARY_DIR}/logc")
set (LOGC_SOURCE_DIR ${CMAKE_BINARY_DIR})
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
set (CATCH_DIR "${CMAKE_BINARY_DIR}/catch")
add_target_from_url (catch ${CATCH_URL} ${CATCH_DIR})
include_directories (${CATCH_DIR})

# Update submodules
# =================
add_custom_target (
	update_submodules
	COMMAND git submodule init
	COMMAND git submodule update
	WORKING_DIRECTORY ${PROJECT_SOURCE_DIR} )

# Tests
# =====
#file (GLOB_RECURSE TESTS "test/*.*")
#add_executable (tests ${TESTS})

#enable_testing ()
#add_test (ousiac_tests tests)
