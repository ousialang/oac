cmake_minimum_required (VERSION 3.4.3)
project (ousia)

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

# Sources
# =======
file (GLOB_RECURSE SOURCES "src/*.*")
file (GLOB_RECURSE HEADERS "include/*.h")
include_directories ("include/")

# catch2
# ======
add_library (catch2 INTERFACE)
target_include_directories (catch2 INTERFACE "lib/catch2/")

# Update submodules
# =================
add_custom_target (
	update_submodules
	COMMAND git submodule init
	COMMAND git submodule update
	WORKING_DIRECTORY ${PROJECT_SOURCE_DIR} )

# Tests
# =====
file (GLOB_RECURSE TESTS "test/*.*")
add_executable (tests ${TESTS})
target_link_libraries (tests catch2)

# Building and linking
# ====================
add_executable (ousiac ${HEADERS} ${SOURCES})
target_link_libraries (ousiac curl)

enable_testing ()
add_test (ousiac_tests tests)
