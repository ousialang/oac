cmake_minimum_required (VERSION 3.4.3)
project (zenzi CXX)

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
set (VERSION_TAGS "")

set (C_STANDARD 99)
set (CMAKE_CXX_STANDARD 17)
set (BUILD_TESTING ON)
set (CMAKE_MODULE_PATH "${CMAKE_CURRENT_SOURCE_DIR}/CMake")

# Boost
set (Boost_USE_STATIC_LIBS ON)
set (Boost_USE_MULTITHREADED ON)
set (Boost_USE_STATIC_RUNTIME OFF)
find_package (Boost 1.45.0 COMPONENTS filesystem thread)
if (Boost_FOUND)
    include_directories (${Boost_INCLUDE_DIRS})
else ()
	message (FATAL_ERROR "Boost components not found.")
endif()

# catch
set (CATCH_URL "https://raw.githubusercontent.com/catchorg/Catch2/v2.0.1/single_include/catch.hpp")
set (CATCH_DIR "${CMAKE_CURRENT_BINARY_DIR}/catch")
set (CATCH_MD5 "9b3d2cb5c0f9532cddfbbfd0a622f0af")
add_target_from_url (catch ${CATCH_URL} ${CATCH_DIR} ${CATCH_MD5})
include_directories (${CATCH_DIR})

# flatc
ExternalProject_Add (
	flatc
	URL "https://github.com/google/flatbuffers/archive/v1.8.0.tar.gz"
	URL_MD5 "276cab8303c4189cbe3b8a70e0515d65"
	DOWNLOAD_NO_PROGRESS 1
	INSTALL_COMMAND ""
	CMAKE_ARGS -DCMAKE_BUILD_TYPE=${CMAKE_BUILD_TYPE} )
ExternalProject_Get_Property (flatc BINARY_DIR)
ExternalProject_Get_Property (flatc SOURCE_DIR)
set (FLATC "${BINARY_DIR}/${CMAKE_CFG_INTDIR}/flatc")
include_directories ("${SOURCE_DIR}/include")

# FlatBuffers schemas generation
set (FLATBUF_SCHEMAS_DIR "${CMAKE_CURRENT_BINARY_DIR}/schemas")
file (MAKE_DIRECTORY ${FLATBUF_SCHEMAS_DIR})
add_custom_target (
	flatbuf_schemas_gen
	DEPENDS flatc
	COMMAND ${FLATC} --cpp "${CMAKE_CURRENT_SOURCE_DIR}/src/schemas/tree.fbs"
	WORKING_DIRECTORY ${FLATBUF_SCHEMAS_DIR} )
include_directories (${FLATBUF_SCHEMAS_DIR})

# Source
set (INCLUDES_DIR "${CMAKE_CURRENT_SOURCE_DIR}/include")
include_directories (${INCLUDES_DIR})
file (GLOB_RECURSE SOURCES "src/*.c" "src/*.cpp")
add_library (zenzic_lib ${SOURCES})
add_dependencies (zenzic_lib flatbuf_schemas_gen)
add_executable (zenzic ${SOURCES})
target_link_libraries (zenzic zenzic_lib)
set (VERSION_H_IN "${CMAKE_CURRENT_SOURCE_DIR}/include/version.hpp.in")
set (VERSION_H "${CMAKE_CURRENT_BINARY_DIR}/include/version.hpp")
configure_file ("${VERSION_H_IN}" ${VERSION_H})
include_directories ("${CMAKE_CURRENT_BINARY_DIR}/include")
target_link_libraries (zenzic ${Boost_LIBRARIES})

# Tests
enable_testing ()
file (GLOB_RECURSE TESTS "test/*.*")
add_executable (zenzic_tests ${TESTS})
add_dependencies (zenzic_tests catch)
add_test (zenzic_tests zenzic_tests)
