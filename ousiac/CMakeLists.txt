cmake_minimum_required (VERSION 3.4.3)
project (ousiac)
set (C_STANDARD 99)

file (GLOB_RECURSE SOURCES "src/*.*" "include/*.h")

include_directories ("include/")

add_executable (ousiac ${SOURCES})

target_link_libraries (ousiac curl)
