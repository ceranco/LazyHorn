project(LazyHorn)
cmake_minimum_required(VERSION 3.15.0)

if (CMAKE_SOURCE_DIR STREQUAL CMAKE_BINARY_DIR ) 
  message (FATAL_ERROR
    "In-source builds are not allowed. Please clean your source tree and try again.")  
endif()

# Add path for custom modules
set(CMAKE_MODULE_PATH
  ${CMAKE_MODULE_PATH}
  "${CMAKE_CURRENT_SOURCE_DIR}/cmake"
  )

set(CMAKE_CXX_STANDARD 14 CACHE STRING "C++ standard to conform to")
add_definitions(-D__STDC_FORMAT_MACROS -D__STDC_LIMIT_MACROS)
#add_definitions ("-std=c++17")

option(IH_STATIC_EXE "Static executables." OFF)

# put static libraries first
set(CMAKE_FIND_LIBRARY_SUFFIXES ".a" ${CMAKE_FIND_LIBRARY_SUFFIXES})

set (CUSTOM_BOOST_ROOT "/home/omer.r" CACHE PATH "Path to custom boost installation.")
if (CUSTOM_BOOST_ROOT)
  set (BOOST_ROOT ${CUSTOM_BOOST_ROOT})
  set (Boost_NO_SYSTEM_PATHS "ON")
endif()

set(Boost_USE_STATIC_LIBS ${IH_STATIC_EXE})
find_package(Boost 1.77 REQUIRED COMPONENTS program_options)
if (Boost_FOUND)
  include_directories (${Boost_INCLUDE_DIRS})
endif ()

# prefer linking with static libraries
set(CMAKE_FIND_LIBRARY_SUFFIXES ".a" ${CMAKE_FIND_LIBRARY_SUFFIXES})

# check for rt lib. Not needed on OSX.
find_library(RT_LIB NAMES rt)
if (NOT RT_LIB)
  set(RT_LIB "")
endif()
mark_as_advanced(RT_LIB)

find_package(Z3 4.8.12)
if (NOT Z3_FOUND)
  message(Error "No Z3 found.")
else()
  include_directories(${Z3_INCLUDE_DIR})
  message ("Found Z3 at ${Z3_EXECUTABLE}")
  # indicate that we want z3 binary to be included in the binary distribution
  install (PROGRAMS ${Z3_EXECUTABLE} DESTINATION bin)
endif()

add_subdirectory(src)
