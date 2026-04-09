cmake_minimum_required(VERSION 3.24)
cmake_policy(SET CMP0135 NEW)

if(MSVC)
  set(CMAKE_CONFIGURATION_TYPES "Debug;Release" CACHE STRING "Available configuration types to select")
endif()

option(GPU "GPU" ON)
if(GPU)
  if(NOT DEFINED CMAKE_CUDA_ARCHITECTURES)
    set(CMAKE_CUDA_ARCHITECTURES native CACHE STRING "Targeted CUDA architectures")
  endif()
  project(lala-interval
    HOMEPAGE_URL "https://github.com/lattice-land/lala-interval"
    LANGUAGES CUDA CXX)
else()
  project(lala-interval
    HOMEPAGE_URL "https://github.com/lattice-land/lala-interval"
    LANGUAGES CXX)
endif()
option(LOCAL_DEPS "LOCAL_DEPS" OFF)
option(LALA_INTERVAL_BUILD_TESTS "LALA_INTERVAL_BUILD_TESTS" OFF)
option(LALA_INTERVAL_BUILD_DOC "LALA_INTERVAL_BUILD_DOC" OFF)

# Dependencies

include(FetchContent)

if(LOCAL_DEPS)
  FetchContent_Declare(cuda_battery SOURCE_DIR "${CMAKE_CURRENT_LIST_DIR}/../cuda-battery/")
else()
  FetchContent_Declare(
    cuda_battery
    GIT_REPOSITORY "https://github.com/lattice-land/cuda-battery.git"
    GIT_TAG        v1.5.8
  )
endif()

FetchContent_MakeAvailable(cuda_battery)

# Preparing the library

add_library(lala_interval INTERFACE)
target_link_libraries(lala_interval INTERFACE cuda_battery)
target_include_directories(lala_interval INTERFACE include)

if(LALA_INTERVAL_BUILD_TESTS)

# Google Test dependency

FetchContent_Declare(
  googletest
  GIT_REPOSITORY https://github.com/google/googletest.git
  GIT_TAG v1.17.0
  GIT_SHALLOW 1
)
# For Windows: Prevent overriding the parent project's compiler/linker settings
set(gtest_force_shared_crt ON CACHE BOOL "" FORCE)
FetchContent_MakeAvailable(googletest)

enable_testing()
include(GoogleTest)

file(GLOB cpu_test_files tests/*_test.cpp)
foreach(file ${cpu_test_files})
  cmake_path(GET file STEM test_name)
  add_executable(${test_name} ${file})
  target_link_libraries(${test_name} lala_interval gtest_main)
  gtest_discover_tests(${test_name})
endforeach()

endif()

if(LALA_INTERVAL_BUILD_DOC)

# Documentation
find_package(Doxygen REQUIRED doxygen)

set(DOXYGEN_PROJECT_NAME "Interval Abstract Domain")
set(DOXYGEN_BUILTIN_STL_SUPPORT YES)
set(DOXYGEN_CASE_SENSE_NAMES NO)
set(DOXYGEN_CLASS_DIAGRAMS NO)
set(DOXYGEN_DISTRIBUTE_GROUP_DOC YES)
set(DOXYGEN_EXTRACT_ALL YES)
set(DOXYGEN_EXTRACT_PRIVATE NO)
set(DOXYGEN_FILE_PATTERNS *.hpp)
set(DOXYGEN_GENERATE_TREEVIEW YES)
set(DOXYGEN_HIDE_IN_BODY_DOCS YES)
set(DOXYGEN_QUIET YES)
set(DOXYGEN_RECURSIVE YES)
set(DOXYGEN_SORT_BY_SCOPE_NAME YES)
set(DOXYGEN_SORT_MEMBER_DOCS NO)
set(DOXYGEN_SOURCE_BROWSER NO)
set(DOXYGEN_STRIP_CODE_COMMENTS NO)
set(DOXYGEN_USE_MATHJAX YES)
set(DOXYGEN_EXTRA_PACKAGES stmaryrd)
set(DOXYGEN_EXCLUDE_SYMBOLS = impl)
set(DOXYGEN_ENABLE_PREPROCESSING YES)
set(DOXYGEN_PREDEFINED __NVCC__)
set(DOXYGEN_REFERENCED_BY_RELATION NO)
set(DOXYGEN_REFERENCES_RELATION NO)

doxygen_add_docs(doc_lala_interval
                 "include/"
                 ALL
                 COMMENT "Generate HTML documentation")
endif()
