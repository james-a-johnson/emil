cmake_minimum_required(VERSION 3.24 FATAL_ERROR)

project(emil CXX)

set(CMAKE_EXPORT_COMPILE_COMMANDS 1)
set(HEADLESS 0)
set(CMAKE_CXX_STANDARD 20)

set(CMAKE_AUTOMOC ON)
set(CMAKE_INCLUDE_CURRENT_DIR ON)

find_path(
    BN_API_PATH
    NAMES binaryninjaapi.h
    HINTS ../../binaryninja-api $ENV{BN_API_PATH}
    REQUIRED
)
add_subdirectory(${BN_API_PATH} api)

find_package(Qt6 COMPONENTS Core Gui Widgets REQUIRED)

add_library(${PROJECT_NAME} SHARED src/emil.cpp)

target_link_libraries(${PROJECT_NAME} PUBLIC binaryninjaui Qt6::Core Qt6::Gui Qt6::Widgets)

set_target_properties(${PROJECT_NAME} PROPERTIES
    CXX_STANDARD 20
    CXX_VISIBILITY_PRESET hidden
    CXX_STANDARD_REQUIRED ON
    VISIBILITY_INLINES_HIDDEN ON
    POSITION_INDEPENDENT_CODE ON)

bn_install_plugin(${PROJECT_NAME})
