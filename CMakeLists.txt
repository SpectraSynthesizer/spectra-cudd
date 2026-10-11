cmake_minimum_required(VERSION 3.2)

project(cudd)

find_package(Java COMPONENTS Development)
find_package(JNI REQUIRED)

FILE(GLOB glob_cudd cuddf-s/cudd/*.c)
FILE(GLOB glob_dddmp cuddf-s/dddmp/*.c)
FILE(GLOB glob_epd cuddf-s/epd/*.c)
FILE(GLOB glob_mtr cuddf-s/mtr/*.c)
FILE(GLOB glob_st cuddf-s/st/*.c)
FILE(GLOB glob_synt cuddf-s/synt/*.c)
FILE(GLOB glob_util cuddf-s/util/*.c)

include_directories(${JNI_INCLUDE_DIRS} cuddf-s/cudd cuddf-s/dddmp cuddf-s/epd cuddf-s/mtr cuddf-s/st cuddf-s/synt cuddf-s/util)

add_library(cudd SHARED
    cuddf-s/cudd_jni.c
    ${glob_cudd}
    ${glob_dddmp}
    ${glob_epd}
    ${glob_mtr}
    ${glob_st}
    ${glob_synt}
    ${glob_util}
    )

