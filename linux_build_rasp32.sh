#!/bin/sh

# Remember to change SIZEOF_VOID_P 8 to SIZEOF_VOID_P 4  in config.h when compiling in ARM.

ROOT=$(pwd)

gcc -std=c99 -Wall -Werror-implicit-function-declaration -Werror=return-type -O3 -DHAVE_IEEE_754 -DBSD -DSIZEOF_VOID_P=4 -DSIZEOF_LONG=8 -fPIC -c \
$ROOT/cuddf-s/cudd_jni.c \
$ROOT/cuddf-s/cudd/*.c \
$ROOT/cuddf-s/dddmp/*.c \
$ROOT/cuddf-s/epd/*.c \
$ROOT/cuddf-s/mtr/*.c \
$ROOT/cuddf-s/st/*.c \
$ROOT/cuddf-s/synt/*.c \
$ROOT/cuddf-s/util/*.c \
-I/usr/include/arm-linux-gnueabihf/sys \
-I/usr/lib/jvm/jdk-8-oracle-arm32-vfp-hflt/include/ \
-I/usr/lib/jvm/jdk-8-oracle-arm32-vfp-hflt/include/linux \
-I$ROOT/cuddf-s/cudd \
-I$ROOT/cuddf-s/dddmp \
-I$ROOT/cuddf-s/epd \
-I$ROOT/cuddf-s/mtr \
-I$ROOT/cuddf-s/nanotrav \
-I$ROOT/cuddf-s/st \
-I$ROOT/cuddf-s/synt \
-I$ROOT/cuddf-s/util

gcc $ROOT/*.o -std=c99 -shared -z noexecstack -o $ROOT/rasp_32bit/libcudd.so

rm -rf *.o


