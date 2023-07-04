#!/bin/sh

ROOT=$(pwd)

gcc -std=c99 -Wall -Werror-implicit-function-declaration -Werror=return-type -m32 -O3 -fPIC -c \
$ROOT/cuddf-s/cudd_jni.c \
$ROOT/cuddf-s/cudd/*.c \
$ROOT/cuddf-s/dddmp/*.c \
$ROOT/cuddf-s/epd/*.c \
$ROOT/cuddf-s/mtr/*.c \
$ROOT/cuddf-s/st/*.c \
$ROOT/cuddf-s/synt/*.c \
$ROOT/cuddf-s/util/*.c \
-I/usr/include/x86_64-linux-gnu/sys \
-I/usr/lib/jvm/java-8-openjdk-amd64/include \
-I/usr/lib/jvm/java-8-openjdk-amd64/include/linux \
-I$ROOT/cuddf-s/cudd \
-I$ROOT/cuddf-s/dddmp \
-I$ROOT/cuddf-s/epd \
-I$ROOT/cuddf-s/mtr \
-I$ROOT/cuddf-s/nanotrav \
-I$ROOT/cuddf-s/st \
-I$ROOT/cuddf-s/synt \
-I$ROOT/cuddf-s/util

gcc $ROOT/*.o -std=c99 -m32 -shared -z noexecstack -o $ROOT/32bit/libcudd.so

rm -rf *.o


