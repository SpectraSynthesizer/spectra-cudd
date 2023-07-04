#!/bin/sh

ROOT=$(pwd)

clang -arch arm64 -Wall -O3 -fPIC -c \
$ROOT/cuddf-s/util/*.c \
$ROOT/cuddf-s/mtr/*.c \
$ROOT/cuddf-s/cudd/*.c \
$ROOT/cuddf-s/dddmp/*.c \
$ROOT/cuddf-s/epd/*.c \
$ROOT/cuddf-s/st/*.c \
$ROOT/cuddf-s/synt/*.c \
$ROOT/cuddf-s/cudd_jni.c \
-I/usr/include/sys \
-I/opt/homebrew/opt/openjdk@17/include \
-I$ROOT/cuddf-s/util \
-I$ROOT/cuddf-s/mtr \
-I$ROOT/cuddf-s/cudd \
-I$ROOT/cuddf-s/dddmp \
-I$ROOT/cuddf-s/epd \
-I$ROOT/cuddf-s/nanotrav \
-I$ROOT/cuddf-s/st \
-I$ROOT/cuddf-s/synt

clang $ROOT/*.o -dynamiclib -o $ROOT/cudd.dylib

rm -rf *.o
