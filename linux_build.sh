#!/bin/sh

set -e

ROOT=$(pwd)

# Compiler: override with e.g. CC=gcc-13 ./linux_build.sh
CC=${CC:-gcc}

# JDK used only for the JNI headers (jni.h, jni_md.h), which are stable across
# JDK versions. Uses $JAVA_HOME, else the JDK of javac on PATH, else default-java.
if [ -z "$JAVA_HOME" ] || [ ! -f "$JAVA_HOME/include/jni.h" ]; then
	if command -v javac >/dev/null 2>&1; then
		JAVA_HOME=$(dirname "$(dirname "$(readlink -f "$(command -v javac)")")")
	else
		JAVA_HOME=/usr/lib/jvm/default-java
	fi
fi
if [ ! -f "$JAVA_HOME/include/jni.h" ]; then
	echo "jni.h not found under $JAVA_HOME/include; install a JDK or set JAVA_HOME" >&2
	exit 1
fi
echo "Using $($CC --version | head -n 1), JNI headers from $JAVA_HOME"

$CC -Wall -Werror-implicit-function-declaration -Werror=return-type -O3 -fPIC -c \
$ROOT/cuddf-s/cudd_jni.c \
$ROOT/cuddf-s/cudd/*.c \
$ROOT/cuddf-s/dddmp/*.c \
$ROOT/cuddf-s/epd/*.c \
$ROOT/cuddf-s/mtr/*.c \
$ROOT/cuddf-s/st/*.c \
$ROOT/cuddf-s/synt/*.c \
$ROOT/cuddf-s/util/*.c \
-I/usr/include/x86_64-linux-gnu/sys \
-I$JAVA_HOME/include \
-I$JAVA_HOME/include/linux \
-I$ROOT/cuddf-s/cudd \
-I$ROOT/cuddf-s/dddmp \
-I$ROOT/cuddf-s/epd \
-I$ROOT/cuddf-s/mtr \
-I$ROOT/cuddf-s/nanotrav \
-I$ROOT/cuddf-s/st \
-I$ROOT/cuddf-s/synt \
-I$ROOT/cuddf-s/util

$CC $ROOT/*.o -shared -z noexecstack -lm -o $ROOT/libcudd.so

rm -rf *.o

