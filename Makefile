# Makefile equivalent to linux_build.sh
# Build CUDD library as a shared library

# Variables
ROOT = $(shell pwd)
CC = gcc
CFLAGS = -Wall -Werror-implicit-function-declaration -Werror=return-type -O3 -fPIC
LDFLAGS = -shared -z noexecstack -lm
TARGET = libcudd.so

# JDK used only for the JNI headers; override with JAVA_HOME=...
JAVA_HOME ?= $(shell dirname $$(dirname $$(readlink -f $$(command -v javac))))

# Include directories
INCLUDES = -I/usr/include/x86_64-linux-gnu/sys \
           -I$(JAVA_HOME)/include \
           -I$(JAVA_HOME)/include/linux \
           -I$(ROOT)/cuddf-s/cudd \
           -I$(ROOT)/cuddf-s/dddmp \
           -I$(ROOT)/cuddf-s/epd \
           -I$(ROOT)/cuddf-s/mtr \
           -I$(ROOT)/cuddf-s/nanotrav \
           -I$(ROOT)/cuddf-s/st \
           -I$(ROOT)/cuddf-s/synt \
           -I$(ROOT)/cuddf-s/util

# Object directory
OBJDIR = obj

# Source files
SOURCES = $(ROOT)/cuddf-s/cudd_jni.c \
          $(wildcard $(ROOT)/cuddf-s/cudd/*.c) \
          $(wildcard $(ROOT)/cuddf-s/dddmp/*.c) \
          $(wildcard $(ROOT)/cuddf-s/epd/*.c) \
          $(wildcard $(ROOT)/cuddf-s/mtr/*.c) \
          $(wildcard $(ROOT)/cuddf-s/st/*.c) \
          $(wildcard $(ROOT)/cuddf-s/synt/*.c) \
          $(wildcard $(ROOT)/cuddf-s/util/*.c)

# Object files - preserve directory structure in obj directory
OBJECTS = $(patsubst $(ROOT)/%, $(OBJDIR)/%, $(SOURCES:.c=.o))

# Default target
all: $(TARGET)

# Create object directory
$(OBJDIR):
	mkdir -p $(OBJDIR)

# Rule to build the shared library
$(TARGET): $(OBJECTS)
	$(CC) $(OBJECTS) $(LDFLAGS) -o $(TARGET)

# Rule to compile C files - preserve directory structure
$(OBJDIR)/%.o: $(ROOT)/%.c
	@mkdir -p $(dir $@)
	$(CC) $(CFLAGS) $(INCLUDES) -c $< -o $@

# Clean target
clean:
	rm -rf $(OBJDIR) $(TARGET)

# Phony targets
.PHONY: all clean