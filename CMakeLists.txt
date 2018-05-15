cmake_minimum_required(VERSION 3.10)
project(Bpril)

set(CMAKE_CXX_STANDARD 11)

add_executable(Bpril main.cpp TypeTerm.cpp TypeTerm.h Kernel.cpp Kernel.h Library.cpp Library.h Unification.cpp Unification.h ProofGraph.cpp ProofGraph.h Search.cpp Search.h)