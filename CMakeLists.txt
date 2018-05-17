cmake_minimum_required(VERSION 3.10)
project(Bpril)

set(CMAKE_CXX_STANDARD 11)

include_directories(.)

add_executable(Bpril
        Kernel.cpp
        Kernel.h
        Library.cpp
        Library.h
        main.cpp
        ProofGraph.cpp
        ProofGraph.h
        Search.cpp
        Search.h
        TypeTerm.cpp
        TypeTerm.h
        Unification.cpp
        Unification.h)
