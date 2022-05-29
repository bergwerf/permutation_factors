#!/bin/bash

coq_makefile -f _CoqProject -o CoqMakefile
make -f CoqMakefile
