#!/bin/sh

# Simple script for generating the makefile and the _CoqProject file

LibName=SFC

{ echo "-R . $LibName " ; find -name '*.v' -print; } > _CoqProject && coq_makefile -f _CoqProject -o Makefile
