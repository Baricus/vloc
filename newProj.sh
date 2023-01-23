#!/bin/bash

# builds a new _CoqProject automatically as needed

PROJ="_CoqProject"

FOLDERS="CCode Lib Proofs"

# anything else we need to print
FLAGS="
-docroot .
-R . Vloc
"

# wipe the file
echo -n "" > $PROJ

# print out all .v files in the folder
for f in $FOLDERS
do
	(echo $f/* | tr ' ' '\n' | grep '\.[cv]$' | sed 's/\.c$/.v/' | uniq) >> $PROJ
	echo "" >> $PROJ
done

# add our flags
echo "$FLAGS" >> $PROJ

# for simplicity, we generate the default makefile here so we can avoid having it in the repo
coq_makefile -f $PROJ -o Makefile
