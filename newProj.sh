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
	(echo $f/* | tr ' ' '\n' | grep "\.v$") >> $PROJ
	echo "" >> $PROJ
done

# add our flags
echo "$FLAGS" >> $PROJ
