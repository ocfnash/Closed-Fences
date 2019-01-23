#!/bin/bash

test_data=test-cases/fence4.in.$1

echo Coq implementation:
cat $test_data | coq/fence4
echo

echo Haskell implementation:
cat $test_data | haskell/fence4
echo
echo

echo Cpp implementation:
# Reads from file instead of stdin to conform with USACO spec
cd cpp
ln -s ../$test_data fence4.in
./fence4
rm fence4.in fence4.out
cd ..
