#!/bin/bash
cd bin
echo "Parameters: <case_study> <action>"
python wagfinder.py $1 $2 1
echo "search complete !!!"
cd ..

