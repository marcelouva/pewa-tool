#!/bin/bash
cd bin

case_study="treeset"
echo "Case study: $case_study"
python wagfinder.py $case_study add 1;
python wagfinder.py $case_study ceiling  1;
python wagfinder.py $case_study clear 1;
python wagfinder.py $case_study contains 1;
python wagfinder.py $case_study first 1;
python wagfinder.py $case_study last 1;
python wagfinder.py $case_study floor 1;
python wagfinder.py $case_study higher 1;
python wagfinder.py $case_study is_empty 1;
python wagfinder.py $case_study lower 1;
python wagfinder.py $case_study poll_first 1;
python wagfinder.py $case_study poll_last 1;
python wagfinder.py $case_study remove 1;


echo "search complete !!!"
cd ..

