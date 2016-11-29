#!/bin/bash
cd bin
case_study="list"
echo "Case study: $case_study"
python wagfinder.py $case_study push 1;
python wagfinder.py $case_study add_first  1;
python wagfinder.py $case_study add 1;
python wagfinder.py $case_study add_last  1;
python wagfinder.py $case_study clear  1;
python wagfinder.py $case_study contains 1;
python wagfinder.py $case_study element 1;
python wagfinder.py $case_study get_first 1;
python wagfinder.py $case_study get 1;
python wagfinder.py $case_study get_last 1;
python wagfinder.py $case_study index_of 1;
python wagfinder.py $case_study is_empty 1;
python wagfinder.py $case_study last_index_of 1;
python wagfinder.py $case_study offer 1;
python wagfinder.py $case_study offer_first 1;
python wagfinder.py $case_study offer_last 1;
python wagfinder.py $case_study peek 1;
python wagfinder.py $case_study pool 1;
python wagfinder.py $case_study pool_first 1;
python wagfinder.py $case_study pool_last 1;
python wagfinder.py $case_study pop 1;
python wagfinder.py $case_study remove 1;
python wagfinder.py $case_study remove2 1;
python wagfinder.py $case_study remove_first 1;
python wagfinder.py $case_study remove_last 1;
python wagfinder.py $case_study set_element 1;
python wagfinder.py $case_study size 1;

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

poll_first_entry |  poll_last_entry |  put |  remove |  

case_study="treemap"
echo "Case study: $case_study"
python wagfinder.py $case_study ceiling_entry 1;
python wagfinder.py $case_study clear 1;
python wagfinder.py $case_study contains_key 1;
python wagfinder.py $case_study contains_value 1;
python wagfinder.py $case_study first_entry 1;
python wagfinder.py $case_study first_key 1;
python wagfinder.py $case_study floor_key 1;
python wagfinder.py $case_study floor_entry 1;
python wagfinder.py $case_study get 1;
python wagfinder.py $case_study higher_key 1;
python wagfinder.py $case_study higher_entry 1;
python wagfinder.py $case_study is_empty 1;
python wagfinder.py $case_study last_key 1;
python wagfinder.py $case_study last_entry 1;
python wagfinder.py $case_study lower_key 1;
python wagfinder.py $case_study lower_entry 1;
python wagfinder.py $case_study put 1;
python wagfinder.py $case_study remove 1;
python wagfinder.py $case_study pool_last_entry 1;
python wagfinder.py $case_study pool_first_entry 1;


echo "search complete !!!"
cd ..

