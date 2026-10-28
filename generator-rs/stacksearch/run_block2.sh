#!/bin/bash
cd "$(dirname "$0")"
M=./target/release/macro
$M 4 x0,x1,x2,x3 t6,t5,t7,t4 16 0 8 x 2 lazy,strict > block_s.txt 2>&1 &
$M 4 x0,x1,x2,x3 t6,P,t5,t7,t4 16 0 8 x 2 lazy,strict > blockexit_s.txt 2>&1 &
$M 4 x0,x1,x2,x3 t6,t5,t7,t4 16 0 8 final 2 lazy,strict > blockfinal_s.txt 2>&1 &
wait
