#!/bin/bash
cd "$(dirname "$0")"
M=./target/release/macro
$M 4 x0,x1,x2,x3 t6,t5,t7,t4 16 0 8 x 2 lazy > block0.txt 2>&1 &
$M 4 x0,x1,x2,x3 t6,P,t5,t7,t4 16 0 8 x 2 lazy > blockexit0.txt 2>&1 &
$M 4 x0,x1,x2,x3 t6,t5,t7,t4,P 16 0 8 final 2 lazy > blockfinal0.txt 2>&1 &
wait
