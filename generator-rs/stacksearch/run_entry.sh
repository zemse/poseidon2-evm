#!/bin/bash
cd "$(dirname "$0")"
M=./target/release/macro
{
  echo "== t2 entry A";   $M 2 x0,x1,P o0,P,o1 16 2 8 x 2
  echo "== t2 entry B";   $M 2 x0,x1,P o0,o1 16 2 8 x 2
  echo "== t3 entry A";   $M 3 x0,x1,x2,P o0,P,o1,o2 16 2 8 x 2
  echo "== t3 entry B";   $M 3 x0,x1,x2,P o0,o1,o2 16 2 8 x 2
  echo "== t3 reentry osaka B"; $M 3 s0,s1,P,s2 o0,o1,o2 16 2 8 x 2
  echo "== t3 reentry osaka A"; $M 3 s0,s1,P,s2 o0,P,o1,o2 16 2 8 x 2
} > entry.txt 2>&1
