#!/bin/bash
cd "$(dirname "$0")"
M=./target/release/macro
{
  echo "== t2 B";       $M 2 s0,s1 o0,o1 16 2 8 x 2
  echo "== t2 A";       $M 2 s0,P,s1 o0,P,o1 16 2 8 x 2
  echo "== t2 B->A";    $M 2 s0,s1 o0,P,o1 16 2 8 x 2
  echo "== t2 final B"; $M 2 s0,s1 o0,o1,P 16 2 8 final 2
  echo "== t2 final A"; $M 2 s0,P,s1 o0,o1,P 16 2 8 final 2
  echo "== t3 B";       $M 3 s0,s1,s2 o0,o1,o2 16 2 8 x 2
  echo "== t3 A";       $M 3 s0,P,s1,s2 o0,P,o1,o2 16 2 8 x 2
  echo "== t3 B->A";    $M 3 s0,s1,s2 o0,P,o1,o2 16 2 8 x 2
  echo "== t3 final B"; $M 3 s0,s1,s2 o0,o1,o2,P 16 2 8 final 2
  echo "== t3 final A"; $M 3 s0,P,s1,s2 o0,o1,o2,P 16 2 8 final 2
} > t23.txt 2>&1
