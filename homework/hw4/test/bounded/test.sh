#!/usr/bin/env bash

TDIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
IMP="${TDIR}/../../Imp.native"

if ! [ -f "$IMP" ]; then
  echo "ERROR: could not find $IMP, please build first"
  exit 1
fi

if [ $# -ne 2 ]; then
  echo "Usage: $0 MININT MAXINT"
  exit 1
fi

MININT=$1
MAXINT=$2

function go {
  prog="$1"
  shift

  input="$(mktemp TESTIMP.XXXXX)"
  for a in "$@"; do
    echo "$a" >> "$input"
  done

  if cat "$input" | $IMP --test "$prog" > /dev/null; then
    rm "$input"
  else
    echo "FAIL $prog on:"
    cat "$input"
    exit 1
  fi
}

function bloop {
  for x in "False" "True"; do
    $@ "$x"
  done
}

function iloop {
  for x in $(seq $MININT $MAXINT); do
    $@ "$x"
  done
}

function sloop {
  for x in "\"\"" "a" "ab" "abc"; do
    $@ "$x"
  done
}

pushd "$TDIR" > /dev/null
bloop go not.imp
iloop go neg.imp

iloop iloop go add.imp
sloop sloop go sadd.imp
iloop iloop go sub.imp
iloop iloop go mul.imp
iloop iloop go div.imp
iloop iloop go mod.imp

iloop iloop go eq-i.imp
bloop bloop go eq-b.imp
iloop iloop go le.imp
iloop iloop go lt.imp

bloop bloop go conj.imp
bloop bloop go disj.imp
