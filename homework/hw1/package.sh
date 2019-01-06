#!/usr/bin/env bash

HW='hw1'

cd ..

if [ ! -d "$HW" ]; then
  echo "ERROR: could not find '$HW'"
  echo
  echo "Please do not rename the homework directory."
  echo "To fix this issue, rename your homework directory back to '$HW'"
  exit 1
fi

zip -x "*frap*" \
    -x "*.vo*" \
    -x "*.glob*" \
    -x "*.native*" \
    -x "*.aux*" \
    -x "*_build*" \
    -r hw1.zip hw1/
