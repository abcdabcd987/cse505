#!/usr/bin/env bash

HW='final'

cd ..

if [ ! -d "$HW" ]; then
  echo "ERROR: could not find '$HW'"
  echo
  echo "Please do not rename the final directory."
  echo "To fix this issue, rename your final directory back to '$HW'"
  exit 1
fi

zip -x "*frap*" \
    -x "*.vo*" \
    -x "*.glob*" \
    -x "*.native*" \
    -x "*.aux*" \
    -x "*_build*" \
    -r ${HW}.zip ${HW}/
