#!/usr/bin/env bash

i=1
max_attempts=10
while ! memora "$@"; do
  echo "Attempt $i/$max_attempts of 'memora $@' failed."
  if test $i -ge $max_attempts; then
    echo "'memora $@' keeps failing; aborting!"
    exit 1
  fi
  i=$(($i+1))
done
