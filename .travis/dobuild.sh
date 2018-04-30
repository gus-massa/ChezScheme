#!/bin/bash

./configure -m=$TARGET_MACHINE
exitcode=$?
if [ $exitcode -ne 0 ] ; then
  echo "Failed: configure step"
  exit $exitcode
fi
( cd ${TARGET_MACHINE}/c && make)
( cd ${TARGET_MACHINE}/s && make all)
make
exitcode=$?
if [ $exitcode -ne 0 ] ; then
  echo "Failed: make step"
  exit $exitcode
fi
echo !!!!!!
( export SCHEMEHEAPDIRS=.:../../boot/${TARGET_MACHINE} && cd ${TARGET_MACHINE}/bin/${TARGET_MACHINE} && ./scheme -q < ../../../test.ss )
echo !!!!!!
( cd ${TARGET_MACHINE}/mats && make partialx 2>&1 ) | tee Make.out | grep '^matting '
diff -q .travis/summary ${TARGET_MACHINE}/mats/summary
exitcode=$?

if [ $exitcode -ne 0 ] ; then
  echo "Failed: testing step"
  echo "mats summary:"
  cat ${TARGET_MACHINE}/mats/summary
  exit $exitcode
fi
