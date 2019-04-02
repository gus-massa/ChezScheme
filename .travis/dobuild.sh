#!/bin/bash
case $TARGET_MACHINE in
  *i3le) sudo apt-get -yq --no-install-suggests --no-install-recommends install uuid-dev:i386 ;;
  *)
esac

case $TARGET_MACHINE in
  *i3osx) PRE_TARGET_MACHINE=ti3osx;;
  *a6osx) PRE_TARGET_MACHINE=ta6osx;;
  *i3le) PRE_TARGET_MACHINE=ti3le;;
  *a6le) PRE_TARGET_MACHINE=ta6le;;
  *i3nt) PRE_TARGET_MACHINE=ti3nt;;
  *a6le) PRE_TARGET_MACHINE=ta6nt;;
  *)
esac
if [ $PRE_TARGET_MACHINE ] ; then
  ./configure -m=$PRE_TARGET_MACHINE
  make
  make bootfiles bootfiles=${TARGET_MACHINE}.boot
  exitcode=$?
  if [ $exitcode -ne 0 ] ; then
    echo "Failed: bootfile step"
    exit $exitcode
  fi
fi

./configure -m=$TARGET_MACHINE
exitcode=$?
if [ $exitcode -ne 0 ] ; then
  echo "Failed: configure step"
  exit $exitcode
fi
make
exitcode=$?
if [ $exitcode -ne 0 ] ; then
  echo "Failed: make step"
  exit $exitcode
fi

( cd ${TARGET_MACHINE}/mats && make partialx 2>&1 ) | tee Make.out | grep '^matting '
diff -q .travis/summary ${TARGET_MACHINE}/mats/summary
exitcode=$?
if [ $exitcode -ne 0 ] ; then
  echo "Failed: testing step"
  echo "mats summary:"
  cat ${TARGET_MACHINE}/mats/summary
  exit $exitcode
fi
