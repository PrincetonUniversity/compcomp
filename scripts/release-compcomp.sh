#!/bin/bash

cd ../..
if [ -d compcomp-release ]; then
  rm -rf compcomp-release
fi
cp -r compcomp compcomp-release
cd compcomp-release 
make distclean
cd ../
tar czf compcomp-release.tgz compcomp-release
