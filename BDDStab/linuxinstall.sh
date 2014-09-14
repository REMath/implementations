#! /bin/sh

if [ -d "jakstab" ]; then echo Jakstab directory already present; exit 1; fi
echo Cloning Jakstab
hg clone https://bitbucket.org/jkinder/jakstab
cd jakstab
hg update dde24eb1ac03
if [ $? != 0 ]; then echo Could not clone Jakstab; exit 1; fi
echo Downloading Scala
wget http://www.scala-lang.org/files/archive/scala-2.10.3.tgz
if [ $? != 0 ]; then echo Could not download Scala; exit 1; fi
echo Unpacking Scala
tar xf scala-2.10.3.tgz
if [ $? != 0 ]; then echo Could not unpack Scala; exit 1; fi
echo Copying scala-library.jar
cp -i scala-2.10.3/lib/scala-library.jar lib
if [ $? != 0 ]; then echo Could copy scala-library.jar; exit 1; fi
echo Copying bdd.jar
cp -i ../bdd.jar lib
if [ $? != 0 ]; then echo Could copy bdd.jar; exit 1; fi
echo Importing BDDStab patch
hg import ../bddstab.diff
if [ $? != 0 ]; then echo Could not import bddstab.diff; exit 1; fi
echo Will compile now
./compile.sh
if [ $? != 0 ]; then echo Could not import bddstab.diff; exit 1; else echo All good; fi
cd ..
