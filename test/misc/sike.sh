#!/bin/sh

if [ ! "$#" -eq 1 ]
then
cat <<END

usage: $ ./sike.sh DEST_DIR

END
  exit
fi

build=$1

mkdir -p $build

for type in j,jazz c,c
do
  IFS=','
  set -- $type
  ./params $1 7 0x0002341f271773446cfc5fd681c520567bc65c783158aea3fdc1767ae2ffffffffffffffffffffffffffffffffffffffffffffffffffffff > $build/libjbn_sike434.$2

  ./params $1 8 0x004066f541811e1e6045c6bdda77a4d01b9bf6c87b7e7daf13085bda2211e7a0abffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff > $build/libjbn_sike503.$2

  ./params $1 10 0x000000027bf6a768819010c251e7d88cb255b2fa10c4252a9ae7bf45048ff9abb1784de8aa5ab02e6e01ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff > $build/libjbn_sike610.$2

  ./params $1 12 0x00006fe5d541f71c0e12909f97badc668562b5045cb25748084e9867d6ebe876da959b1a13f7cc76e3ec968549f878a8eeafffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff > $build/libjbn_sike751.$2
done
