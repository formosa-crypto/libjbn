#!/bin/bash

top=$(cd "$(dirname "$0")/../../" ; pwd -P)

if [ ! "$#" -eq 5 ]
then
cat <<END

usage:   $ ./gen.sh TYPE DEST_DIR MIN_LIMBS MAX_LIMBS NUMBER_TESTS
 * TYPE : 'det' or 'rnd'

 example: $ ./gen.sh det _build/ 1 16 10
  * creates the following files in _build/ directory:
   * libjbn_d_{1..16}_{1..10}.{jazz,c}

 example: $ ./gen.sh rdn _build/ 4 4 1
  * creates two files:
   * _build/libjbn_d_4_1.jazz and _build/libjbn_d_4_1.c

 notes:
  * to compile _build/libjbn_d_4_1.jazz run:
   * jasminc -I Libjbn:${top}/src _build/libjbn_d_4_1.jazz -o _build/libjbn_d_4_1.s

END
  exit
fi

ptype=$1
build=$2
min_limbs=$3
max_limbs=$4
max_tests=$5

mkdir -p $build

for nlimbs in $(seq $min_limbs $max_limbs)
do
  counter=1
  while read prime
  do
    for type in j,jazz c,c
    do
      IFS=','
      set -- $type
      ./params $1 $nlimbs $prime > ${build}/libjbn_d_${nlimbs}_${counter}.${2}
    done
    ((counter++))
  done < <(./primes-${ptype} $nlimbs $max_tests)
done

