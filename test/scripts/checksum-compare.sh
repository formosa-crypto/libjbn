#!/usr/bin/env bash

top=$(cd "$(dirname "$0")/../../" ; pwd -P)

if [ ! "$#" -eq 3 ]
then
cat <<END

usage:   $ ./checksum-compare.sh DIR LIBRARY_NAME_1 LIBRARY_NAME_2

 * DIR : for example, ${top}/test/bin/
 * LIBRARY_NAME_1 : for example, libjbn
 * LIBRARY_NAME_2 : for example, gmp

 example 1: $ ./checksum-compare.sh ${top}/test/bin/ libjbn gmp
 example 2: $ ./scripts/checksum-compare.sh bin/ libjbn gmp

END
  exit
fi

dir=$1
lib1=$2
lib2=$3

while read lib1_file
do

  lib2_file=${lib1_file/\/${lib1}_/\/${lib2}_}

  checksum_lib1=$(cat $lib1_file);
  checksum_lib2=$(cat $lib2_file);

  result_file=$lib1_file.checksum_match_with_$lib2

  if [ "$checksum_lib1" == "$checksum_lib2" ];
  then
    echo -n "" > $result_file.log
  else
    echo -e "$checksum_lib1 /\n$checksum_lib2" > $result_file.error
  fi

done < <(find $dir -name "${lib1}_*.out")
