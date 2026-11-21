from Jasmin require import JByte_array.

require import BArray32 BArray1064.

clone SubByteArray as SBArray1064_32  with theory Asmall <= BArray32,
                                           theory Abig <= BArray1064.
