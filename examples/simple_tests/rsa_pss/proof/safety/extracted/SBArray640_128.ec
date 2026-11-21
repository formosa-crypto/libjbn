from Jasmin require import JByte_array.

require import BArray128 BArray640.

clone SubByteArray as SBArray640_128  with theory Asmall <= BArray128,
                                           theory Abig <= BArray640.
