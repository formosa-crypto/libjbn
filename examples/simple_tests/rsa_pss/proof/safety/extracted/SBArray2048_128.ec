from Jasmin require import JByte_array.

require import BArray128 BArray2048.

clone SubByteArray as SBArray2048_128  with theory Asmall <= BArray128,
                                            theory Abig <= BArray2048.
