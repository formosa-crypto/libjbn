from Jasmin require import JByte_array.

require import BArray512 BArray1032.

clone SubByteArray as SBArray1032_512  with theory Asmall <= BArray512,
                                            theory Abig <= BArray1032.
