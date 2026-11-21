from Jasmin require import JByte_array.

require import BArray256 BArray1032.

clone SubByteArray as SBArray1032_256  with theory Asmall <= BArray256,
                                            theory Abig <= BArray1032.
