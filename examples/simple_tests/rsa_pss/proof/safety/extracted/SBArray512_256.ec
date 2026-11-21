from Jasmin require import JByte_array.

require import BArray256 BArray512.

clone SubByteArray as SBArray512_256  with theory Asmall <= BArray256,
                                           theory Abig <= BArray512.
