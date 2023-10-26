
## Usability & conventions

- parameter order convention: change to "results first".
- systematic definition of `_xxx_` procedure variants (preferred user access to the library code)
- ?? `for` vs `while` ?? (e.g. in mult/red innerloops)


## Proof

- add statements for ll and correctness lemmas "for all procedures" (after changes on the conventions...)
- (medium term) port existing proofs to the new framework
- add ct verification (generalize the extraction "heuristics/scripts" to deal with leakage)
- ? move sampling code/lemmas from `Bn_base

## Code (nice to have)

- test code...
- GMP baseline 
- a good profile of the efficiency/size of multiplication code and reductions
- efficient operand-scanning multiplication (with upto 4/5/6 limbs... -- base: curve25519)
- karatsuba
- add some safeguards to rsample (e.g. mask leading zeros on bnd, etc.)


