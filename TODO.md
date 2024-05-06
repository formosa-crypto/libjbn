
## Usability & conventions

+ [Done] parameter order convention: change to "results first".
+ [Done] systematic definition of `_xxx_` procedure variants (preferred user access to the library code)
- ?? `for` vs `while` ?? (e.g. in mult/red innerloops)


## Proof

+ [In progress] add statements for ll and correctness lemmas "for all procedures" (after changes on the conventions...)
- (medium term) port existing proofs to the new framework
- add ct verification ([Done] generalize the extraction "heuristics/scripts" to deal with leakage)
+ [In progress] move sampling code/lemmas from `Bn_base` into `Bn_rnd`

## Code (nice to have)

- test code...
- GMP baseline 
- a good profile of the efficiency/size of multiplication code and reductions
- efficient operand-scanning multiplication (with upto 4/5/6 limbs... -- base: curve25519)
- [In progress] karatsuba
- add some safeguards to rsample (e.g. mask leading zeros on bnd, etc.)


