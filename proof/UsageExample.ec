require import AllCore Int IntDiv List.


from Jasmin require import JModel_x86.
import SLH64.

require JBigNumber.
require import MLeakage.


require Bn_util Bn_base Bn_rnd Bn_exp Fp_base Fp_mont.

(* Adapt to fit the use case... *)

from JExtract require import XtrCode.
from JExtract require XtrCodeCT.
from JExtract require import Array11 Array22 Array88 WArray88.

abbrev nlimbs = 11.

print XtrCode.

clone import JBigNumber.BigN
 with op nlimbs <- 11,
      theory BN.A <= Array11,
      theory BN2.A <= Array22,
      theory BN_Abytes <= Array88,
      theory BN_WAbytes <= WArray88
      proof gt0_nlimbs by done.


(* --- *)


clone Fp_mont as FPM
 with op nlimbs <- nlimbs,
      theory BigN <- BigN,
      op P <- bn XtrCode.glob_P,
      op glob_P <- XtrCode.glob_P,
      op glob_mP <- XtrCode.glob_mP,
      op glob_P0i <- XtrCode.glob_P0i,
      op glob_exp0 <- XtrCode.glob_exp0,
      op glob_Pm2 <- XtrCode.glob_Pm2
(*      theory BNUTIL <- BNUTIL,
      theory BNB <- BNB*)
(*      theory FPB <- FPB*)
      proof gt0_nlimbs by done.


equiv FPM_mulm_eq:
 FPM.FPB.M(FPM.M.P_FP)._mulm_ ~ XtrCode.M(Syscall).fPM_mulm_ : ={arg} ==> ={res}
by sim.

equiv BN_eq_eq:
 FPM.BNB.M._eq_ ~ XtrCode.M(Syscall).bN_eq_ : ={arg} ==> ={res}
by sim.

equiv BN_muln_eq:
 FPM.BNB.M._muln_ ~ XtrCode.M(Syscall).bN_muln_ : ={arg} ==> ={res}
by sim.

print FPM.BNB._muln__ll.

equiv BN_cswap_mask_eq:
 FPM.BNB.M._cswap_mask_ ~ XtrCode.M(Syscall).bN_cswap_mask_ : ={arg} ==> ={res}
by sim.

equiv BN_rsample_eq:
 FPM.FPB.BNRND.M._rsample_ ~ XtrCode.M(Syscall).bN_rsample_
 : ={arg} ==> ={res}
by sim.



(* And now with leakage annotations... *)
equiv BN_muln_eqLeak:
 FPM.BNB.MLeak._muln_ ~ XtrCodeCT.M(XtrCodeCT.Syscall).bN_muln_ :
 ={arg} /\ LEAK.leakages{1} = XtrCodeCT.M.leakages{2} 
 ==> ={res} /\ LEAK.leakages{1} = XtrCodeCT.M.leakages{2}
by sim.



