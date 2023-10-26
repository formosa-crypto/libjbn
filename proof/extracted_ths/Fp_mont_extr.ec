require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


(* Theory Parameters *)
op nlimbs: int.
clone export PolyArray as Ap1
 with op size <- nlimbs.
type bignum = W64.t Ap1.t.
clone export PolyArray as Ap2
 with op size <- 2*nlimbs.
type bignum2 = W64.t Ap2.t.


op glob_P: bignum.
op glob_mP: bignum.
op glob_exp0: bignum.
op glob_Pm2: bignum.
op glob_P0i: W64.t.
op glob_rMP: bignum.



from JPExtract require Bn_base_extr.
clone Bn_base_extr as BNbase_extr
 with op nlimbs <- nlimbs,
      theory Ap1 <- Ap1,
      theory Ap2 <- Ap2.
module BN = BNbase_extr.M. 

from JPExtract require Fp_base_extr.
clone Fp_base_extr as FPbase_extr
 with op nlimbs <- nlimbs,
      op glob_P <- glob_P,
      op glob_mP <- glob_mP,
      op glob_Pm2 <- glob_Pm2,
      op glob_exp0 <- glob_exp0,
      theory Ap1 <- Ap1,
      theory Ap2 <- Ap2,
      theory BNbase_extr <= BNbase_extr.
module FP = FPbase_extr.M.


module M = {
  proc _redM (a:bignum2, r:bignum) : bignum = {
    
    var _P0i:W64.t;
    
    _P0i <- glob_P0i;
    a <- a;
    r <@ BN.__mont_redM (a, r, glob_P, glob_mP, _P0i);
    r <- r;
    return (r);
  }
  
  proc __fromM (a:bignum) : bignum = {
    
    var _tmp:bignum2;
    var tmp2:bignum;
    var tmp:bignum2;
    _tmp <- witness;
    tmp <- witness;
    tmp2 <- witness;
    tmp2 <- (Ap1.init (fun i => _tmp.[0 + i]));
    tmp2 <@ BN.__copy2 (a, tmp2);
    _tmp <- Ap2.init
            (fun i => if 0 <= i < 0 + 11 then tmp2.[i-0] else _tmp.[i]);
    tmp2 <- (Ap1.init (fun i => _tmp.[11 + i]));
    tmp2 <@ BN.__set0 (tmp2);
    _tmp <- Ap2.init
            (fun i => if 11 <= i < 11 + 11 then tmp2.[i-11] else _tmp.[i]);
    tmp <- _tmp;
    a <@ _redM (tmp, a);
    return (a);
  }

  module Pfp = { proc fun_red = _redM }
  proc __toM (a:bignum) : bignum = {
    
    var rMP:bignum;
    rMP <- witness;
    rMP <- glob_rMP;
    a <- a;
    a <@ FP(Pfp)._mulmU (a, rMP);
    a <- a;
    return (a);
  }
}.
