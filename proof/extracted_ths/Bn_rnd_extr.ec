require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


(* Theory Parameters *)
op nlimbs: int.
clone export PolyArray as Ap1
 with op size <- nlimbs.
clone export PolyArray as Ap2
 with op size <- 2*nlimbs.

(* additional arrays needed by 'bn_rnd' *)
clone import PolyArray as Ap3
 with op size <- 8*nlimbs.
clone import WArray as WAp3
 with op size <- 8*nlimbs.


from JPExtract require Bn_base_extr.

clone Bn_base_extr as BNbase_extr
 with op nlimbs <- nlimbs,
      theory Ap1 <- Ap1,
      theory Ap2 <- Ap2.

module BN_M = BNbase_extr.M. 
module BN_MLeak = BNbase_extr.MLeak.


from JExtract require export MLeakage.

module M = {

  proc randombytes_p3(a:W8.t Ap3.t) : W8.t Ap3.t = {
    a <$ dmap WAp3.darray
         (fun a => Ap3.init (fun i => WAp3.get8 a i));
    return a;
  }

  proc _rnd_ (a:W64.t Ap1.t) : W64.t Ap1.t = {
    var aux: W8.t Ap3.t;
    
    
    
    a <- a;
    aux <@ randombytes_p3 ((Ap3.init (fun i => get8
                              (WAp3.init64 (fun i => (a).[i])) i)));
    a <-
    (Ap1.init (fun i => get64 (WAp3.init8 (fun i => (aux).[i])) i));
    a <- a;
    return (a);
  }
  
  proc _rsample_ (a:W64.t Ap1.t, bnd:W64.t Ap1.t) : W64.t Ap1.t = {
    
    var cf:bool;
    
    a <@ _rnd_ (a);
    cf <@ BN_M._lt_cf_ (a, bnd);
    while ((! cf)) {
      a <@ _rnd_ (a);
      cf <@ BN_M._lt_cf_ (a, bnd);
    }
    return (a);
  }
}.



module MLeak = {

  proc randombytes_p3(a:W8.t Ap3.t) : W8.t Ap3.t = {
    a <$ dmap WAp3.darray
         (fun a => Ap3.init (fun i => WAp3.get8 a i));
    return a;
  }

  proc _rnd_ (a:W64.t Ap1.t) : W64.t Ap1.t = {
    var aux_0: W8.t Ap3.t;
    var aux: W64.t Ap1.t;
    
    
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- a;
    a <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <@ randombytes_p3 ((Ap3.init (fun i => get8
                                (WAp3.init64 (fun i => (a).[i])) i)));
    a <-
    (Ap1.init (fun i => get64 (WAp3.init8 (fun i => (aux_0).[i])) i));
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- a;
    a <- aux;
    return (a);
  }
  
  proc _rsample_ (a:W64.t Ap1.t, bnd:W64.t Ap1.t) : W64.t Ap1.t = {
    var aux_0: bool;
    var aux: W64.t Ap1.t;
    
    var cf:bool;
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <@ _rnd_ (a);
    a <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <@ BN_M._lt_cf_ (a, bnd);
    cf <- aux_0;
    LEAK.leakages <- LeakCond((! cf)) :: LeakAddr([]) :: LEAK.leakages;
    
    while ((! cf)) {
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux <@ _rnd_ (a);
      a <- aux;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_0 <@ BN_M._lt_cf_ (a, bnd);
      cf <- aux_0;
    LEAK.leakages <- LeakCond((! cf)) :: LeakAddr([]) :: LEAK.leakages;
    
    }
    return (a);
  }
}.

