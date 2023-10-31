require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


from JExtract require export MLeakage Array3.

(* This Theory has no Parameters *)

(* Rewritings:
  "bNUTIL" -> "" (remove qualifier)
*)

module M = {
  proc __mask_zf (mask:W64.t) : bool = {
    
    var zf:bool;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:W64.t;
    
    ( _0,  _1,  _2,  _3, zf,  _4) <- AND_64 mask mask;
    return (zf);
  }
  
  proc __mask_cf (mask:W64.t) : bool = {
    
    var cf:bool;
    var t:W64.t;
    
    t <- (W64.of_int 0);
    (cf, t) <- sbb_64 t mask false;
    return (cf);
  }
  
  proc __cf_mask (cf:bool) : W64.t = {
    
    var mask:W64.t;
    
    mask <- (W64.of_int 0);
    (cf, mask) <- adc_64 mask (W64.of_int 0) cf;
    mask <- (- mask);
    return (mask);
  }
  
  proc __addacc3 (a:W64.t Array3.t, b1:W64.t, b0:W64.t, k:int) : 
  W64.t Array3.t = {
    var aux: bool;
    var aux_0: W64.t;
    
    var cf:bool;
    
    (aux, aux_0) <- adc_64 a.[(k %% 3)] b0 false;
    cf <- aux;
    a.[(k %% 3)] <- aux_0;
    (aux, aux_0) <- adc_64 a.[((k + 1) %% 3)] b1 cf;
    cf <- aux;
    a.[((k + 1) %% 3)] <- aux_0;
    (aux, aux_0) <- adc_64 a.[((k + 2) %% 3)] (W64.of_int 0) cf;
    cf <- aux;
    a.[((k + 2) %% 3)] <- aux_0;
    return (a);
  }
  
  proc __addacc3x2 (a:W64.t Array3.t, x:W64.t, y:W64.t, k:int) : 
  W64.t Array3.t = {
    var aux: bool;
    var aux_0: W64.t;
    
    var b1:W64.t;
    var b0:W64.t;
    var t:W64.t;
    var cf:bool;
    var b2:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    
    (b1, b0) <- mulu_64 x y;
    t <- b0;
    b0 <- (b0 `<<` (W8.of_int 1));
    ( _0, cf,  _1,  _2,  _3, b1) <- SHLD_64 b1 t (W8.of_int 1);
    b2 <- MOV_64 (W64.of_int 0);
    (cf, b2) <- adc_64 b2 b2 cf;
    (aux, aux_0) <- adc_64 a.[(k %% 3)] b0 false;
    cf <- aux;
    a.[(k %% 3)] <- aux_0;
    (aux, aux_0) <- adc_64 a.[((k + 1) %% 3)] b1 cf;
    cf <- aux;
    a.[((k + 1) %% 3)] <- aux_0;
    (aux, aux_0) <- adc_64 a.[((k + 2) %% 3)] b2 cf;
    cf <- aux;
    a.[((k + 2) %% 3)] <- aux_0;
    return (a);
  }
}.


module MLeak = {
  
  proc __mask_zf (mask:W64.t) : bool = {
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux_0: bool;
    var aux: bool;
    var aux_4: W64.t;
    
    var zf:bool;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:W64.t;
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    (aux_3, aux_2, aux_1, aux_0, aux, aux_4) <- AND_64 mask mask;
     _0 <- aux_3;
     _1 <- aux_2;
     _2 <- aux_1;
     _3 <- aux_0;
    zf <- aux;
     _4 <- aux_4;
    return (zf);
  }
  
  proc __mask_cf (mask:W64.t) : bool = {
    var aux_0: bool;
    var aux: W64.t;
    
    var cf:bool;
    var t:W64.t;
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- (W64.of_int 0);
    t <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    (aux_0, aux) <- sbb_64 t mask false;
    cf <- aux_0;
    t <- aux;
    return (cf);
  }
  
  proc __cf_mask (cf:bool) : W64.t = {
    var aux_0: bool;
    var aux: W64.t;
    
    var mask:W64.t;
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- (W64.of_int 0);
    mask <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    (aux_0, aux) <- adc_64 mask (W64.of_int 0) cf;
    cf <- aux_0;
    mask <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- (- mask);
    mask <- aux;
    return (mask);
  }
  
  proc __addacc3 (a:W64.t Array3.t, b1:W64.t, b0:W64.t, k:int) : 
  W64.t Array3.t = {
    var aux: bool;
    var aux_0: W64.t;
    
    var cf:bool;
    
    LEAK.leakages <- LeakAddr([(k %% 3)]) :: LEAK.leakages;
    (aux, aux_0) <- adc_64 a.[(k %% 3)] b0 false;
    cf <- aux;
    LEAK.leakages <- LeakAddr([(k %% 3)]) :: LEAK.leakages;
    a.[(k %% 3)] <- aux_0;
    LEAK.leakages <- LeakAddr([((k + 1) %% 3)]) :: LEAK.leakages;
    (aux, aux_0) <- adc_64 a.[((k + 1) %% 3)] b1 cf;
    cf <- aux;
    LEAK.leakages <- LeakAddr([((k + 1) %% 3)]) :: LEAK.leakages;
    a.[((k + 1) %% 3)] <- aux_0;
    LEAK.leakages <- LeakAddr([((k + 2) %% 3)]) :: LEAK.leakages;
    (aux, aux_0) <- adc_64 a.[((k + 2) %% 3)] (W64.of_int 0) cf;
    cf <- aux;
    LEAK.leakages <- LeakAddr([((k + 2) %% 3)]) :: LEAK.leakages;
    a.[((k + 2) %% 3)] <- aux_0;
    return (a);
  }
  
  proc __addacc3x2 (a:W64.t Array3.t, x:W64.t, y:W64.t, k:int) : 
  W64.t Array3.t = {
    var aux_5: bool;
    var aux_4: bool;
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux_0: W64.t;
    var aux: W64.t;
    
    var b1:W64.t;
    var b0:W64.t;
    var t:W64.t;
    var cf:bool;
    var b2:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    (aux_0, aux) <- mulu_64 x y;
    b1 <- aux_0;
    b0 <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <- b0;
    t <- aux_0;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <- (b0 `<<` (W8.of_int 1));
    b0 <- aux_0;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    (aux_5, aux_4, aux_3, aux_2, aux_1, aux_0) <- SHLD_64 b1 t (W8.of_int 1);
     _0 <- aux_5;
    cf <- aux_4;
     _1 <- aux_3;
     _2 <- aux_2;
     _3 <- aux_1;
    b1 <- aux_0;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <- MOV_64 (W64.of_int 0);
    b2 <- aux_0;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    (aux_5, aux_0) <- adc_64 b2 b2 cf;
    cf <- aux_5;
    b2 <- aux_0;
    LEAK.leakages <- LeakAddr([(k %% 3)]) :: LEAK.leakages;
    (aux_5, aux_0) <- adc_64 a.[(k %% 3)] b0 false;
    cf <- aux_5;
    LEAK.leakages <- LeakAddr([(k %% 3)]) :: LEAK.leakages;
    a.[(k %% 3)] <- aux_0;
    LEAK.leakages <- LeakAddr([((k + 1) %% 3)]) :: LEAK.leakages;
    (aux_5, aux_0) <- adc_64 a.[((k + 1) %% 3)] b1 cf;
    cf <- aux_5;
    LEAK.leakages <- LeakAddr([((k + 1) %% 3)]) :: LEAK.leakages;
    a.[((k + 1) %% 3)] <- aux_0;
    LEAK.leakages <- LeakAddr([((k + 2) %% 3)]) :: LEAK.leakages;
    (aux_5, aux_0) <- adc_64 a.[((k + 2) %% 3)] b2 cf;
    cf <- aux_5;
    LEAK.leakages <- LeakAddr([((k + 2) %% 3)]) :: LEAK.leakages;
    a.[((k + 2) %% 3)] <- aux_0;
    return (a);
  }
}.

