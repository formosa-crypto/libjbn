require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.

require import Array3 JBigNumber.

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
    var  _0:bool;
    
    mask <- (W64.of_int 0);
    ( _0, mask) <- sbb_64 mask (W64.of_int 0) cf;
    return (mask);
  }
  
  proc __ncf_mask (cf:bool) : W64.t = {
    
    var mask:W64.t;
    
    mask <@ __cf_mask (cf);
    mask <- NOT_64 mask;
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



(******************************************************************************
 **               Library LEMMAS                                             **
 **                                                                          **
 ******************************************************************************)


(** LOSSLESS lemmas *)
lemma __mask_zf_ll: islossless M.__mask_zf
by islossless.

lemma __mask_cf_ll: islossless M.__mask_cf
by islossless.

lemma __cf_mask_ll: islossless M.__cf_mask
by islossless.

lemma __ncf_mask_ll: islossless M.__ncf_mask
by islossless.

lemma __addacc3_ll: islossless M.__addacc3
by islossless.

lemma __addacc3x2_ll: islossless M.__addacc3x2
by islossless.

(** CORRECTNESS lemmas [hoare] *)
hoare __mask_zf_h _mask:
 M.__mask_zf : mask=_mask ==> res=(to_uint _mask = 0).
proof.
proc; wp; skip => />.
rewrite /AND_64 /rflags_of_bwop_w /flags_w /rflags_of_bwop /= /ZF_of.
by rewrite W64.to_uint_eq.
qed.

hoare __mask_cf_h _mask:
 M.__mask_cf : mask=_mask ==> res=(to_uint _mask <> 0).
proof.
proc; wp; skip => />.
rewrite subcE /borrow_sub /=.
smt(W64.to_uint_cmp).
qed.

hoare __cf_mask_h _cf:
 M.__cf_mask : cf=_cf ==> res=(W64.of_int (-b2i _cf)).
proof.
proc; wp; skip => />.
by rewrite subcE /=.
qed.

hoare __ncf_mask_h _cf:
 M.__ncf_mask : cf=_cf ==> res=(W64.of_int (-b2i (! _cf))).
proof.
proc; wp; call (__cf_mask_h _cf); skip => /> *.
rewrite /NOT_64; case: _cf => /= _;
 by rewrite W64.to_uint_eq W64.to_uint_invw /=.
qed.

(* obs: the final carry is discarded, hence the result is
   computed modulo [W64.modulus^3] *)
hoare __addacc3_h _a _b0 _b1 _k:
 M.__addacc3
 : a=_a /\ b0=_b0 /\ b1=_b1 /\ k=_k 
 ==> bn_seq [ res.[_k%%3]; res.[(_k+1)%%3]; res.[(_k+2)%%3] ]
     = (bn_seq [ _a.[_k%%3]; _a.[(_k+1)%%3]; _a.[(_k+2)%%3] ]
        + bn_seq [ _b0; _b1 ]) %% W64.modulus^3.
proof.
proc; wp; skip => />.
have H0: 0 <= _k %% 3 < 3 by smt().
have H1: 0 <= (_k+1) %% 3 < 3 by smt().
have H2: 0 <= (_k+2) %% 3 < 3 by smt().
have N01: (_k+1) %% 3 <> _k %% 3 by smt().
have N02: (_k+2) %% 3 <> _k %% 3 by smt().
have N12: (_k+2) %% 3 <> (_k+1) %% 3 by smt().
have N10: _k %% 3 <> (_k+1) %% 3 by smt().
have N20: _k %% 3 <> (_k+2) %% 3 by smt().
have N21: (_k+1) %% 3 <> (_k+2) %% 3 by smt().
rewrite !Array3.get_setE // ?N01 ?N02 ?N12 ?N10 ?N20 ?N21 /=.
by rewrite addc3P /bn_seq /=.
qed.

hoare __addacc3x2_h _a _x _y _k:
 M.__addacc3x2
 : a=_a /\ x=_x /\ y=_y /\ k=_k 
 ==> bn_seq [ res.[_k%%3]; res.[(_k+1)%%3]; res.[(_k+2)%%3] ]
     = (bn_seq [ _a.[_k%%3]; _a.[(_k+1)%%3]; _a.[(_k+2)%%3] ]
        + to_uint _x * to_uint _y * 2) %% W64.modulus^3.
proof.
proc.
seq 6: (a=_a /\ k=_k /\ bn_seq [b0; b1; b2] = to_uint _x * to_uint _y * 2).
 by wp; skip => />; rewrite /MOV_64 -(dbl_mulu _x _y).
wp; skip => &hr [-> [-> Hb]] /=.
have H0: 0 <= _k %% 3 < 3 by smt().
have H1: 0 <= (_k+1) %% 3 < 3 by smt().
have H2: 0 <= (_k+2) %% 3 < 3 by smt().
have N01: (_k+1) %% 3 <> _k %% 3 by smt().
have N02: (_k+2) %% 3 <> _k %% 3 by smt().
have N12: (_k+2) %% 3 <> (_k+1) %% 3 by smt().
have N10: _k %% 3 <> (_k+1) %% 3 by smt().
have N20: _k %% 3 <> (_k+2) %% 3 by smt().
have N21: (_k+1) %% 3 <> (_k+2) %% 3 by smt().
rewrite !Array3.get_setE // ?N01 ?N02 ?N12 ?N10 ?N20 ?N21 /=.
by rewrite addc3P Hb.
qed.

(* exact versions, assuming that no overflow occurs *)
hoare __addacc3_exact_h _a _b0 _b1 _k:
 M.__addacc3
 : a=_a /\ b0=_b0 /\ b1=_b1 /\ k=_k
   /\ bn_seq [ _a.[_k%%3]; _a.[(_k+1)%%3]; _a.[(_k+2)%%3] ]
      + bn_seq [ _b0; _b1 ] < W64.modulus^3
 ==> bn_seq [ res.[_k%%3]; res.[(_k+1)%%3]; res.[(_k+2)%%3] ]
     = bn_seq [ _a.[_k%%3]; _a.[(_k+1)%%3]; _a.[(_k+2)%%3] ]
       + bn_seq [ _b0; _b1 ].
proof.
conseq (__addacc3_h _a _b0 _b1 _k) => //.
move=> &hr [_ [_ [_ [_ Hb]]]] r ->.
have [Ha _] := bn_seq_cmp [_a.[_k %% 3]; _a.[(_k + 1) %% 3]; _a.[(_k + 2) %% 3]].
have [Hc _] := bn_seq_cmp [_b0; _b1].
rewrite modz_small // StdOrder.IntOrder.ger0_norm 1:StdOrder.IntOrder.expr_ge0 //.
by split; [apply addz_ge0 | move=> _].
qed.

hoare __addacc3x2_exact_h _a _x _y _k:
 M.__addacc3x2
 : a=_a /\ x=_x /\ y=_y /\ k=_k
   /\ bn_seq [ _a.[_k%%3]; _a.[(_k+1)%%3]; _a.[(_k+2)%%3] ]
      + to_uint _x * to_uint _y * 2 < W64.modulus^3
 ==> bn_seq [ res.[_k%%3]; res.[(_k+1)%%3]; res.[(_k+2)%%3] ]
     = bn_seq [ _a.[_k%%3]; _a.[(_k+1)%%3]; _a.[(_k+2)%%3] ]
       + to_uint _x * to_uint _y * 2.
proof.
conseq (__addacc3x2_h _a _x _y _k) => //.
move=> &hr [_ [_ [_ [_ Hb]]]] r ->.
have [Ha _] := bn_seq_cmp [_a.[_k %% 3]; _a.[(_k + 1) %% 3]; _a.[(_k + 2) %% 3]].
have Hc: 0 <= to_uint _x * to_uint _y * 2.
 apply StdOrder.IntOrder.mulr_ge0 => //.
 by apply StdOrder.IntOrder.mulr_ge0; [case: (W64.to_uint_cmp _x) | case: (W64.to_uint_cmp _y)].
rewrite modz_small // StdOrder.IntOrder.ger0_norm 1:StdOrder.IntOrder.expr_ge0 //.
by split; [apply addz_ge0 | move=> _].
qed.

(** CORRECTNESS lemmas [phoare] *)
phoare __mask_zf_ph _mask:
 [ M.__mask_zf
 : mask=_mask ==> res=(to_uint _mask = 0)
 ] = 1%r
by conseq __mask_zf_ll (__mask_zf_h _mask).

phoare __mask_cf_ph _mask:
 [ M.__mask_cf
 : mask=_mask ==> res=(to_uint _mask <> 0)
 ] = 1%r
by conseq __mask_cf_ll (__mask_cf_h _mask).

phoare __cf_mask_ph _cf:
 [ M.__cf_mask 
 : cf=_cf ==> res=(W64.of_int (-b2i _cf))
 ] = 1%r
by conseq __cf_mask_ll (__cf_mask_h _cf).

phoare __ncf_mask_ph _cf:
 [ M.__ncf_mask 
 : cf=_cf ==> res=(W64.of_int (-b2i (! _cf)))
 ] = 1%r
by conseq __ncf_mask_ll (__ncf_mask_h _cf).

phoare __addacc3_ph _a _b0 _b1 _k:
 [ M.__addacc3
 : a=_a /\ b0=_b0 /\ b1=_b1 /\ k=_k 
 ==> bn_seq [ res.[_k%%3]; res.[(_k+1)%%3]; res.[(_k+2)%%3] ]
     = (bn_seq [ _a.[_k%%3]; _a.[(_k+1)%%3]; _a.[(_k+2)%%3] ]
        + bn_seq [ _b0; _b1 ]) %% W64.modulus^3
 ] = 1%r
by conseq __addacc3_ll (__addacc3_h _a _b0 _b1 _k).

phoare __addacc3x2_ph _a _x _y _k:
 [ M.__addacc3x2
 : a=_a /\ x=_x /\ y=_y /\ k=_k 
 ==> bn_seq [ res.[_k%%3]; res.[(_k+1)%%3]; res.[(_k+2)%%3] ]
     = (bn_seq [ _a.[_k%%3]; _a.[(_k+1)%%3]; _a.[(_k+2)%%3] ]
        + to_uint _x * to_uint _y * 2) %% W64.modulus^3
 ] = 1%r
by conseq __addacc3x2_ll (__addacc3x2_h _a _x _y _k).
