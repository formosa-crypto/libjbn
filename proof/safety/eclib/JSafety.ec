(* Copy of eclib/JSafety.ec of the Jasmin branch safety-assert2 (MIT licence,
   Copyright (C) 2016 IMDEA Software Institute), which the safety extraction
   requires (`from Jasmin require import Jcheck JSafety`) and the released
   eclib (2026.09.0) does not have; easycrypt.project maps the Jasmin namespace
   to this directory as well (`idirs = Jasmin:eclib`), as formosa-libjade does. *)

require import AllCore IntDiv CoreMap List Distr StdBigop.
import Bigbool.


lemma BBAnd_big_foldr ['a] (F : 'a -> bool) (r : 'a list) :
  foldr (fun x0 acc => x0 /\ acc) true (map F r) =
  BBAnd.big predT F r.
    proof.
by rewrite /BBAnd.big filter_predT.    
  qed.
  
lemma and_iota (F : int -> bool) i l :
  foldr (fun x0 acc => x0 /\ acc) true (map F (iota_ i l)) <=>
  forall k, i <= k < i + l => F k.
    proof.
      rewrite BBAnd_big_foldr BBAnd.bigP filter_predT List.allP.
    smt( mem_iota).
  qed.