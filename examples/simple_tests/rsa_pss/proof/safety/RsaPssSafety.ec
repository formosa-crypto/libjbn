(* Safety of the RSA example (../../rsa2048.jazz): its own procedures and
   the three exports, from the library procedures' lemmas of
   RsaPssSafety_inst.ec. The code is straight-line at concrete sizes: each
   proof is a chain of calls, the initialisation goals close by the hints of
   the `safety` database. *)
require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.
from Jasmin require import Jcheck JSafety JByte_array JMemory.
require import ByteArrayInit JbnSafetyLib.
require import RsaPssXtr_safety RsaPssSafety_inst.
require import SBArray256_128 SBArray288_256 SBArray512_256 SBArray520_128 SBArray520_256 SBArray640_128 SBArray1032_256 SBArray1032_512 SBArray1064_32 SBArray1064_1032 SBArray1424_128 SBArray1424_520.

(* the hints of the safety database for the sub-arrays *)
clone SubByteArrayInit as SBI256_128 with theory SB <- SBArray256_128.
clone SubByteArrayInit as SBI288_256 with theory SB <- SBArray288_256.
clone SubByteArrayInit as SBI512_256 with theory SB <- SBArray512_256.
clone SubByteArrayInit as SBI520_128 with theory SB <- SBArray520_128.
clone SubByteArrayInit as SBI520_256 with theory SB <- SBArray520_256.
clone SubByteArrayInit as SBI640_128 with theory SB <- SBArray640_128.
clone SubByteArrayInit as SBI1032_256 with theory SB <- SBArray1032_256.
clone SubByteArrayInit as SBI1032_512 with theory SB <- SBArray1032_512.
clone SubByteArrayInit as SBI1064_32 with theory SB <- SBArray1064_32.
clone SubByteArrayInit as SBI1064_1032 with theory SB <- SBArray1064_1032.
clone SubByteArrayInit as SBI1424_128 with theory SB <- SBArray1424_128.
clone SubByteArrayInit as SBI1424_520 with theory SB <- SBArray1424_520.

lemma h__RSA___ctx_init_N_safety _ctx _b_ctx _n _b_n : h__RSA___ctx_init_N_spec _ctx _b_ctx _n _b_n.
proof.
hint +safety.
rewrite /h__RSA___ctx_init_N_spec; proc.
wp; ecall (h__FPM___ctx_init__safety param b_param param_0 ((BArray256.init_arr (W8.of_int 255)))).
by auto => />.
qed.

lemma h__RSA___ctx_init_P_safety _ctx _b_ctx _p _b_p : h__RSA___ctx_init_P_spec _ctx _b_ctx _p _b_p.
proof.
hint +safety.
rewrite /h__RSA___ctx_init_P_spec; proc.
wp; ecall (h__H__FPM___ctx_init__safety param b_param param_0 ((BArray128.init_arr (W8.of_int 255)))).
by auto => />.
qed.

lemma h__RSA____RSA_expand_pk_safety _pK _b_PK _pk _b_pk : h__RSA____RSA_expand_pk_spec _pK _b_PK _pk _b_pk.
proof.
hint +safety.
rewrite /h__RSA____RSA_expand_pk_spec; proc.
unroll for ^while.
wp; ecall (h__RSA___ctx_init_N_safety param b_param param_0 b_param_0).
by auto => /> *; smt(BL256.is_init_sub BL288.is_init_sub BL640.is_init_sub BL1064.is_init_sub BL1424.is_init_sub).
qed.

lemma h__RSA____RSA_expand_sk_safety _sK _b_SK _sk _b_sk : h__RSA____RSA_expand_sk_spec _sK _b_SK _sk _b_sk.
proof.
hint +safety.
rewrite /h__RSA____RSA_expand_sk_spec; proc.
wp; ecall (h__H__BN___mov__safety param_7 b_param_7 param_8 b_param_8).
wp; ecall (h__H__BN___mov__safety param_5 b_param_5 param_6 b_param_6).
wp; ecall (h__H__BN___mov__safety param_3 b_param_3 param_4 b_param_4).
wp; ecall (h__RSA___ctx_init_P_safety param_1 b_param_1 param_2 b_param_2).
wp; ecall (h__RSA___ctx_init_P_safety param b_param param_0 b_param_0).
by auto => /> *; smt(BL256.is_init_sub BL288.is_init_sub BL640.is_init_sub BL1064.is_init_sub BL1424.is_init_sub).
qed.

lemma h__RSA____RSAVP1_safety _y _b_y _s _b_s _pk _b_pk : h__RSA____RSAVP1_spec _y _b_y _s _b_s _pk _b_pk.
proof.
hint +safety.
rewrite /h__RSA____RSAVP1_spec; proc.
wp; ecall (h__FPM___fromM__safety param_7 ((BArray256.init_arr (W8.of_int 255))) param_8 b_param_4).
wp; ecall (h__FPM__EXPE___expmLR_noct__safety param_3 b_param_1 param_4 ((BArray256.init_arr (W8.of_int 255))) param_5 b_param_2 param_6 b_param_3).
wp; ecall (h__FPM___toM__safety param_1 ((BArray256.init_arr (W8.of_int 255))) param_2 b_param_0).
wp; ecall (h__BN___mov__safety param b_param param_0 ((BArray256.init_arr (W8.of_int 255)))).
by auto => /> *; smt(BL256.is_init_sub BL288.is_init_sub BL640.is_init_sub BL1064.is_init_sub BL1424.is_init_sub).
qed.

lemma h__RSA___crt_exp_safety _r _b_r _c _b_c _dX _b_dX _ctxX _b_ctxX : h__RSA___crt_exp_spec _r _b_r _c _b_c _dX _b_dX _ctxX _b_ctxX.
proof.
hint +safety.
rewrite /h__RSA___crt_exp_spec; proc.
wp; ecall (h__H__FPM__EXP___expm__safety param_6 b_param_0 param_7 ((BArray128.init_arr (W8.of_int 255))) param_8 ((BArray128.init_arr (W8.of_int 255))) param_9 ((BArray520.init_arr (W8.of_int 255)))).
wp; ecall (h__H__FPM___toM__safety param_4 ((BArray128.init_arr (W8.of_int 255))) param_5 ((BArray520.init_arr (W8.of_int 255)))).
wp; ecall (h__H__FPM___toM__safety param_2 ((BArray128.init_arr (W8.of_int 255))) param_3 ((BArray520.init_arr (W8.of_int 255)))).
wp; ecall (h__H__FPM___redM__safety param b_param param_0 ((BArray256.init_arr (W8.of_int 255))) param_1 ((BArray520.init_arr (W8.of_int 255)))).
by auto => />.
qed.

lemma h__RSA____RSASP1_crt_safety _s _b_s _sk _b_sk : h__RSA____RSASP1_crt_spec _s _b_s _sk _b_sk.
proof.
hint +safety.
rewrite /h__RSA____RSASP1_crt_spec; proc.
wp; ecall (h__BN___addU__safety param_23 ((BArray256.init_arr (W8.of_int 255))) param_24 b_param_14).
wp; ecall (h__H__BN___set0__safety param_22 b_param_13).
wp; ecall (h__H__MUL___muln__safety param_19 ((BArray256.init_arr (W8.of_int 255))) param_20 ((BArray128.init_arr (W8.of_int 255))) param_21 b_param_12).
wp; ecall (h__H__FPM___mulmU__safety param_16 ((BArray128.init_arr (W8.of_int 255))) param_17 b_param_10 param_18 b_param_11).
wp; ecall (h__H__FPM___submU__safety param_13 ((BArray128.init_arr (W8.of_int 255))) param_14 ((BArray128.init_arr (W8.of_int 255))) param_15 b_param_9).
wp; ecall (h__H__FPM___toM__safety param_11 ((BArray128.init_arr (W8.of_int 255))) param_12 b_param_8).
wp; ecall (h__H__BN___mov__safety param_9 b_param_6 param_10 b_param_7).
wp; ecall (h__H__FPM___fromM__safety param_7 ((BArray128.init_arr (W8.of_int 255))) param_8 b_param_5).
wp; ecall (h__RSA___crt_exp_safety param_3 b_param_2 param_4 ((BArray256.init_arr (W8.of_int 255))) param_5 b_param_3 param_6 b_param_4).
wp; ecall (h__RSA___crt_exp_safety param b_param param_0 ((BArray256.init_arr (W8.of_int 255))) param_1 b_param_0 param_2 b_param_1).
by auto => /> *; smt(BL256.is_init_sub BL288.is_init_sub BL640.is_init_sub BL1064.is_init_sub BL1424.is_init_sub).
qed.

lemma rsa_init_safety _pk _b_pk _sk _b_sk : rsa_init_spec _pk _b_pk _sk _b_sk.
proof.
hint +safety.
rewrite /rsa_init_spec; proc.
wp; ecall (h__RSA____RSA_expand_sk_safety param_1 b_param_0 param_2 ((BArray640.init_arr (W8.of_int 255)))).
wp; ecall (h__RSA____RSA_expand_pk_safety param b_param param_0 ((BArray288.init_arr (W8.of_int 255)))).
by auto => />.
qed.

lemma rsa_enc_safety _c _b_c _m _b_m _pk _b_pk : rsa_enc_spec _c _b_c _m _b_m _pk _b_pk.
proof.
hint +safety.
rewrite /rsa_enc_spec; proc.
wp; ecall (h__RSA____RSAVP1_safety param b_param param_0 ((BArray256.init_arr (W8.of_int 255))) param_1 ((BArray1064.init_arr (W8.of_int 255)))).
by auto => />.
qed.

lemma rsa_dec_safety _m _b_m _c _b_c _sk _b_sk : rsa_dec_spec _m _b_m _c _b_c _sk _b_sk.
proof.
hint +safety.
rewrite /rsa_dec_spec; proc.
wp; ecall (h__RSA____RSASP1_crt_safety param_1 ((BArray256.init_arr (W8.of_int 255))) param_2 ((BArray1424.init_arr (W8.of_int 255)))).
wp; ecall (h__BN___mov__safety param b_param param_0 ((BArray256.init_arr (W8.of_int 255)))).
by auto => />.
qed.

