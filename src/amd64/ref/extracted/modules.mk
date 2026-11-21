# The modules of the abstract instantiation (libjbn_abs.jazz) and, for each,
# the namespace path and the procedures to extract (with their callees): read
# by this directory's Makefile (correctness extraction) and by
# proof/safety/Makefile (safety extraction).

XTR_MODULES = BNUTIL_bn_util BN_bn_base BNRND_bn_rnd BNMUL_bn_mul BNMULL_bn_mul_loop BNMULX_bn_mulx BNMULXL_bn_mulx_loop BNMULXR_bn_mulxr BNMULSEL_bn_mulsel BNMULREG_bn_mulreg BNKAR_bn_karatsuba BNE_bn_exp FP_fp_base FPM_fp_mont FPPM_fp_pm

BNUTIL_bn_util_NS  = UTIL::
BNUTIL_bn_util_FNS = __mask_zf __mask_cf __cf_mask __ncf_mask __addacc3 __addacc3x2

BN_bn_base_NS  = H::BN::
BN_bn_base_FNS = _load_ _store_ _eq_ _test0_ __copy _mov_ _cmov_ _cswap_cf_ _set0_ __cfill _or_mask_ _and_mask_ _set_err_ __carrypropU _addcU_ _addU_ _addc_ _add_ _subcU_ _subU_ _subc_ _sub_ _lt_cf_ _ltc_cf_ _negU_ _negcU_ _neg_ _negc_ _cnegU_ _caddU_ _cminusP_ _pack2_

BNRND_bn_rnd_NS  = H::RND::
BNRND_bn_rnd_FNS = _rnd_ _rsample_

BNMUL_bn_mul_NS  = H::MUL::UNR::
BNMUL_bn_mul_FNS = _os_muln_ _ps_muln_ _ps_sqrn_ _ps_ksqrn_ __mont_redM

BNMULL_bn_mul_loop_NS  = H::MUL::LOOP::
BNMULL_bn_mul_loop_FNS = _os_muln_ _os_sqrn_ __mont_redM

BNMULX_bn_mulx_NS  = H::MUL::XUNR::
BNMULX_bn_mulx_FNS = _os_muln_ _os_sqrn_ __mont_redM

BNMULXL_bn_mulx_loop_NS  = H::MUL::XLOOP::
BNMULXL_bn_mulx_loop_FNS = _os_muln_ _os_sqrn_ __mont_redM

BNMULXR_bn_mulxr_NS  = H::MUL::XREG::
BNMULXR_bn_mulxr_FNS = _os_muln_ _os_sqrn_ __mont_redM

BNMULSEL_bn_mulsel_NS  = H::MUL::
BNMULSEL_bn_mulsel_FNS = _muln_ _sqrn_ __mont_redM

BNMULREG_bn_mulreg_NS  = H::MULREG::
BNMULREG_bn_mulreg_FNS = _osreg_muln_

BNKAR_bn_karatsuba_NS  = KAR::
BNKAR_bn_karatsuba_FNS = _kar_muln_

BNE_bn_exp_NS  = H::EXP::
BNE_bn_exp_FNS = _expm_noct_ _expmU_noct_ _expm_ _expmU_ _expmLR_noct_

FP_fp_base_NS  = H::FP::
FP_fp_base_FNS = _chk_bnds_ _addm_ _addmU_ _subm_ _submU_ _mulm_ _mulmU_ _sqrm_ _sqrmU_ _invm_ _invmU_

FPM_fp_mont_NS  = H::FPM::
FPM_fp_mont_FNS = fun_muln fun_sqrn _redM_ _fromM_ _toM_ _ctx_init_

FPPM_fp_pm_NS  = H::FPPM::
FPPM_fp_pm_FNS = fun_muln fun_sqrn fun_red _redPM_ _fromM_ _toM_ _ctx_init_ _mulm_
