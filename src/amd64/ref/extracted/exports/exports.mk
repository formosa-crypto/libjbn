# The export templates (src/amd64/ref/*_export@2n.jinc), each instantiated by
# its harness exports/<template>.jazz, and the entry points to extract: read
# by proof/safety/Makefile (safety extraction only). A module name is
# <QUAL>_<template>.

EXPORT_MODULES = EXBN_bn_base_export EXMUL_bn_mul_export EXMULL_bn_mul_loop_export \
                 EXKAR_bn_karatsuba_export EXKSQR_bn_ksqr_export \
                 EXFPC_fp_mont_ctx_export EXFP_fp_mont_export

EXBN_bn_base_export_FNS       = bn_eq bn_test0 bn_copy bn_set0 bn_addU bn_subU
EXMUL_bn_mul_export_FNS       = bn_ps_muln bn_ps_sqrn bn_os_muln
EXMULL_bn_mul_loop_export_FNS = bn_os_muln bn_os_sqrn
EXKAR_bn_karatsuba_export_FNS = bn_kar_muln
EXKSQR_bn_ksqr_export_FNS    = bn_kar_sqrn
EXFPC_fp_mont_ctx_export_FNS  = fpc_ctx_init fpc_add fpc_sub fpc_mul fpc_sqr fpc_exp \
                                fpc_exp_ladder fpc_exp_noct fpc_inv fpc_toM fpc_fromM
EXFP_fp_mont_export_FNS       = fp_add fp_sub fp_mul fp_sqr fp_exp_noct fp_expLR_noct \
                                fp_exp fp_exp_ladder fp_inv fp_toM fp_fromM
