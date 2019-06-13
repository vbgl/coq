#!/usr/bin/env bash

# This is the basic overlay set for repositories in the CI.

# Maybe we should just use Ruby to have real objects...

# : "${foo:=bar}" sets foo to "bar" if it is unset or null

########################################################################
# MathComp
########################################################################
: "${mathcomp_CI_REF:=3df66cf26c7a50cfbfbb837659658e49010dde1d}"
: "${mathcomp_CI_GITURL:=https://github.com/math-comp/math-comp}"
: "${mathcomp_CI_ARCHIVEURL:=${mathcomp_CI_GITURL}/archive}"

: "${fourcolor_CI_REF:=0851d498d9a06ab81cf978494b6d41fbeb5f6631}"
: "${fourcolor_CI_GITURL:=https://github.com/math-comp/fourcolor}"
: "${fourcolor_CI_ARCHIVEURL:=${fourcolor_CI_GITURL}/archive}"

: "${oddorder_CI_REF:=ca602a4638a9fe8ac30780095543d861f60fbfa0}"
: "${oddorder_CI_GITURL:=https://github.com/math-comp/odd-order}"
: "${oddorder_CI_ARCHIVEURL:=${oddorder_CI_GITURL}/archive}"

########################################################################
# UniMath
########################################################################
: "${unimath_CI_REF:=d1977361edf6b7719ebcecbb54289282e34c8aaf}"
: "${unimath_CI_GITURL:=https://github.com/UniMath/UniMath}"
: "${unimath_CI_ARCHIVEURL:=${unimath_CI_GITURL}/archive}"

########################################################################
# Unicoq + Mtac2
########################################################################
: "${unicoq_CI_REF:=1bfb474f11123f277722eaeaca1b28eaa4abb633}"
: "${unicoq_CI_GITURL:=https://github.com/unicoq/unicoq}"
: "${unicoq_CI_ARCHIVEURL:=${unicoq_CI_GITURL}/archive}"

: "${mtac2_CI_REF:=master}"
: "${mtac2_CI_GITURL:=https://github.com/Mtac2/Mtac2}"
: "${mtac2_CI_ARCHIVEURL:=${mtac2_CI_GITURL}/archive}"

########################################################################
# Mathclasses + Corn
########################################################################
: "${math_classes_CI_REF:=4d19c6bf11739a7541c8c3afed871603d2b4395e}"
: "${math_classes_CI_GITURL:=https://github.com/coq-community/math-classes}"
: "${math_classes_CI_ARCHIVEURL:=${math_classes_CI_GITURL}/archive}"

: "${Corn_CI_REF:=db29aed4b2d378721715bfff258e59968207331f}"
: "${Corn_CI_GITURL:=https://github.com/coq-community/corn}"
: "${Corn_CI_ARCHIVEURL:=${Corn_CI_GITURL}/archive}"

########################################################################
# Iris
########################################################################

# NB: stdpp and Iris refs are gotten from the opam files in the Iris
# and lambdaRust repos respectively.
: "${stdpp_CI_GITURL:=https://gitlab.mpi-sws.org/robbertkrebbers/coq-stdpp}"
: "${stdpp_CI_ARCHIVEURL:=${stdpp_CI_GITURL}/-/archive}"

: "${Iris_CI_GITURL:=https://gitlab.mpi-sws.org/FP/iris-coq}"
: "${Iris_CI_ARCHIVEURL:=${Iris_CI_GITURL}/-/archive}"

: "${lambdaRust_CI_REF:=8304869457a6453db081beb31aecfa194bc7048b}"
: "${lambdaRust_CI_GITURL:=https://gitlab.mpi-sws.org/FP/LambdaRust-coq}"
: "${lambdaRust_CI_ARCHIVEURL:=${lambdaRust_CI_GITURL}/-/archive}"

########################################################################
# HoTT
########################################################################
: "${HoTT_CI_REF:=93145f51419930b7d47c4231cf1010abe84b2f40}"
: "${HoTT_CI_GITURL:=https://github.com/HoTT/HoTT}"
: "${HoTT_CI_ARCHIVEURL:=${HoTT_CI_GITURL}/archive}"

########################################################################
# CoqHammer
########################################################################
: "${coqhammer_CI_REF:=6fb6a92c83cdfa4f629758737e464c20249510cc}"
: "${coqhammer_CI_GITURL:=https://github.com/lukaszcz/coqhammer}"
: "${coqhammer_CI_ARCHIVEURL:=${coqhammer_CI_GITURL}/archive}"

########################################################################
# GeoCoq
########################################################################
: "${GeoCoq_CI_REF:=2b4cf1129fd566e14a64eaa651e941b90b1925e9}"
: "${GeoCoq_CI_GITURL:=https://github.com/GeoCoq/GeoCoq}"
: "${GeoCoq_CI_ARCHIVEURL:=${GeoCoq_CI_GITURL}/archive}"

########################################################################
# Flocq
########################################################################
: "${Flocq_CI_REF:=3cba812be9541200ff1c353814b2011a2909bc4b}"
: "${Flocq_CI_GITURL:=https://gitlab.inria.fr/flocq/flocq}"
: "${Flocq_CI_ARCHIVEURL:=${Flocq_CI_GITURL}/-/archive}"

########################################################################
# Coquelicot
########################################################################
: "${coquelicot_CI_REF:=b488d25b68759b0ede744079e574f09a339cc894}"
: "${coquelicot_CI_GITURL:=https://gitlab.inria.fr/coquelicot/coquelicot}"
: "${coquelicot_CI_ARCHIVEURL:=${coquelicot_CI_GITURL}/-/archive}"

########################################################################
# CompCert
########################################################################
: "${compcert_CI_REF:=ddb2c968e6c57d2117434f169471d87f643d831a}"
: "${compcert_CI_GITURL:=https://github.com/AbsInt/CompCert}"
: "${compcert_CI_ARCHIVEURL:=${compcert_CI_GITURL}/archive}"

########################################################################
# VST
########################################################################
: "${vst_CI_REF:=1b6854c822156c81cd5add0b25e40a8e6ba34e11}"
: "${vst_CI_GITURL:=https://github.com/PrincetonUniversity/VST}"
: "${vst_CI_ARCHIVEURL:=${vst_CI_GITURL}/archive}"

########################################################################
# cross-crypto
########################################################################
: "${cross_crypto_CI_REF:=ab65a8834528d677f8f59477a4e15d8ee4f2560e}"
: "${cross_crypto_CI_GITURL:=https://github.com/mit-plv/cross-crypto}"
: "${cross_crypto_CI_ARCHIVEURL:=${cross_crypto_CI_GITURL}/archive}"

########################################################################
# fiat_parsers
########################################################################
: "${fiat_parsers_CI_REF:=b8accbfda377ba82298ff7a279cbee5c2170aeda}"
: "${fiat_parsers_CI_GITURL:=https://github.com/mit-plv/fiat}"
: "${fiat_parsers_CI_ARCHIVEURL:=${fiat_parsers_CI_GITURL}/archive}"

########################################################################
# fiat_crypto
########################################################################
: "${fiat_crypto_CI_REF:=8517e5f3afe079e7b42220088ca0c8e79e5e4343}"
: "${fiat_crypto_CI_GITURL:=https://github.com/mit-plv/fiat-crypto}"
: "${fiat_crypto_CI_ARCHIVEURL:=${fiat_crypto_CI_GITURL}/archive}"

########################################################################
# fiat_crypto_legacy
########################################################################
: "${fiat_crypto_legacy_CI_REF:=847b18bf8f38f7262331181f25ca96aee0423f52}"
: "${fiat_crypto_legacy_CI_GITURL:=https://github.com/mit-plv/fiat-crypto}"
: "${fiat_crypto_legacy_CI_ARCHIVEURL:=${fiat_crypto_legacy_CI_GITURL}/archive}"

########################################################################
# coq_dpdgraph
########################################################################
: "${coq_dpdgraph_CI_REF:=879fbcd7e901e60d34e3bee05c6ae9c86cb3f32f}"
: "${coq_dpdgraph_CI_GITURL:=https://github.com/Karmaki/coq-dpdgraph}"
: "${coq_dpdgraph_CI_ARCHIVEURL:=${coq_dpdgraph_CI_GITURL}/archive}"

########################################################################
# CoLoR
########################################################################
: "${color_CI_REF:=b6c9486a8a6379a5faad8f47afda3dc3f7fcbb15}"
: "${color_CI_GITURL:=https://github.com/fblanqui/color}"
: "${color_CI_ARCHIVEURL:=${color_CI_GITURL}/archive}"

########################################################################
# SF
########################################################################
: "${sf_lf_CI_TARURL:=https://www.cis.upenn.edu/~bcpierce/sf/lf-current/lf.tgz}"
: "${sf_plf_CI_TARURL:=https://www.cis.upenn.edu/~bcpierce/sf/plf-current/plf.tgz}"
: "${sf_vfa_CI_TARURL:=https://www.cis.upenn.edu/~bcpierce/sf/vfa-current/vfa.tgz}"

########################################################################
# TLC
########################################################################
: "${tlc_CI_REF:=6dc379c6c7a306be6b7ef1b3774bdb9ea2c94330}"
: "${tlc_CI_GITURL:=https://gforge.inria.fr/git/tlc/tlc}"

########################################################################
# Bignums
########################################################################
: "${bignums_CI_REF:=0cd435d0a3c731605536c83d0a731c3fc336cce7}"
: "${bignums_CI_GITURL:=https://github.com/coq/bignums}"
: "${bignums_CI_ARCHIVEURL:=${bignums_CI_GITURL}/archive}"

########################################################################
# bedrock2
########################################################################
: "${bedrock2_CI_REF:=master}"
: "${bedrock2_CI_GITURL:=https://github.com/mit-plv/bedrock2}"
: "${bedrock2_CI_ARCHIVEURL:=${bedrock2_CI_GITURL}/archive}"

########################################################################
# Equations
########################################################################
: "${equations_CI_REF:=b020ec613736de280554f84812b905bc7467be60}"
: "${equations_CI_GITURL:=https://github.com/mattam82/Coq-Equations}"
: "${equations_CI_ARCHIVEURL:=${equations_CI_GITURL}/archive}"

########################################################################
# Elpi
########################################################################
: "${elpi_CI_REF:=1c43ef1311f83d9b2499a4d6a22ba34dece9144f}"
: "${elpi_CI_GITURL:=https://github.com/LPCIC/coq-elpi}"
: "${elpi_CI_ARCHIVEURL:=${elpi_CI_GITURL}/archive}"

########################################################################
# fcsl-pcm
########################################################################
: "${fcsl_pcm_CI_REF:=0b889701e2c38df031fc0c763d1b0d5c8e6c795d}"
: "${fcsl_pcm_CI_GITURL:=https://github.com/imdea-software/fcsl-pcm}"
: "${fcsl_pcm_CI_ARCHIVEURL:=${fcsl_pcm_CI_GITURL}/archive}"

########################################################################
# ext-lib
########################################################################
: "${ext_lib_CI_REF:=f27a18a679b09b884f3ab63581c0048de9fa9089}"
: "${ext_lib_CI_GITURL:=https://github.com/coq-ext-lib/coq-ext-lib}"
: "${ext_lib_CI_ARCHIVEURL:=${ext_lib_CI_GITURL}/archive}"

########################################################################
# simple-io
########################################################################
: "${simple_io_CI_REF:=533e02ed746eeb0e1600122c82ff62d8d776da60}"
: "${simple_io_CI_GITURL:=https://github.com/Lysxia/coq-simple-io}"
: "${simple_io_CI_ARCHIVEURL:=${simple_io_CI_GITURL}/archive}"

########################################################################
# quickchick
########################################################################
: "${quickchick_CI_REF:=9d3914b47aea20f7b97ac510903cd9d43fc4a2c1}"
: "${quickchick_CI_GITURL:=https://github.com/QuickChick/QuickChick}"
: "${quickchick_CI_ARCHIVEURL:=${quickchick_CI_GITURL}/archive}"

########################################################################
# menhirlib
########################################################################
: "${menhirlib_CI_REF:=ca0655b2f96057a271fb5c9a254a38d195b4a7f9}"
: "${menhirlib_CI_GITURL:=https://gitlab.inria.fr/fpottier/coq-menhirlib}"
: "${menhirlib_CI_ARCHIVEURL:=${menhirlib_CI_GITURL}/-/archive}"

########################################################################
# aac_tactics
########################################################################
: "${aac_tactics_CI_REF:=4869852b949e4256310a484e8282779b5c607f2f}"
: "${aac_tactics_CI_GITURL:=https://github.com/coq-community/aac-tactics}"
: "${aac_tactics_CI_ARCHIVEURL:=${aac_tactics_CI_GITURL}/archive}"

########################################################################
# paramcoq
########################################################################
: "${paramcoq_CI_REF:=1aeb53dc6af9b17979a600bc91acacc321977444}"
: "${paramcoq_CI_GITURL:=https://github.com/coq-community/paramcoq}"
: "${paramcoq_CI_ARCHIVEURL:=${paramcoq_CI_GITURL}/archive}"

########################################################################
# relation_algebra
########################################################################
: "${relation_algebra_CI_REF:=aaab2097f7da6f0909f01367e3abd77f87e0005b}"
: "${relation_algebra_CI_GITURL:=https://github.com/damien-pous/relation-algebra}"
: "${relation_algebra_CI_ARCHIVEURL:=${relation_algebra_CI_GITURL}/archive}"

########################################################################
# StructTact + InfSeqExt + Cheerios + Verdi + Verdi Raft
########################################################################
: "${struct_tact_CI_REF:=4b9229f9678c7360d07a9e96318950800b369257}"
: "${struct_tact_CI_GITURL:=https://github.com/uwplse/StructTact}"
: "${struct_tact_CI_ARCHIVEURL:=${struct_tact_CI_GITURL}/archive}"

: "${inf_seq_ext_CI_REF:=dd91f4eb8be379bb1591fc565b376727ef97abe6}"
: "${inf_seq_ext_CI_GITURL:=https://github.com/DistributedComponents/InfSeqExt}"
: "${inf_seq_ext_CI_ARCHIVEURL:=${inf_seq_ext_CI_GITURL}/archive}"

: "${cheerios_CI_REF:=f512bfcb9c8d0b211a72b9f2b195ad46ced7df76}"
: "${cheerios_CI_GITURL:=https://github.com/uwplse/cheerios}"
: "${cheerios_CI_ARCHIVEURL:=${cheerios_CI_GITURL}/archive}"

: "${verdi_CI_REF:=163b9d0039ba6de2c72b77728136e45ba3f93623}"
: "${verdi_CI_GITURL:=https://github.com/uwplse/verdi}"
: "${verdi_CI_ARCHIVEURL:=${verdi_CI_GITURL}/archive}"

: "${verdi_raft_CI_REF:=3fc8d5223865e80e97d6f90ff39700f8977a1eae}"
: "${verdi_raft_CI_GITURL:=https://github.com/uwplse/verdi-raft}"
: "${verdi_raft_CI_ARCHIVEURL:=${verdi_raft_CI_GITURL}/archive}"

########################################################################
# stdlib2
########################################################################
: "${stdlib2_CI_REF:=master}"
: "${stdlib2_CI_GITURL:=https://github.com/coq/stdlib2}"
: "${stdlib2_CI_ARCHIVEURL:=${stdlib2_CI_GITURL}/archive}"

########################################################################
# argosy
########################################################################
: "${argosy_CI_REF:=68674f1c36c812b088d4429792446d018dc27dc2}"
: "${argosy_CI_GITURL:=https://github.com/mit-pdos/argosy}"
: "${argosy_CI_ARCHIVEURL:=${argosy_CI_GITURL}/archive}"
