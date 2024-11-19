
theory  FixInvalidDirtyEvictFilled imports  BaseProof1.BasicInvariants  begin
sledgehammer_params[timeout=10, dont_minimize, "try0" = false]
lemma snps2_HostInvalidDirtyEvict: shows "snps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = snps2 T"
apply(case_tac "program1 T")
by simp+
lemma snps1_HostInvalidDirtyEvict: shows "snps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = snps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqs2_HostInvalidDirtyEvict: shows "reqs2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = reqs2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps2_HostInvalidDirtyEvict: shows "snpresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = snpresps2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps1_HostInvalidDirtyEvict: shows "snpresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = snpresps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps2_HostInvalidDirtyEvict: shows "reqresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = reqresps2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_HostInvalidDirtyEvict: shows "reqresps1 T = [] \<Longrightarrow> length (reqresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])) \<le> 1"
by simp
lemma dthdatas1_HostInvalidDirtyEvict: shows "dthdatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = dthdatas1 T"
apply(case_tac "program1 T")
by simp+
lemma dthdatas2_HostInvalidDirtyEvict: shows "dthdatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = dthdatas2 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas1_HostInvalidDirtyEvict: shows "htddatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = htddatas1 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas2_HostInvalidDirtyEvict: shows "htddatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = htddatas2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_HostInvalidDirtyEvict_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma reqresps1_HostInvalidDirtyEvict_aux1: shows "reqresps1 T = reqresps1 (T [ Dev1 +=d2hd dthd] [ -=i 0])"
apply(case_tac "program1 T")
by simp+
lemma nextEvict_HostInvalidDirtyEvict_invariant: shows"nextEvict T 0 = nextEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
by simp
lemma CSTATE_HostInvalidDirtyEvict_otherside_invariant2: shows
" CSTATE X ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 = CSTATE X T 1"
by simp
lemma CSTATE_HostInvalidDirtyEvict_otherside_invariant3: shows
" CSTATE X ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 = CSTATE X T 0"
by simp
lemma HostInvalidDirtyEvict_nextGOPendingIs_otherside: shows 
"nextGOPendingIs X ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 = nextGOPendingIs X T 1"
by simp
lemma HostInvalidDirtyEvict_nextEvict_otherside: shows 
"nextEvict  ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 = nextEvict T 1"
by simp
lemma HostInvalidDirtyEvict_nextHTDDataPending_otherside: shows 
"nextDTHDataPending  ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 = nextDTHDataPending T 1"
by simp
lemma HostInvalidDirtyEvict_nextSnpRespIs_otherside: shows 
"nextSnpRespIs X  ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 = nextSnpRespIs X T 1"
by simp
lemma HostInvalidDirtyEvict_nextSnpRespIs_sameside: shows 
"nextSnpRespIs X  ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 = nextSnpRespIs X T 0"
by simp
lemma HostInvalidDirtyEvict_HSTATE: shows "HSTATE IB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) "
apply(case_tac "program1 T")
apply  simp+
done
lemma HostInvalidDirtyEvict_nextLoad: shows "nextLoad ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) i = nextLoad T i"
apply(case_tac "program1 T")
by simp+
lemma nextStore_nextEvict_exclusive: shows "nextEvict T i \<Longrightarrow> \<not>nextStore T i"
apply(induct "program1 T")
apply simp
apply (metis One_nat_def startsEvict.elims(2) startsStore.simps(4) zero_neq_one)
apply(case_tac a)
apply (metis nextEvict_def nextStore_def startsEvict.elims(2) startsStore.simps(4))
apply (metis nextEvict_def nextStore_def startsEvict.elims(2) startsStore.simps(4))
by (metis nextEvict_def nextStore_def startsEvict.elims(2) startsStore.simps(4))
lemma reqlength1_minus: shows "length (reqs1 T) \<le> 1 \<Longrightarrow> reqs1  ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply(cases "reqs1 T")
apply simp+
done
lemma HostInvalidDirtyEvict': shows "reqs1 (T [ 5 sHost= SharedM] [ 0 +=reqresp GO_WritePullDrop Invalid txid]) = reqs1 T"
by simp
lemma empty_reqs_nextReqIs: shows "reqs1 T  = [] \<Longrightarrow> \<not> nextReqIs X T 0"
by simp
lemma aux_r34_5: "reqresps1 T = [] \<Longrightarrow> nextGOPendingIs y  ( T  [ 0 +=reqresp y x txid]) 0"
apply simp
done
lemma aux_r34_4: "reqresps1 T = [] \<Longrightarrow>   (nextGOPendingIs y  ( T [ z sHost= t] [ 0 +=reqresp y x txid]) 0)"
apply simp
done
lemma aux_r34_3: "reqresps1 T = [] \<Longrightarrow> nextGOPendingIs y  ( T [ z sHost= t] [ 0 +=reqresp y x txid] [ 0 -=req ]) 0"
by simp
lemma nextGOPendingIs_inequality: shows "\<lbrakk>X \<noteq> Y ; nextGOPendingIs X T i \<rbrakk> \<Longrightarrow> \<not> nextGOPendingIs Y T i"
apply(case_tac i)
apply(case_tac "reqresps1 T")
apply force
apply simp
apply(case_tac "reqresps2 T")
apply simp+
done
lemma nextLoad_HostInvalidDirtyEvict: "nextLoad ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) i = nextLoad T i"
apply(case_tac i)
apply simp+
done
lemma nextGOPending_HostInvalidDirtyEvict: "nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 = nextGOPending T 1"
apply simp+
done
lemma nextReqIs_HostInvalidDirtyEvict_otherside_1: "nextReqIs z ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 = nextReqIs z T 1"
by simp
lemma HostInvalidDirtyEvict'_coherent_aux_simpler: assumes "SWMR_state_machine T \<and> HSTATE InvalidM T \<and> nextReqIs DirtyEvict T 0 \<and> GTS T 1 \<and> CSTATE IIA T 0"
  shows "SWMR_state_machine  ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
proof -
have i0: "SWMR T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i1x: "HSTATE InvalidM T " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i2x: "nextReqIs DirtyEvict T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i3x: "GTS T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i4x: "CSTATE IIA T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i3: "C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i4: "H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i5: "H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i6: "C_msg_P_oppo ISAD nextGOPending (\<lambda>T i. \<not> CSTATE Modified T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i10: "H_msg_P_same SharedM (nextReqIs RdShared) (\<lambda>T i. \<not> CSTATE Modified T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i11: "H_msg_P_oppo SharedM (nextReqIs RdShared) (\<lambda>T i. \<not> CSTATE Modified T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i12: "H_msg_P_same ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> CSTATE Modified T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i13: "H_msg_P_oppo ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> nextDTHDataPending T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i14: "H_msg_P_oppo ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> nextSnpRespIs RspIFwdM T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i15: "H_msg_P_same ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> nextSnpRespIs RspIFwdM T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i16: "C_H_state IMAD (nextReqIs RdOwn) Modified SD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i17: "C_H_state IMAD (nextReqIs RdOwn) Modified SAD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i18: "C_H_state IMAD (nextReqIs RdOwn) Modified SA T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i19: "C_H_state Invalid nextStore Modified SAD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i20: "C_H_state Invalid nextStore Modified SA T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i21: "C_H_state Invalid nextStore Modified SD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i22: "HSTATE SharedM T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i23: "HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i24: "HSTATE MD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i25: "C_msg_not RdShared IMAD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i26: "C_msg_not RdShared Invalid T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i27: "H_msg_P_same ModifiedM (nextReqIs DirtyEvict) (\<lambda>T i. CSTATE MIA T i \<or> CSTATE IIA T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i28: "C_msg_P_host MIA (nextGOPendingIs GO_WritePull) (\<lambda>T. \<not> HSTATE ModifiedM T) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i29: "C_msg_P_same MIA (nextGOPendingIs GO_WritePull) nextEvict T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i30: "C_msg_P_host MIA (nextGOPendingIs GO_WritePull) (HSTATE ID) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i31: "C_state_not MIA RdShared T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i32: "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) nextEvict T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i34: "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextReqIs RdShared T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i35: "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextDTHDataPending T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i36: "H_C_state_msg_same ModifiedM Modified (\<lambda>T i. \<not> nextReqIs RdShared T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i37: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) nextEvict T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i39: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextReqIs RdShared T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i40: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextDTHDataPending T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i41: "H_C_state_msg_oppo ModifiedM IIA (\<lambda>T i. \<not> nextReqIs RdShared T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i46: "C_msg_P_host Shared (nextSnoopIs SnpInv) (HSTATE MA) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i47: "C_msg_state RdShared ISAD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i49: "C_not_C_msg Modified ISAD nextGOPending T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i50: "C_msg_P_same Invalid nextStore (\<lambda>T i. \<not> nextHTDDataPending T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i51: "C_msg_P_same Invalid nextStore (\<lambda>T i. \<not> nextSnoopIs SnpInv T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i52: "C_msg_P_same ISAD nextGOPending (\<lambda>T i. \<not> nextReqIs RdShared T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i55: "snps2 T \<noteq> [] \<longrightarrow> reqs1 T = [] \<and> snpresps2 T = [] \<and> dthdatas2 T = [] \<and> reqresps1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i56: "snps1 T \<noteq> [] \<longrightarrow> reqs2 T = [] \<and> snpresps1 T = [] \<and> dthdatas1 T = [] \<and> reqresps2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i57: "length (reqs1 T) \<le> 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i58: "length (reqs2 T) \<le> 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i59: "C_msg_P_same Shared (nextSnoopIs SnpInv) (\<lambda>T i. \<not> nextHTDDataPending T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i60: "length (snps2 T) \<le> 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i61: "length (snps1 T) \<le> 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i611old: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) (\<lambda> T i. \<not>nextSnoopPending T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i612old: "C_msg_P_oppo Invalid nextStore (\<lambda>T i. \<not> nextSnoopPending T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i613old: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i614old: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i615old: "(CSTATE Shared T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i616old: "(CSTATE Shared T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i617old: "(CSTATE IIA T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> htddatas1 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i618old: "(CSTATE IIA T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> htddatas2 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i68: "CSTATE Invalid T 0 \<longrightarrow> reqs1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i69: "CSTATE Invalid T 1 \<longrightarrow> reqs2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i70: "CSTATE Shared T 0 \<longrightarrow> reqs1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i71: "CSTATE Shared T 1 \<longrightarrow> reqs2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i72: "CSTATE Modified T 0 \<longrightarrow> \<not>CSTATE Modified T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i73: "CSTATE Modified T 1 \<longrightarrow> \<not>CSTATE Modified T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i74: "CSTATE ISD T 0 \<longrightarrow> \<not>HSTATE ModifiedM T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i75: "CSTATE ISD T 1 \<longrightarrow> \<not>HSTATE ModifiedM T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i76: "C_msg_P_host ISD (nextSnoopIs SnpInv) (HSTATE MA) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i77: "length (htddatas1 T) \<le> 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i78: "length (htddatas2 T) \<le> 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i79: "CSTATE ISD T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i80: "CSTATE ISD T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i81: "CSTATE ISD T 0 \<longrightarrow> reqs1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i82: "CSTATE ISD T 1 \<longrightarrow> reqs2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i83: "(CSTATE IMAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> reqs1 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i84: "(CSTATE IMAD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> reqs2 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i85: "(length (reqresps1 T) \<le> 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i86: "(length (reqresps2 T) \<le> 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i87: "(CSTATE MIA T 0 \<and> (nextGOPendingIs GO_WritePull T 0)  \<longrightarrow> snps1 T = [] )" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i88: "(CSTATE MIA T 1 \<and> (nextGOPendingIs GO_WritePull T 1)  \<longrightarrow> snps2 T = [] )" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i89: "(CSTATE MIA T 0 \<and> (nextGOPendingIs GO_WritePull T 0) \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i90: "(CSTATE MIA T 1 \<and> (nextGOPendingIs GO_WritePull T 1) \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> htddatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i91: "(CSTATE ISAD T 0 \<longrightarrow> \<not> nextReqIs DirtyEvict T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i92: "(CSTATE ISAD T 1 \<longrightarrow> \<not> nextReqIs DirtyEvict T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i93: "(C_msg_P_same MIA  (nextReqIs DirtyEvict) (nextEvict) T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i94: "(reqs1 T \<noteq> [] \<longrightarrow> reqresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i95: "(reqs2 T \<noteq> [] \<longrightarrow> reqresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i98: "(reqs1 T \<noteq> [] \<longrightarrow> snpresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i99: "(reqs2 T \<noteq> [] \<longrightarrow> snpresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i100: "(reqs1 T \<noteq> [] \<longrightarrow> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i101: "(reqs2 T \<noteq> [] \<longrightarrow> htddatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i751old: " (CSTATE ISD T 0 \<longrightarrow> nextLoad T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)+
have i752old: " (CSTATE ISD T 1 \<longrightarrow> nextLoad T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)+
have i104: "(reqs1 T \<noteq> [] \<longrightarrow> reqresps1 T = [] ) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i105: "(reqs2 T \<noteq> [] \<longrightarrow> reqresps2 T = [] ) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i106: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i107: "(HSTATE ModifiedM T \<longrightarrow> \<not>CSTATE Shared T 0 \<and> \<not>CSTATE Shared T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i108: "(HSTATE SD T \<and> dthdatas1 T \<noteq> [] \<longrightarrow> htddatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i109: "(HSTATE SD T \<and> dthdatas2 T \<noteq> [] \<longrightarrow> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i110: "(length (dthdatas1 T ) \<le> 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i111: "(length (dthdatas2 T ) \<le> 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i112: "(HSTATE SD T \<and> nextDTHDataFrom 0 T \<longrightarrow> (CSTATE ISAD T 1 \<or> CSTATE ISD T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i113: "(HSTATE SD T \<and> nextDTHDataFrom 1 T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISD T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i114: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i115: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i118: "(snpresps1 T \<noteq> [] \<longrightarrow> reqresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i119: "(snpresps2 T \<noteq> [] \<longrightarrow> reqresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i120: "(length (snpresps1 T) \<le> 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i121: "(length (snpresps2 T) \<le> 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i126: "(HSTATE SAD T \<and> snpresps1 T \<noteq> [] \<longrightarrow> htddatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i127: "(HSTATE SAD T \<and> snpresps2 T \<noteq> [] \<longrightarrow> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i128: "(HSTATE MD T \<and> reqs1 T \<noteq> [] \<longrightarrow> dthdatas1 T \<noteq> []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i129: "(HSTATE MD T \<and> reqs2 T \<noteq> [] \<longrightarrow> dthdatas2 T \<noteq> []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i130: "(HSTATE ID T \<and> dthdatas1 T \<noteq> [] \<longrightarrow> CSTATE Invalid T 0 \<or> CSTATE ISAD T 0 \<or> CSTATE IMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i131: "(HSTATE ID T \<and> dthdatas2 T \<noteq> [] \<longrightarrow> CSTATE Invalid T 1 \<or> CSTATE ISAD T 1 \<or> CSTATE IMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i132: "(HSTATE ID T \<and> dthdatas1 T \<noteq> [] \<longrightarrow> \<not>CSTATE MIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i133: "(HSTATE ID T \<and> dthdatas2 T \<noteq> [] \<longrightarrow> \<not>CSTATE MIA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i136: "(dthdatas1 T \<noteq> [] \<and> HSTATE SD T \<longrightarrow> snpresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i137: "(dthdatas2 T \<noteq> [] \<and> HSTATE SD T \<longrightarrow> snpresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i138: "(CSTATE ISD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> nextLoad T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i139: "(CSTATE ISD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> nextLoad T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i142: "(C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) (\<lambda> T i. \<not>nextSnoopPending T i) T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i143: "(CSTATE ISAD T 0 \<and> nextGOPending T 0 \<longrightarrow> HSTATE SD T \<or> HSTATE SharedM T \<or> HSTATE MAD T \<or> HSTATE SB T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i144: "(CSTATE ISAD T 1 \<and> nextGOPending T 1 \<longrightarrow> HSTATE SD T \<or> HSTATE SharedM T \<or> HSTATE MAD T \<or> HSTATE SB T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i145: "(CSTATE ISAD T 0 \<longrightarrow> nextLoad T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i146: "(CSTATE ISAD T 1 \<longrightarrow> nextLoad T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i147: "(CSTATE ISAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i148: "(CSTATE ISAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i149: "(CSTATE ISAD T 0 \<and> nextGOPending T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] ) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i150: "(CSTATE ISAD T 1 \<and> nextGOPending T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] ) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i153: "((CSTATE Invalid T 0 \<or> CSTATE ISDI T 0) \<and> HSTATE MD T \<longrightarrow> dthdatas1 T \<noteq> []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i154: "((CSTATE Invalid T 1 \<or> CSTATE ISDI T 1) \<and> HSTATE MD T \<longrightarrow> dthdatas2 T \<noteq> []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i159: "(HSTATE ModifiedM T \<longrightarrow> snpresps2 T = [] \<and> snpresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i160: "(HSTATE SAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> CSTATE ISAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i161: "(HSTATE SAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> CSTATE ISAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i164: "(HSTATE SAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> htddatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i165: "(HSTATE SAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i166: "(HSTATE SAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqs2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i167: "(HSTATE SAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqs1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i168: "(HSTATE SD T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqs2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i169: "(HSTATE SD T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqs1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i170: "(HSTATE SharedM T \<and> nextReqIs RdOwn T 0 \<longrightarrow> dthdatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i171: "(HSTATE SharedM T \<and> nextReqIs RdOwn T 1 \<longrightarrow> dthdatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i172: "(HSTATE SharedM T \<and> nextReqIs RdShared T 0 \<longrightarrow> dthdatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i173: "(HSTATE SharedM T \<and> nextReqIs RdShared T 1 \<longrightarrow> dthdatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i178: "(CSTATE IIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> HSTATE IB T \<or> HSTATE SB T \<or> HSTATE MB T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i179: "(CSTATE IIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> HSTATE IB T \<or> HSTATE SB T \<or> HSTATE MB T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i180: "(CSTATE IIA T 0 \<and> nextGOPendingIs GO_WritePullDrop T 0 \<longrightarrow> HSTATE SharedM T \<or> HSTATE InvalidM T \<or> HSTATE ModifiedM T \<or> HSTATE SB T \<or> HSTATE ID T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i181: "(CSTATE IIA T 1 \<and> nextGOPendingIs GO_WritePullDrop T 1 \<longrightarrow> HSTATE SharedM T \<or> HSTATE InvalidM T \<or> HSTATE ModifiedM T \<or> HSTATE SB T \<or> HSTATE ID T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i182: "(CSTATE IMAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MA T \<or> HSTATE MAD T \<or> HSTATE SAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i183: "(CSTATE IMAD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MA T \<or> HSTATE MAD T \<or> HSTATE SAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i186: "(HSTATE SharedM T \<longrightarrow> dthdatas1 T = [] \<and> dthdatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i187: "(CSTATE MIA T 1 \<longrightarrow> \<not>CSTATE MIA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i188: "(CSTATE MIA T 0 \<longrightarrow> \<not>CSTATE MIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i189: "(HSTATE ModifiedM T \<longrightarrow> dthdatas2 T = [] \<and> dthdatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i190: "(nextDTHDataFrom  0 T \<longrightarrow> \<not> nextHTDDataPending T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i191: "(nextDTHDataFrom  1 T \<longrightarrow> \<not> nextHTDDataPending T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i192: "(nextDTHDataFrom 0 T \<longrightarrow> \<not> nextDTHDataFrom 1 T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i193: "(nextDTHDataFrom 1 T \<longrightarrow> \<not> nextDTHDataFrom 0 T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i194: "(HSTATE SA T \<longrightarrow> dthdatas2 T = [] \<and> dthdatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i195: "(HSTATE SD T \<longrightarrow> \<not> CSTATE IIA T 0 \<or> \<not> CSTATE IIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i196: "(HSTATE SAD T \<longrightarrow> (\<not> CSTATE IIA T 0 \<or> nextSnpRespIs RspIFwdM T 0) \<and> (\<not> CSTATE IIA T 1 \<or> nextSnpRespIs RspIFwdM T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i197: "(CSTATE IIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> \<not> nextDTHDataFrom 1 T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i198: "(CSTATE IIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> \<not> nextDTHDataFrom 0 T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i199: "(CSTATE IIA T 0 \<longrightarrow> \<not> CSTATE IIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i200: "(CSTATE IIA T 1 \<longrightarrow> \<not> CSTATE IIA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i301: "(CSTATE MIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> \<not> nextDTHDataFrom 1 T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i302: "(CSTATE MIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> \<not> nextDTHDataFrom 0 T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i305: "(snpresps1 T \<noteq> [] \<longrightarrow> reqresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i306: "(snpresps2 T \<noteq> [] \<longrightarrow> reqresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i307: "(HSTATE SharedM T \<and> nextReqIs RdShared T 1 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i308: "(HSTATE SharedM T \<and> nextReqIs RdShared T 0 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i309: "(HSTATE SD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i310: "(HSTATE SD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i313: "(HSTATE ModifiedM T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i314: "(C_msg_P_same SIA (nextGOPendingIs GO_WritePull) nextEvict T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i315: "(C_msg_P_same SIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextReqIs RdShared T i) T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i316: "(CSTATE SIA T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i317: "(CSTATE SIA T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> htddatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i318: "(C_msg_P_same SIA (nextGOPendingIs GO_WritePull) (\<lambda> T i. \<not>nextSnoopPending T i) T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i319: "(CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> HSTATE IB T \<or> HSTATE SB T \<or> HSTATE MB T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i320: "(CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> HSTATE IB T \<or> HSTATE SB T \<or> HSTATE MB T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i321: "(C_msg_P_same SIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextDTHDataPending T i) T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i322: "(CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> \<not> nextDTHDataFrom 1 T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i323: "(CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> \<not> nextDTHDataFrom 0 T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i324: "(C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) nextEvict T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i325: "(C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextReqIs RdShared T i) T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i326: "(C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) (\<lambda> T i. \<not>nextSnoopPending T i) T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i327: "(CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePullDrop T 0 \<longrightarrow> HSTATE InvalidM T \<or> HSTATE SharedM T \<or> HSTATE SB T \<or> HSTATE IB T \<or> HSTATE ModifiedM T \<or> HSTATE ID T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i328: "(CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePullDrop T 1 \<longrightarrow> HSTATE InvalidM T \<or> HSTATE SharedM T \<or> HSTATE SB T \<or> HSTATE IB T \<or> HSTATE ModifiedM T \<or> HSTATE ID T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i329: "(C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextDTHDataPending T i) T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i332: "(CSTATE SMAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MA T \<or> HSTATE MAD T \<or> HSTATE SAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i333: "(CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow>  HSTATE SharedM T \<or> HSTATE SA T \<or> HSTATE MA T \<or> HSTATE SB T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i334: "(CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow>  HSTATE SharedM T \<or> HSTATE SA T \<or> HSTATE MA T \<or> HSTATE SB T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i335: "(CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> (CSTATE IMAD T 1 \<and> nextHTDDataPending T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i336: "(CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> (CSTATE IMAD T 0 \<and> nextHTDDataPending T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i337: "(C_not_C_msg Modified IMAD nextGOPending T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i338: "(CSTATE IMAD T 0 \<and> nextGOPending T 0 \<longrightarrow> HSTATE MD T \<or> HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i339: "(CSTATE IMAD T 0 \<longrightarrow> nextStore T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i340: "(CSTATE IMAD T 1 \<longrightarrow> nextStore T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i341: "(CSTATE IMAD T 0 \<and> nextGOPending T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] ) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i342: "(CSTATE IMAD T 1 \<and> nextGOPending T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] ) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i343: "(snpresps1 T \<noteq> [] \<longrightarrow> reqresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i344: "(snpresps2 T \<noteq> [] \<longrightarrow> reqresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i345: "(CSTATE SMAD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MA T \<or> HSTATE MAD T \<or> HSTATE SAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i346: "(CSTATE IMAD T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE MD T \<or> HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i347: "(CSTATE SMAD T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE MD T \<or> HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i348: "(CSTATE SMAD T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE MD T \<or> HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i349: "(CSTATE SMAD T 0 \<longrightarrow> nextStore T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i350: "(CSTATE SMAD T 1 \<longrightarrow> nextStore T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i351: "(C_msg_P_same IMA (nextGOPending) nextStore T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i352: "(CSTATE IMA T 0 \<or> CSTATE SMA T 0 \<or> CSTATE ISA T 0 \<longrightarrow> \<not> nextHTDDataPending T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i353: "(CSTATE IMA T 1 \<or> CSTATE SMA T 1 \<or> CSTATE ISA T 1 \<longrightarrow> \<not> nextHTDDataPending T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i354: "(C_msg_P_oppo IMA (nextGOPending) (\<lambda> T i. \<not>nextSnoopPending T i) T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i355: "(C_msg_P_oppo SMA (nextGOPending) (\<lambda> T i. \<not>nextSnoopPending T i) T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i356: "(C_msg_P_oppo ISA (nextGOPending) (\<lambda> T i. \<not>nextSnoopPending T i) T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i357: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i358: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i365: "(C_msg_P_same SMA (nextGOPending) nextStore T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i366: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i367: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i368: "(CSTATE ISD T 0 \<or> CSTATE ISAD T 0 \<or> CSTATE ISA T 0 \<or> CSTATE ISDI T 0 \<longrightarrow> nextLoad T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i369: "(CSTATE ISD T 1 \<or> CSTATE ISAD T 1 \<or> CSTATE ISA T 1 \<or> CSTATE ISDI T 1 \<longrightarrow> nextLoad T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i370: "(CSTATE IMD T 0 \<or> CSTATE IMAD T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMD T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE SMA T 0  \<longrightarrow> nextStore T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i371: "(CSTATE IMD T 1 \<or> CSTATE IMAD T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMD T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE SMA T 1  \<longrightarrow> nextStore T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i374: "(CSTATE ISA T 0 \<and> nextGOPending T 0 \<longrightarrow> HSTATE SharedM T \<or> HSTATE MAD T \<or> HSTATE MA T \<or> HSTATE SB T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i375: "(CSTATE ISA T 1 \<and> nextGOPending T 1 \<longrightarrow> HSTATE SharedM T \<or> HSTATE MAD T \<or> HSTATE MA T \<or> HSTATE SB T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i376: "(CSTATE ISDI T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> HSTATE ModifiedM T \<or> HSTATE MAD T  \<or> HSTATE MA T \<or> HSTATE MD T\<or> HSTATE ID T \<or> HSTATE InvalidM T \<or> HSTATE SharedM T \<or> HSTATE SB T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i377: "(CSTATE ISDI T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> snps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i378: "(CSTATE ISDI T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> snps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i379: "(CSTATE ISDI T 0 \<longrightarrow> \<not>nextReqIs RdOwn T 1 \<or> \<not>HSTATE ModifiedM T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i380: "(CSTATE ISDI T 1 \<longrightarrow> \<not>nextReqIs RdOwn T 0 \<or> \<not>HSTATE ModifiedM T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i381: "(CSTATE Invalid T 0 \<longrightarrow> reqresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i382: "(CSTATE Invalid T 1 \<longrightarrow> reqresps2 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i383: "(CSTATE ISDI T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> HSTATE ModifiedM T \<or> HSTATE MAD T  \<or> HSTATE MA T \<or> HSTATE MD T\<or> HSTATE ID T \<or> HSTATE InvalidM T \<or> HSTATE SharedM T \<or> HSTATE SB T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i384: "(CSTATE Shared T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i385: "(CSTATE Shared T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i388: "(CSTATE SMAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i389: "(CSTATE SMAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i390: "(CSTATE SMAD T 0 \<and> reqresps1 T = [] \<and> htddatas1 T = [] \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i391: "(CSTATE SMAD T 1 \<and> reqresps2 T = [] \<and> htddatas2 T = [] \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i392: "(nextReqIs RdOwn T 0 \<longrightarrow> CSTATE SMAD T 0 \<or> CSTATE IMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i393: "(nextReqIs RdOwn T 1 \<longrightarrow> CSTATE SMAD T 1 \<or> CSTATE IMAD T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i396: "(CSTATE SMAD T 0 \<and> nextSnoopIs SnpInv T 0 \<and> CXL_SPG_used T 0 \<longrightarrow> nextReqIs RdOwn T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i397: "(CSTATE SMAD T 1 \<and> nextSnoopIs SnpInv T 1 \<and> CXL_SPG_used T 1 \<longrightarrow> nextReqIs RdOwn T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i400: "(CSTATE ISD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i401: "(CSTATE ISD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i406: "(CSTATE IMA T 0 \<or> CSTATE SMA T 0 \<or> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0)  \<longrightarrow> dthdatas1 T = [] \<and> (dthdatas2 T = [] \<or> HSTATE MB T \<or> HSTATE ModifiedM T)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i407: "(CSTATE IMA T 1 \<or> CSTATE SMA T 1 \<or> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1)  \<longrightarrow> dthdatas2 T = [] \<and> (dthdatas1 T = [] \<or> HSTATE MB T \<or> HSTATE ModifiedM T)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i408: "(HSTATE MD T \<longrightarrow> snpresps1 T = [] \<and> snpresps2 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i415: "(HSTATE ModifiedM T  \<and> nextReqIs RdOwn T 0 \<longrightarrow> (CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i416: "(HSTATE ModifiedM T  \<and> nextReqIs RdOwn T 1 \<longrightarrow> (CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i417: "((CSTATE Invalid T 0 \<or> CSTATE ISDI T 0) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i418: "((CSTATE Invalid T 1 \<or> CSTATE ISDI T 1) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i419: "(CSTATE IIA T 0 \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i420: "(CSTATE IIA T 1 \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i421: "(HSTATE MD T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i422: "(HSTATE MD T \<and> nextDTHDataFrom 0 T \<longrightarrow> CSTATE IMAD T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i423: "(HSTATE MD T \<and> nextDTHDataFrom 1 T \<longrightarrow> CSTATE IMAD T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i424: "(HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> CSTATE IMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i425: "(HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> CSTATE IMAD T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i426: "(HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> snpresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i427: "(HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> snpresps1 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i430: "(HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> reqs2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i431: "(HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE Modified T 1 \<and> reqs1 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i432: "(HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i433: "(HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqresps1 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i435: "(CSTATE IMD T 0 \<or> CSTATE SMD T 0 \<or> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextGOPending T 0) \<longrightarrow> dthdatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i436: "(CSTATE IMD T 1 \<or> CSTATE SMD T 1 \<or> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextGOPending T 1) \<longrightarrow> dthdatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i437: "(HSTATE SAD T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 ) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i438: "(HSTATE SAD T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 ) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i441: "(nextSnpRespIs RspSFwdM T 0 \<longrightarrow> CSTATE Shared T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE SIA T 0 \<or> CSTATE SIAC T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i442: "(nextSnpRespIs RspSFwdM T 1 \<longrightarrow> CSTATE Shared T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE SIA T 1 \<or> CSTATE SIAC T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i443: "((HSTATE SAD T \<or> HSTATE MAD T \<or> HSTATE SA T \<or> HSTATE MA T) \<and> snpresps1 T \<noteq> [] \<longrightarrow> htddatas1 T = [] \<or> CSTATE ISDI T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i444: "((HSTATE SAD T \<or> HSTATE MAD T \<or> HSTATE SA T \<or> HSTATE MA T) \<and> snpresps2 T \<noteq> [] \<longrightarrow> htddatas2 T = [] \<or> CSTATE ISDI T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i445: "(HSTATE SAD T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i446: "(HSTATE SAD T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i449: "(HSTATE MAD T \<and> nextSnpRespIs RspIFwdM T 0 \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> dthdatas1 T \<noteq> [] \<and> htddatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i450: "(HSTATE MAD T \<and> nextSnpRespIs RspIFwdM T 1 \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> dthdatas2 T \<noteq> [] \<and> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i451: "(HSTATE MA T \<and> snpresps1 T \<noteq> [] \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> htddatas2 T \<noteq> [] \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> htddatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i452: "(HSTATE MA T \<and> snpresps2 T \<noteq> [] \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> htddatas1 T \<noteq> [] \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i453: "(nextReqIs DirtyEvict T 0 \<longrightarrow> CSTATE MIA T 0 \<or>  CSTATE SIA T 0 \<or> CSTATE IIA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i454: "(nextReqIs DirtyEvict T 1 \<longrightarrow> CSTATE MIA T 1 \<or>  CSTATE SIA T 1 \<or> CSTATE IIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i455: "(HSTATE MA T \<longrightarrow> dthdatas2 T = [] \<and> dthdatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i456: "((nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspIHitSE T 0) \<longrightarrow> CSTATE Invalid T 0 \<or> CSTATE ISDI T 0 \<or> CSTATE ISAD T 0 \<or> CSTATE IMAD T 0 \<or> CSTATE IIA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i457: "((nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspIHitSE T 1) \<longrightarrow> CSTATE Invalid T 1 \<or> CSTATE ISDI T 1 \<or> CSTATE ISAD T 1 \<or> CSTATE IMAD T 1 \<or> CSTATE IIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i460: "((CSTATE Invalid T 0  \<or> CSTATE ISDI T 0 \<or> nextReqIs RdOwn T 0) \<and> HSTATE MA T \<longrightarrow> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i461: "((CSTATE Invalid T 1  \<or> CSTATE ISDI T 1 \<or> nextReqIs RdOwn T 1) \<and> HSTATE MA T \<longrightarrow> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0))" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i462: "((CSTATE ISAD T 0 \<and> nextGOPending T 0) \<or> CSTATE ISA T 0 \<or> ( nextHTDDataPending T 0) \<or> CSTATE Shared T 0 \<longrightarrow> \<not> CSTATE Modified T 1 \<and> (dthdatas1 T = [] \<or> nextSnpRespIs RspSFwdM T 0 \<or> HSTATE SD T)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i463: "((CSTATE ISAD T 1 \<and> nextGOPending T 1) \<or> CSTATE ISA T 1 \<or> ( nextHTDDataPending T 1) \<or> CSTATE Shared T 1 \<longrightarrow> \<not> CSTATE Modified T 0 \<and> (dthdatas2 T = [] \<or> nextSnpRespIs RspSFwdM T 1 \<or> HSTATE SD T)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i465: "(CSTATE IMD T 0 \<or> CSTATE SMD T 0 \<or> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextGOPending T 0) \<longrightarrow> ((\<not> CSTATE ISD T 1) \<and> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE SMD T 1 \<and> \<not>( (CSTATE ISAD T 1 \<or> CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextGOPending T 1) \<and> \<not>CSTATE ISA T 1 \<and> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> \<not> (  nextHTDDataPending T 1) \<and>  \<not> CSTATE Shared T 1 \<and> \<not> CSTATE Modified T 1) \<or> nextSnoopIs SnpInv T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i466: "(CSTATE IMD T 1 \<or> CSTATE SMD T 1 \<or> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextGOPending T 1) \<longrightarrow> ((\<not> CSTATE ISD T 0) \<and> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE SMD T 0 \<and> \<not>( (CSTATE ISAD T 0 \<or> CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextGOPending T 0) \<and> \<not>CSTATE ISA T 0 \<and> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0 \<and> \<not> (  nextHTDDataPending T 0) \<and>  \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Modified T 0) \<or> nextSnoopIs SnpInv T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i467: "(CSTATE Shared T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE SMA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i468: "(CSTATE Shared T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE SMA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i469: "(CSTATE ISD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE SMA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i470: "(CSTATE ISD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE SMA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i471: "(HSTATE MD T \<and> nextDTHDataFrom 0 T \<longrightarrow>  \<not> nextReqIs CleanEvict T 0 \<and> \<not> nextReqIs CleanEvictNoData T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i472: "(HSTATE MD T \<and> nextDTHDataFrom 1 T \<longrightarrow>  \<not> nextReqIs CleanEvict T 1 \<and> \<not> nextReqIs CleanEvictNoData T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i473: "(HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow>  \<not> nextReqIs CleanEvict T 0 \<and> \<not> nextReqIs CleanEvictNoData T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i474: "(HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow>  \<not> nextReqIs CleanEvict T 1 \<and> \<not> nextReqIs CleanEvictNoData T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i475: "(CSTATE Modified T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i476: "(CSTATE Modified T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i477: "(CSTATE Modified T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 ) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i478: "(CSTATE Modified T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 ) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i479: "(CSTATE MIA T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i480: "(CSTATE MIA T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i481: "(CSTATE MIA T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> CSTATE ISAD T 1 ) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i482: "(CSTATE MIA T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> CSTATE ISAD T 0 ) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i483: "(CSTATE Modified T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i484: "(CSTATE Modified T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i485: "(CSTATE Modified T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> CSTATE ISAD T 1 ) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i486: "(CSTATE Modified T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> CSTATE ISAD T 0 ) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i487: "(CSTATE Modified T 0 \<longrightarrow> reqs1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i488: "(CSTATE Modified T 1 \<longrightarrow> reqs2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i489: "(CSTATE Modified T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i490: "(CSTATE Modified T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i491: "(HSTATE InvalidM T \<and> nextReqIs RdShared T 0 \<longrightarrow> dthdatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i492: "(HSTATE InvalidM T \<and> nextReqIs RdShared T 1 \<longrightarrow> dthdatas1 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i493: "(HSTATE InvalidM T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1 \<and> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i494: "(nextReqIs RdOwn T 0 \<longrightarrow> \<not> CSTATE ISAD T 0 \<and> \<not> CSTATE Invalid T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i495: "(nextReqIs RdOwn T 1 \<longrightarrow> \<not> CSTATE ISAD T 1 \<and> \<not> CSTATE Invalid T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i496: "(HSTATE InvalidM T \<and> nextReqIs RdOwn T 0 \<longrightarrow> CSTATE IMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i497: "(HSTATE InvalidM T \<and> nextReqIs RdOwn T 1 \<longrightarrow> CSTATE IMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i498: "(HSTATE InvalidM T \<and> nextReqIs RdOwn T 0 \<longrightarrow> dthdatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i499: "(HSTATE InvalidM T \<and> nextReqIs RdOwn T 1 \<longrightarrow> dthdatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i500: "(CSTATE SIA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i501: "(CSTATE SIA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i502: "(CSTATE SIA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i503: "(CSTATE SIA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i504: "(CSTATE SIA T 0 \<and> nextSnoopIs SnpInv T 0 \<and> CXL_SPG_used T 0 \<longrightarrow> (nextReqIs CleanEvict T 0 \<or> nextReqIs CleanEvictNoData T 0 )) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i505: "(CSTATE SIA T 1 \<and> nextSnoopIs SnpInv T 1 \<and> CXL_SPG_used T 1 \<longrightarrow> (nextReqIs CleanEvict T 1 \<or> nextReqIs CleanEvictNoData T 1 )) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i506: "(CSTATE SIA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE SMA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i507: "(CSTATE SIA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE SMA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i508: "(CSTATE SMAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE SMA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i509: "(CSTATE SMAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE SMA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i510: "(HSTATE ID T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1 \<and> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i511: "(HSTATE ModifiedM T \<and> nextReqIs DirtyEvict T 0 \<longrightarrow> (\<not> CSTATE Modified T 0 \<or> \<not> CSTATE Modified T 1) \<and> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i512: "(HSTATE ModifiedM T \<and> nextReqIs DirtyEvict T 1 \<longrightarrow> (\<not> CSTATE Modified T 0 \<or> \<not> CSTATE Modified T 1) \<and> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i513: "(HSTATE ID T \<and> nextReqIs RdOwn T 0 \<longrightarrow> CSTATE IMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i514: "(HSTATE ID T \<and> nextReqIs RdOwn T 1 \<longrightarrow> CSTATE IMAD T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i515: "(CSTATE SMAD T 0 \<and> nextGOPending T 0\<longrightarrow> nextHTDDataPending T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i516: "(CSTATE SMAD T 1 \<and> nextGOPending T 1\<longrightarrow> nextHTDDataPending T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i517: "(C_msg_P_oppo SMAD nextGOPending (\<lambda>T i. \<not> nextSnoopPending T i) T)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i518: "(HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 0 \<longrightarrow> CSTATE SIAC T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i519: "(HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 1 \<longrightarrow> CSTATE SIAC T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i522: "(nextGOPendingIs GO_WritePull T 0 \<and> HSTATE InvalidM T \<longrightarrow> reqresps2 T = [] \<or> nextReqRespStateIs Invalid (reqresps2 T)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i523: "(nextGOPendingIs GO_WritePull T 1 \<and> HSTATE InvalidM T \<longrightarrow> reqresps1 T = [] \<or> nextReqRespStateIs Invalid (reqresps1 T)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i524: "(HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 0 \<longrightarrow> nextEvict T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i525: "(HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 1 \<longrightarrow> nextEvict T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i526: "(HSTATE SharedM T \<and> nextReqIs CleanEvict T 0 \<longrightarrow> nextEvict T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i527: "(HSTATE SharedM T \<and> nextReqIs CleanEvict T 1 \<longrightarrow> nextEvict T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i528: "(HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 0 \<longrightarrow> \<not> CSTATE ISDI T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i529: "(HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 1 \<longrightarrow> \<not> CSTATE ISDI T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i530: "(HSTATE SharedM T \<and> nextReqIs CleanEvict T 0 \<longrightarrow> \<not> CSTATE ISDI T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i531: "(HSTATE SharedM T \<and> nextReqIs CleanEvict T 1 \<longrightarrow> \<not> CSTATE ISDI T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i532: "(HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 0 \<longrightarrow> \<not> CSTATE MIA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i533: "(HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 1 \<longrightarrow> \<not> CSTATE MIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i534: "(HSTATE SharedM T \<and> nextReqIs CleanEvict T 0 \<longrightarrow> \<not> CSTATE MIA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i535: "(HSTATE SharedM T \<and> nextReqIs CleanEvict T 1 \<longrightarrow> \<not> CSTATE MIA T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i536: "(CSTATE Shared T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> htddatas2 T \<noteq> [] \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> htddatas2 T = [])) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i537: "(CSTATE Shared T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> htddatas1 T \<noteq> [] \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> htddatas1 T = []))" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i538: "(nextReqIs DirtyEvict T 0 \<longrightarrow> nextEvict T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i539: "(nextReqIs DirtyEvict T 1 \<longrightarrow> nextEvict T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i540: "(nextReqIs DirtyEvict T 0 \<and> HSTATE InvalidM T \<longrightarrow> \<not> nextDTHDataFrom 1 T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i541: "(nextReqIs DirtyEvict T 1 \<and> HSTATE InvalidM T \<longrightarrow> \<not> nextDTHDataFrom 0 T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i542: "(nextReqIs DirtyEvict T 0 \<and> HSTATE InvalidM T \<longrightarrow> \<not> CSTATE ISDI T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i543: "(nextReqIs DirtyEvict T 1 \<and> HSTATE InvalidM T \<longrightarrow> \<not> CSTATE ISDI T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i544: "(nextReqIs DirtyEvict T 0 \<and> HSTATE InvalidM T \<longrightarrow> (reqresps2 T = [] \<or> nextReqRespStateIs Invalid (reqresps2 T))) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i545: "(nextReqIs DirtyEvict T 1 \<and> HSTATE InvalidM T \<longrightarrow> (reqresps1 T = [] \<or> nextReqRespStateIs Invalid (reqresps1 T)))" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i546: "(CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not>(CSTATE ISA T 1 \<or> nextHTDDataPending T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i547: "(CSTATE SMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not>(CSTATE ISA T 0 \<or> nextHTDDataPending T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i548: "(CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MAD T \<and> CSTATE IMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i549: "(CSTATE SMD T 1 \<and> nextHTDDataPending T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MAD T \<and> CSTATE IMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i550: "(CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T \<and> CSTATE ISAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i551: "(CSTATE SMD T 1 \<and> nextHTDDataPending T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T \<and> CSTATE ISAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i552: "(CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i553: "(CSTATE SMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i554: "(CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> nextReqIs DirtyEvict T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i555: "(CSTATE SMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> nextReqIs DirtyEvict T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i556: "((nextReqIs CleanEvictNoData T 0 \<or> nextReqIs CleanEvict T 0) \<longrightarrow> (CSTATE SIA T 0 \<or> CSTATE IIA T 0 \<or> CSTATE SIAC T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i557: "((nextReqIs CleanEvictNoData T 1 \<or> nextReqIs CleanEvict T 1) \<longrightarrow> (CSTATE SIA T 1 \<or> CSTATE IIA T 1 \<or> CSTATE SIAC T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i558: "((CSTATE Shared T 0 \<or> CSTATE Shared T 1) \<longrightarrow> \<not> HSTATE MD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i559: "(CSTATE Shared T 0 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i560: "(CSTATE Shared T 1 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i561: "((nextReqIs CleanEvictNoData T 0 \<or> nextReqIs CleanEvict T 0) \<longrightarrow> nextEvict T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i562: "((nextReqIs CleanEvictNoData T 1 \<or> nextReqIs CleanEvict T 1) \<longrightarrow> nextEvict T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i563: "((nextReqIs CleanEvictNoData T 0 \<or> nextReqIs CleanEvict T 0) \<longrightarrow> \<not> CSTATE ISDI T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i564: "((nextReqIs CleanEvictNoData T 1 \<or> nextReqIs CleanEvict T 1) \<longrightarrow> \<not> CSTATE ISDI T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i565: "((nextReqIs CleanEvictNoData T 0 \<or> nextReqIs CleanEvict T 0) \<longrightarrow> \<not> CSTATE MIA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i566: "((nextReqIs CleanEvictNoData T 1 \<or> nextReqIs CleanEvict T 1) \<longrightarrow> \<not> CSTATE MIA T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i567: "(CSTATE IIA T 0 \<and> HSTATE SharedM T \<longrightarrow> reqs2 T = [] \<or> nextReqIs CleanEvict T 1 \<or> nextReqIs CleanEvictNoData T 1 \<or> nextReqIs RdOwn T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i568: "(CSTATE IIA T 1 \<and> HSTATE SharedM T \<longrightarrow> reqs1 T = [] \<or> nextReqIs CleanEvict T 0 \<or> nextReqIs CleanEvictNoData T 0 \<or> nextReqIs RdOwn T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i569: "(CSTATE IIA T 0 \<and> HSTATE SharedM T \<longrightarrow> CSTATE Shared T 1 \<or> CSTATE SIA T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE ISAD T 1 \<and> nextGOPending T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1 \<and> nextGOPending T 1 \<or> CSTATE ISD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SIAC T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i570: "(CSTATE IIA T 1 \<and> HSTATE SharedM T \<longrightarrow> CSTATE Shared T 0 \<or> CSTATE SIA T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE ISAD T 0 \<and> nextGOPending T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0 \<and> nextGOPending T 0 \<or> CSTATE ISD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SIAC T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i571: "(CSTATE IIA T 1 \<and> HSTATE InvalidM T \<and> nextReqIs RdShared T 0 \<longrightarrow> CSTATE ISAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i572: "(CSTATE IIA T 0 \<and> HSTATE InvalidM T \<and> nextReqIs RdShared T 1 \<longrightarrow> CSTATE ISAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i573: "(HSTATE InvalidM T \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0 \<and> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE SMD T 0 \<and>  \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE SMD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i574: "(HSTATE InvalidM T \<longrightarrow> \<not> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0)) \<and> \<not> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i575: "(nextGOPendingIs GO_WritePull T 0 \<or> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> \<not> HSTATE InvalidM T)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i576: "(CSTATE MIA T 0 \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> \<not> nextHTDDataPending T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i577: "(CSTATE MIA T 1 \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0 \<and> \<not> nextHTDDataPending T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i578: "(nextGOPendingIs GO_WritePull T 0 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i579: "(nextGOPendingIs GO_WritePull T 1 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i580: "((CSTATE IMA T 0 \<or> CSTATE SMA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0) \<longrightarrow> (HSTATE MA T \<or> HSTATE ModifiedM T \<or> HSTATE MB T \<or> HSTATE MAD T \<or> HSTATE SAD T)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i581: "((CSTATE IMA T 1 \<or> CSTATE SMA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1) \<longrightarrow> (HSTATE MA T \<or> HSTATE ModifiedM T \<or> HSTATE MB T \<or> HSTATE MAD T \<or> HSTATE SAD T))" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i582: "(CSTATE MIA T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i583: "(CSTATE MIA T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> htddatas2 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i584: "(CSTATE MIA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i585: "(CSTATE MIA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i586: "(CSTATE MIA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i587: "(CSTATE MIA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i588: "((HSTATE InvalidM T \<or> HSTATE SharedM T \<or> HSTATE ModifiedM T) \<longrightarrow> (\<not> nextGOPendingIs GO_WritePull T 0) \<and> (\<not> nextGOPendingIs GO_WritePull T 1))" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i589: "(CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePullDrop T 0 \<and> CSTATE IIA T 1 \<longrightarrow> HSTATE InvalidM T \<or> HSTATE IB T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i590: "(CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePullDrop T 1 \<and> CSTATE IIA T 0 \<longrightarrow> HSTATE InvalidM T \<or> HSTATE IB T)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i591: "(HSTATE InvalidM T \<longrightarrow> dthdatas1 T = [] \<and> dthdatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i592: "(CSTATE Invalid T 0 \<longrightarrow> \<not> nextSnoopIs SnpInv T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i593: "(CSTATE Invalid T 1 \<longrightarrow> \<not> nextSnoopIs SnpInv T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i594: "(CSTATE Modified T 0 \<longrightarrow> \<not> CSTATE MIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i595: "(CSTATE Modified T 1 \<longrightarrow> \<not> CSTATE MIA T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i596: "(HSTATE MA T \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> htddatas2 T \<noteq> [] \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> htddatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i597: "(HSTATE MA T \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> htddatas1 T \<noteq> [] \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i598: "(CSTATE SMAD T 0 \<and> nextGOPending T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i599: "(CSTATE SMAD T 1 \<and> nextGOPending T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i600: "(HSTATE MA T \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i601: "(HSTATE MA T \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i602: "(HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> CSTATE ISD T 0 \<and> \<not> CSTATE ISA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i603: "(HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> CSTATE ISD T 1 \<and> \<not> CSTATE ISA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i604: "(HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> CSTATE SMD T 0 \<and> \<not> CSTATE SMA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i605: "(HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> CSTATE SMD T 1 \<and> \<not> CSTATE SMA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i606: "(HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE IMA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i607: "(HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE IMA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i608: "(HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> (CSTATE ISAD T 0 \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0))) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i609: "(HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> (CSTATE IMAD T 0 \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0))) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i610: "(HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> (CSTATE SMAD T 0 \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0))) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i611: "(HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> (CSTATE ISAD T 1 \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i612: "(HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> (CSTATE IMAD T 1 \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i613: "(HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> (CSTATE SMAD T 1 \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i614: "(CSTATE ISD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> htddatas2 T \<noteq> []) \<or> ((CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> htddatas2 T = [])) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i615: "(CSTATE ISD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> htddatas1 T \<noteq> []) \<or> ((CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> htddatas1 T = [])) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i616: "(CSTATE ISA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> htddatas2 T \<noteq> []) \<or> ((CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> htddatas2 T = [])) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i617: "(CSTATE ISA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> htddatas1 T \<noteq> []) \<or> ((CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> htddatas1 T = [])) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i618: "(CSTATE ISAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> htddatas2 T \<noteq> []) \<or> ((CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> htddatas2 T = [])) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i619: "(CSTATE ISAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> htddatas1 T \<noteq> []) \<or> ((CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> htddatas1 T = [])) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i620: "(CSTATE IMAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i621: "(CSTATE IMAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i622: "(CSTATE IMD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i623: "(CSTATE IMD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i624: "(CSTATE IMA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i625: "(CSTATE IMA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i626: "(CSTATE SMAD T 0 \<and> nextGOPending T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i627: "(CSTATE SMAD T 1 \<and> nextGOPending T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i628: "(CSTATE SMD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i629: "(CSTATE SMD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i630: "(CSTATE SMA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i631: "(CSTATE SMA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i632: "(CSTATE ISD T 0 \<or> CSTATE ISA T 0 \<longrightarrow> \<not> HSTATE MD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i633: "(CSTATE ISD T 1 \<or> CSTATE ISA T 1 \<longrightarrow> \<not> HSTATE MD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i634: "(CSTATE ISAD T 0 \<and> (nextHTDDataPending T 0 \<or> nextGOPending T 0) \<longrightarrow> \<not> HSTATE MD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i635: "(CSTATE ISAD T 1 \<and> (nextHTDDataPending T 1 \<or> nextGOPending T 1) \<longrightarrow> \<not> HSTATE MD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i636: "(CSTATE ISD T 0 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i637: "(CSTATE ISD T 1 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i638: "(CSTATE ISA T 0 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i639: "(CSTATE ISA T 1 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i640: "(CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> (CSTATE ISAD T 1 \<and> nextGOPending T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i641: "(CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> (CSTATE ISAD T 0 \<and> nextGOPending T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i642: "(CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> CSTATE ISA T 1 \<and> \<not> nextHTDDataPending T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i643: "(CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> nextHTDDataPending T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i644: "(CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> CSTATE Shared T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i645: "(CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> CSTATE Shared T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i646: "(CSTATE ISA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i647: "(CSTATE ISA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i648: "(CSTATE ISAD T 0 \<and> nextGOPending T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i649: "(CSTATE ISAD T 1 \<and> nextGOPending T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i650: "(CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i651: "(CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i652: "(HSTATE SharedM T \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i653: "(HSTATE SharedM T \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i654: "(HSTATE SharedM T \<longrightarrow> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE SMD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i655: "(HSTATE SharedM T \<longrightarrow> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE SMD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i656: "(HSTATE SharedM T \<longrightarrow> \<not> (CSTATE IMAD T 0 \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0))) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i657: "(HSTATE SharedM T \<longrightarrow> \<not> (CSTATE IMAD T 1 \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i658: "(HSTATE SharedM T \<longrightarrow> \<not> (CSTATE SMAD T 0 \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0))) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i659: "(HSTATE SharedM T \<longrightarrow> \<not> (CSTATE SMAD T 1 \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i660: "(HSTATE SharedM T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i661: "(HSTATE InvalidM T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i662: "(HSTATE InvalidM T \<longrightarrow> \<not> CSTATE ISD T 0 \<and> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE SMD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i663: "(HSTATE InvalidM T \<longrightarrow> \<not> CSTATE ISD T 1 \<and> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE SMD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i664: "(HSTATE InvalidM T \<longrightarrow> \<not> (CSTATE ISAD T 0 \<and> nextGOPending T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i665: "(HSTATE InvalidM T \<longrightarrow> \<not> (CSTATE ISAD T 1 \<and> nextGOPending T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i666: "(HSTATE InvalidM T \<longrightarrow> \<not> (CSTATE IMAD T 0 \<and> nextGOPending T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i667: "(HSTATE InvalidM T \<longrightarrow> \<not> (CSTATE IMAD T 1 \<and> nextGOPending T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i668: "(HSTATE InvalidM T \<longrightarrow> \<not> (CSTATE SMAD T 0 \<and> nextGOPending T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i669: "(HSTATE InvalidM T \<longrightarrow> \<not> (CSTATE SMAD T 1 \<and> nextGOPending T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i670: "(HSTATE InvalidM T \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i671: "(HSTATE InvalidM T \<longrightarrow> \<not> CSTATE ISA T 1 \<and> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i672: "(HSTATE InvalidM T \<longrightarrow> \<not> nextHTDDataPending T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i673: "(HSTATE InvalidM T \<longrightarrow> \<not> nextHTDDataPending T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i674: "(HSTATE InvalidM T \<longrightarrow> \<not> CSTATE Shared T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i675: "(HSTATE InvalidM T \<longrightarrow> \<not> CSTATE Shared T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i676: "(HSTATE InvalidM T \<longrightarrow> \<not> CSTATE Modified T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i677: "(CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> snpresps2 T = [] \<and> reqresps1 T = [] \<and> snps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i678: "(CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> snpresps1 T = [] \<and> reqresps2 T = [] \<and> snps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i679: "(CSTATE IMAD T 0 \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<longrightarrow> snpresps2 T = [] \<and> snps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i680: "(CSTATE IMAD T 1 \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<longrightarrow> snpresps1 T = [] \<and> snps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i681: "(CSTATE IMD T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> CSTATE ISAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i682: "(CSTATE IMD T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> CSTATE ISAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i683: "(CSTATE IMA T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> CSTATE ISAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i684: "(CSTATE IMA T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> CSTATE ISAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i685: "(CSTATE IMAD T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> CSTATE ISAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i686: "(CSTATE IMAD T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> CSTATE ISAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i687: "(CSTATE IMD T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i688: "(CSTATE IMD T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i689: "(CSTATE IMA T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i690: "(CSTATE IMA T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i691: "(CSTATE IMAD T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i692: "(CSTATE IMD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i693: "(CSTATE IMD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i694: "(CSTATE IMAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i695: "(CSTATE IMAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i696: "(CSTATE IMA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i697: "(CSTATE IMA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i698: "(CSTATE IMAD T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i699: "(HSTATE IB T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1 \<and> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i700: "(HSTATE IB T \<and> nextReqIs RdOwn T 0 \<longrightarrow> CSTATE IMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i701: "(HSTATE IB T \<and> nextReqIs RdOwn T 1 \<longrightarrow> CSTATE IMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i702: "(HSTATE SB T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i703: "(HSTATE SB T \<longrightarrow> length (dthdatas1 T) \<le> 1 \<and> length (dthdatas2 T) \<le> 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i704: "(HSTATE IB T \<longrightarrow> length (dthdatas1 T) \<le> 1 \<and> length (dthdatas2 T) \<le> 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i705: "(HSTATE SB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE IIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i706: "(HSTATE SB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE IIA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i707: "(HSTATE MB T \<longrightarrow> length (dthdatas1 T) \<le> 1 \<and> length (dthdatas2 T) \<le> 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i708: "(HSTATE SB T \<and> nextDTHDataFrom 0 T \<longrightarrow> dthdatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i709: "(HSTATE SB T \<and> nextDTHDataFrom 1 T \<longrightarrow> dthdatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i710: "(HSTATE IB T \<and> nextDTHDataFrom 0 T \<longrightarrow> dthdatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i711: "(HSTATE IB T \<and> nextDTHDataFrom 1 T \<longrightarrow> dthdatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i712: "(HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> dthdatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i713: "(HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> dthdatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i714: "(HSTATE SB T \<longrightarrow> snps2 T = [] \<and> snps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i715: "(HSTATE IB T \<longrightarrow> snps2 T = [] \<and> snps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i716: "(HSTATE MB T \<longrightarrow> snps2 T = [] \<and> snps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i717: "(HSTATE SB T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i718: "(HSTATE SB T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i719: "(HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i720: "(HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i721: "(HSTATE IB T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i722: "(HSTATE IB T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i723: "(HSTATE SB T \<longrightarrow> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE SMD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i724: "(HSTATE SB T \<longrightarrow> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE SMD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i725: "(HSTATE IB T \<longrightarrow> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE SMD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i726: "(HSTATE IB T \<longrightarrow> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE SMD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i727: "(HSTATE SharedM T \<and> lastSharer T \<and> nextReqIs CleanEvictNoData T 0 \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i728: "(HSTATE SharedM T \<and> lastSharer T \<and> nextReqIs CleanEvictNoData T 1 \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i729: "(HSTATE SharedM T \<and> lastSharer T \<and> nextReqIs CleanEvictNoData T 0 \<longrightarrow> \<not> (CSTATE ISAD T 1 \<and> nextGOPending T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i730: "(HSTATE SharedM T \<and> lastSharer T \<and> nextReqIs CleanEvictNoData T 1 \<longrightarrow> \<not> (CSTATE ISAD T 0 \<and> nextGOPending T 0))" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i731: "(CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> snpresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i732: "(CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> snpresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i733: "(HSTATE SAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> snpresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i734: "(HSTATE SAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> snpresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i735: "(CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i736: "(CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i737: "(HSTATE ModifiedM T \<longrightarrow> (\<not> CSTATE SIA T 0 \<or> nextGOPendingIs GO_WritePullDrop T 0) \<and> (\<not> CSTATE SIA T 1 \<or> nextGOPendingIs GO_WritePullDrop T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i738: "(HSTATE MA T \<and> snpresps1 T \<noteq> [] \<longrightarrow> \<not> CSTATE SIA T 0 \<and> \<not> CSTATE SIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i739: "(HSTATE MA T \<and> snpresps2 T \<noteq> [] \<longrightarrow> \<not> CSTATE SIA T 0 \<and> \<not> CSTATE SIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i740: "(HSTATE MD T \<longrightarrow> \<not> CSTATE SIA T 0 \<and> \<not> CSTATE SIA T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i741: "(CSTATE MIA T 0 \<longrightarrow> \<not> (CSTATE IMAD T 1 \<and> nextGOPending T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i742: "(CSTATE MIA T 1 \<longrightarrow> \<not> (CSTATE IMAD T 0 \<and> nextGOPending T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i743: "(CSTATE MIA T 0 \<longrightarrow> \<not> (CSTATE SMAD T 1 \<and> nextGOPending T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i744: "(CSTATE MIA T 1 \<longrightarrow> \<not> (CSTATE SMAD T 0 \<and> nextGOPending T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i745: "(HSTATE ModifiedM T \<and> nextReqIs RdOwn T 0 \<longrightarrow> CSTATE IMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i746: "(HSTATE ModifiedM T \<and> nextReqIs RdOwn T 1 \<longrightarrow> CSTATE IMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i747: "(HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE ISA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i748: "(HSTATE MD T \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE ISA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i749: "(HSTATE MA T \<and> snpresps1 T \<noteq> [] \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE ISA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i750: "(HSTATE MA T \<and> snpresps2 T \<noteq> [] \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE ISA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i751: "(CSTATE MIA T 0 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE SMA T 1 \<and> \<not> CSTATE SMD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i752: "(CSTATE MIA T 1 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE SMA T 0 \<and> \<not> CSTATE SMD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i753: "(CSTATE MIA T 0 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE IMD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i754: "(CSTATE MIA T 1 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE IMD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i755: "(CSTATE MIA T 0 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> (CSTATE IMAD T 1 \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i756: "(CSTATE MIA T 1 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> (CSTATE IMAD T 0 \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0))) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i757: "(CSTATE MIA T 0 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE SMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i758: "(CSTATE MIA T 1 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE SMAD T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i759: "(CSTATE IMD T 1 \<longrightarrow> reqresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i760: "(CSTATE IMD T 0 \<longrightarrow> reqresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i761: "(HSTATE IB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i762: "(HSTATE IB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i763: "(HSTATE IB T \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE ISD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i764: "(HSTATE IB T \<longrightarrow> \<not> CSTATE ISA T 1 \<and> \<not> CSTATE ISD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i765: "(HSTATE IB T \<longrightarrow> \<not> CSTATE SMA T 0 \<and> \<not> CSTATE SMD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i766: "(HSTATE IB T \<longrightarrow> \<not> CSTATE SMA T 1 \<and> \<not> CSTATE SMD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i767: "(HSTATE IB T \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE IMD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i768: "(HSTATE IB T \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE IMD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i769: "(HSTATE IB T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i770: "(HSTATE IB T \<longrightarrow> \<not> nextHTDDataPending T 0 \<and> \<not> nextHTDDataPending T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i771: "(HSTATE ID T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i772: "(HSTATE ID T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i773: "(HSTATE ID T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i774: "(HSTATE ID T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i775: "(HSTATE ID T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextHTDDataPending T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i776: "(HSTATE ID T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextHTDDataPending T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i777: "(HSTATE ModifiedM T \<and> nextReqIs RdShared T 0 \<longrightarrow> \<not> CSTATE ISDI T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i778: "(HSTATE ModifiedM T \<and> nextReqIs RdShared T 1 \<longrightarrow> \<not> CSTATE ISDI T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i779: "(HSTATE SD T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i780: "(HSTATE SAD T \<and> snpresps1 T \<noteq> [] \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i781: "(HSTATE SAD T \<and> snpresps2 T \<noteq> [] \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i782: "(HSTATE MD T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i783: "(snpresps1 T \<noteq> [] \<and> HSTATE MAD T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i784: "(snpresps2 T \<noteq> [] \<and> HSTATE MAD T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i785: "(CSTATE IMD T 0 \<and> HSTATE MD T \<longrightarrow> snpresps1 T = [] \<and> snps1 T = [] \<and> reqresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i786: "(CSTATE IMD T 1 \<and> HSTATE MD T \<longrightarrow> snpresps2 T = [] \<and> snps2 T = [] \<and> reqresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i787: "(nextDTHDataFrom 0 T \<and> HSTATE MD T \<and> nextReqIs RdOwn T 0 \<longrightarrow> CSTATE IMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i788: "(nextDTHDataFrom 1 T \<and> HSTATE MD T \<and> nextReqIs RdOwn T 1 \<longrightarrow> CSTATE IMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i789: "(HSTATE SAD T \<and> nextSnpRespIs RspSFwdM T 0 \<longrightarrow> \<not> CSTATE Modified T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i790: "(HSTATE SAD T \<and> nextSnpRespIs RspSFwdM T 1 \<longrightarrow> \<not> CSTATE Modified T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i791: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE Modified T 1 \<and> \<not> CSTATE Shared T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i792: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Shared T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i793: "(HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> dthdatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i794: "(HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> dthdatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i795: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i796: "(HSTATE SharedM T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i797: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i798: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i799: "(HSTATE MA T \<and> snpresps1 T \<noteq> [] \<longrightarrow> htddatas1 T = [] \<or> CSTATE ISDI T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i800: "(HSTATE MA T \<and> snpresps2 T \<noteq> [] \<longrightarrow> htddatas2 T = [] \<or> CSTATE ISDI T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i801: "(HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> (CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i802: "(HSTATE MB T \<longrightarrow> \<not> CSTATE ISD T 0 \<and> \<not> CSTATE ISD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i803: "(HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> CSTATE Invalid T 0 \<or> CSTATE ISAD T 0 \<or> CSTATE IMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i804: "(HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> CSTATE Invalid T 1 \<or> CSTATE ISAD T 1 \<or> CSTATE IMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i805: "(HSTATE MB T \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i806: "(HSTATE MB T \<longrightarrow> snpresps1 T = [] \<and> snpresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i807: "(HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i808: "(HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i809: "(HSTATE MB T \<longrightarrow> \<not> CSTATE SIA T 0 \<and> \<not> CSTATE SIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i810: "(HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextReqIs RdOwn T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i811: "(HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextReqIs RdOwn T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i812: "(HSTATE MB T \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE ISA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i813: "(CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<and> HSTATE SB T \<longrightarrow> \<not> CSTATE IIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i814: "(CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<and> HSTATE SB T \<longrightarrow> \<not> CSTATE IIA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i815: "(HSTATE IB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextReqIs DirtyEvict T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i816: "(HSTATE IB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextReqIs DirtyEvict T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i817: "(HSTATE SB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i818: "(HSTATE SB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i819: "(HSTATE SB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i820: "(HSTATE SB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i821: "(HSTATE ID T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i822: "(HSTATE ID T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i823: "(CSTATE Modified T 0 \<longrightarrow> \<not> nextReqIs RdOwn T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i824: "(CSTATE Modified T 1 \<longrightarrow> \<not> nextReqIs RdOwn T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i825: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE ISD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i826: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE ISD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i827: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> (CSTATE ISAD T 1 \<and> nextGOPending T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i828: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> (CSTATE ISAD T 0 \<and> nextGOPending T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i829: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> (CSTATE IMA T 1 \<and> nextGOPending T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i830: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> (CSTATE IMA T 0 \<and> nextGOPending T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i831: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> (CSTATE ISA T 1 \<and> nextGOPending T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i832: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> (CSTATE ISA T 0 \<and> nextGOPending T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i833: "((CSTATE ISAD T 0 \<and> nextGOPending T 0) \<or> CSTATE ISA T 0 \<or> ( nextHTDDataPending T 0) \<or> CSTATE Shared T 0 \<longrightarrow> \<not> (CSTATE IMA T 1 \<and> nextGOPending T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i834: "((CSTATE ISAD T 1 \<and> nextGOPending T 1) \<or> CSTATE ISA T 1 \<or> ( nextHTDDataPending T 1) \<or> CSTATE Shared T 1 \<longrightarrow> \<not> (CSTATE IMA T 0 \<and> nextGOPending T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i835: "(HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> snps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i836: "(HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> snps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i837: "(HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE MIA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i838: "(HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE MIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i839: "(HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE SIA T 0 \<and> \<not> CSTATE SIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i840: "(HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE SIA T 1 \<and> \<not> CSTATE SIA T 0)  " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i841: "(CSTATE Modified T 0 \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> (htddatas2 T = [] \<or> CSTATE ISDI T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i842: "(CSTATE Modified T 1 \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0 \<and> (htddatas1 T = [] \<or> CSTATE ISDI T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i843: "(CSTATE Modified T 0 \<longrightarrow> \<not> CSTATE SMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i844: "(CSTATE Modified T 1 \<longrightarrow> \<not> CSTATE SMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i845: "(CSTATE Modified T 0 \<longrightarrow> snpresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i846: "(CSTATE Modified T 1 \<longrightarrow> snpresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i847: "(CSTATE SMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> (CSTATE ISAD T 1 \<and> nextGOPending T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i848: "(CSTATE SMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> (CSTATE ISAD T 0 \<and> nextGOPending T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i849: "(CSTATE SMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE ISA T 1 \<and> \<not> CSTATE Shared T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i850: "(CSTATE SMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE Shared T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i851: "(CSTATE SMA T 0 \<and> nextGOPending T 0 \<longrightarrow> htddatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i852: "(CSTATE SMA T 1 \<and> nextGOPending T 1 \<longrightarrow> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i853: "(CSTATE SMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE IMA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i854: "(CSTATE SMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE IMA T 0)  " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i855: "(CSTATE Invalid T 0 \<longrightarrow> snps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i856: "(CSTATE Invalid T 1 \<longrightarrow> snps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i857: "(HSTATE SD T \<and> nextDTHDataFrom 0 T \<longrightarrow> CSTATE ISD T 1 \<or> CSTATE ISAD T 1 \<and> nextGOPending T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i858: "(HSTATE SD T \<and> nextDTHDataFrom 1 T \<longrightarrow> CSTATE ISD T 0 \<or> CSTATE ISAD T 0 \<and> nextGOPending T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i859: "(HSTATE SAD T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i860: "(HSTATE SAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i861: "(CSTATE SMAD T 0 \<and> nextGOPending T 0 \<and> nextHTDDataPending T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T \<and> CSTATE ISAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i862: "(CSTATE SMAD T 1 \<and> nextGOPending T 1 \<and> nextHTDDataPending T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T \<and> CSTATE ISAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i863: "(CSTATE SMAD T 0 \<and> nextGOPending T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> nextReqIs DirtyEvict T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i864: "(CSTATE SMAD T 1 \<and> nextGOPending T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> nextReqIs DirtyEvict T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i865: "(CSTATE SMAD T 0 \<and> nextGOPending T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i866: "(CSTATE SMAD T 1 \<and> nextGOPending T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i867: "(CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<and> HSTATE IB T \<longrightarrow> \<not> nextReqIs DirtyEvict T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i868: "(CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<and> HSTATE IB T \<longrightarrow> \<not> nextReqIs DirtyEvict T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i869: "(CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<and> HSTATE SB T \<longrightarrow> \<not> CSTATE MIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i870: "(CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<and> HSTATE SB T \<longrightarrow> \<not> CSTATE MIA T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i871: "(HSTATE InvalidM T \<and> nextReqIs DirtyEvict T 0 \<longrightarrow> CSTATE IIA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i872: "(HSTATE InvalidM T \<and> nextReqIs DirtyEvict T 1 \<longrightarrow> CSTATE IIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i873: "(HSTATE InvalidM T \<longrightarrow> (\<not> CSTATE SIA T 0 \<or> nextGOPendingIs GO_WritePullDrop T 0) \<and> (\<not> CSTATE SIA T 1 \<or> nextGOPendingIs GO_WritePullDrop T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i874: "(HSTATE MA T  \<and> nextSnpRespIs RspIFwdM T 0 \<longrightarrow> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i875: "(HSTATE MA T  \<and> nextSnpRespIs RspIFwdM T 1 \<longrightarrow> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0))  " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i876: "(HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> (CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i877: "(HSTATE MB T \<and> CSTATE IIA T 0 \<longrightarrow> (CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i878: "(HSTATE MB T \<and> CSTATE IIA T 1 \<longrightarrow> (CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i883: "length (dthdatas1 T) \<le> 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i884: "length (dthdatas2 T) \<le> 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i885: "(HSTATE IB T \<and> CSTATE IIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> \<not> nextReqIs DirtyEvict T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i886: "(HSTATE IB T \<and> CSTATE IIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> \<not> nextReqIs DirtyEvict T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i887: "(HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i888: "(HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i889: "(HSTATE MA T \<and> snpresps1 T \<noteq> [] \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i890: "(HSTATE MA T \<and> snpresps2 T \<noteq> [] \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1)  " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i891: "(CSTATE IMAD T 0 \<and> nextGOPending T 0 \<and> HSTATE MD T \<longrightarrow> snpresps1 T = [] \<and> snps1 T = [] \<and> reqresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i892: "(CSTATE IMAD T 1 \<and> nextGOPending T 1 \<and> HSTATE MD T \<longrightarrow> snpresps2 T = [] \<and> snps2 T = [] \<and> reqresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i893: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> (htddatas2 T = [] \<or> CSTATE ISDI T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i894: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0 \<and> (htddatas1 T = [] \<or> CSTATE ISDI T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i895: "(CSTATE SMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> (htddatas2 T = [] \<or> CSTATE ISDI T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i896: "(CSTATE SMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0 \<and> (htddatas1 T = [] \<or> CSTATE ISDI T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i897: "(CSTATE Modified T 0 \<longrightarrow> dthdatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i898: "(CSTATE Modified T 1 \<longrightarrow> dthdatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i899: "(nextSnpRespIs RspIHitSE T 0 \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i900: "(nextSnpRespIs RspIHitSE T 1 \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i901: "(CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> CSTATE SMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i902: "(CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> CSTATE SMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i903: "(CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> CSTATE SMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i904: "(CSTATE SMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> CSTATE SMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i905: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE SMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i906: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE SMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i907: "(CSTATE SMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE SMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i908: "(CSTATE SMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE SMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i909: "(CSTATE IMAD T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE SMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i910: "(CSTATE IMAD T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE SMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i911: "(HSTATE MD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE SMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i912: "(HSTATE MD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE SMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i913: "(CSTATE SMAD T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE SMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i914: "(CSTATE SMAD T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE SMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i915: "(HSTATE InvalidM T \<longrightarrow> \<not> CSTATE SMAD T 1 \<and> \<not> CSTATE SMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i916: "(HSTATE IB T \<longrightarrow> \<not> CSTATE SMAD T 1 \<and> \<not> CSTATE SMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i917: "(HSTATE ID T \<longrightarrow> \<not> CSTATE SMAD T 1 \<and> \<not> CSTATE SMAD T 0)  " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i918: "(HSTATE MA T \<and> nextSnpRespIs RspIHitSE T 0 \<longrightarrow> \<not> nextReqIs DirtyEvict T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i919: "(HSTATE MA T \<and> nextSnpRespIs RspIHitSE T 1 \<longrightarrow> \<not> nextReqIs DirtyEvict T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i920: "(CSTATE Modified T 0 \<longrightarrow> htddatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i921: "(CSTATE Modified T 1 \<longrightarrow> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i922: "(HSTATE ModifiedM T \<longrightarrow> snps1 T = [] \<and> snps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i923: "(CSTATE SMAD T 0 \<and> nextHTDDataPending T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i924: "(CSTATE SMAD T 1 \<and> nextHTDDataPending T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i925: "(CSTATE SMAD T 1 \<and> HSTATE MA T \<and> nextSnpRespIs RspIFwdM T 0 \<longrightarrow> \<not> nextReqIs DirtyEvict T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i926: "(CSTATE SMAD T 0 \<and> HSTATE MA T \<and> nextSnpRespIs RspIFwdM T 1 \<longrightarrow> \<not> nextReqIs DirtyEvict T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i927: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i928: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i929: "(CSTATE SIAC T 0 \<longrightarrow> \<not> nextHTDDataPending T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i930: "(CSTATE SIAC T 1 \<longrightarrow> \<not> nextHTDDataPending T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i931: "((CSTATE SIAC T 0 \<and> nextGOPending T 0 \<and> nextGOPendingState Invalid T 0) --> snps2 T = [] \<and> snpresps2 T = [] \<and> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i932: "((CSTATE SIAC T 1 \<and> nextGOPending T 1 \<and> nextGOPendingState Invalid T 1) --> snps1 T = [] \<and> snpresps1 T = [] \<and> htddatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i933: "((CSTATE SIAC T 0 \<and> nextGOPending T 0 \<and> nextGOPendingState Invalid T 0) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i934: "((CSTATE SIAC T 1 \<and> nextGOPending T 1 \<and> nextGOPendingState Invalid T 1) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i935: "((CSTATE SIAC T 0 \<and> nextGOPending T 0 \<and> nextGOPendingState Invalid T 0) \<and> HSTATE MD T \<longrightarrow> dthdatas1 T \<noteq> []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i936: "((CSTATE SIAC T 1 \<and> nextGOPending T 1 \<and> nextGOPendingState Invalid T 1) \<and> HSTATE MD T \<longrightarrow> dthdatas2 T \<noteq> []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i937: "((CSTATE SIAC T 0 \<and> nextGOPending T 0 \<and> nextGOPendingState Invalid T 0) \<and> HSTATE MA T \<longrightarrow>(CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i938: "((CSTATE SIAC T 1 \<and> nextGOPending T 1 \<and> nextGOPendingState Invalid T 1) \<and> HSTATE MA T \<longrightarrow>(CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i939: "((CSTATE SIAC T 0 \<and> nextGOPending T 0 \<and> nextGOPendingState Invalid T 0) --> snps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i940: "((CSTATE SIAC T 1 \<and> nextGOPending T 1 \<and> nextGOPendingState Invalid T 1) --> snps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i941: "((CSTATE SIAC T 0 \<and> nextGOPending T 0 \<and> nextGOPendingState Invalid T 0) --> reqs1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i942: "((CSTATE SIAC T 1 \<and> nextGOPending T 1 \<and> nextGOPendingState Invalid T 1) --> reqs2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i943: "(HSTATE MA T \<and> nextSnpRespIs RspIFwdM T 0 \<longrightarrow> \<not> nextHTDDataPending T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i944: "(HSTATE MA T \<and> nextSnpRespIs RspIFwdM T 1 \<longrightarrow> \<not> nextHTDDataPending T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i945: "(HSTATE SB T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i946: "(nextReqIs CleanEvictNoData T 0 \<longrightarrow> CSTATE SIAC T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i947: "(nextReqIs CleanEvictNoData T 1 \<longrightarrow> CSTATE SIAC T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i948: "(nextSnpRespIs RspIHitSE T 0 \<longrightarrow> \<not> nextDTHDataFrom 0 T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i949: "(nextSnpRespIs RspIHitSE T 1 \<longrightarrow> \<not> nextDTHDataFrom 1 T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i950: "(nextSnpRespIs RspIFwdM T 0 \<longrightarrow> \<not> nextReqIs CleanEvictNoData T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i951: "(nextSnpRespIs RspIFwdM T 1 \<longrightarrow> \<not> nextReqIs CleanEvictNoData T 1)  " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i952: "(CSTATE SMA T 0 \<and> nextSnoopIs SnpData T 0 \<and> nextGOPending T 0 \<longrightarrow> HSTATE SAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i953: "(CSTATE SMA T 1 \<and> nextSnoopIs SnpData T 1 \<and> nextGOPending T 1 \<longrightarrow> HSTATE SAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i954: "((CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePullDrop T 0) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or>(CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i955: "((CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePullDrop T 1) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or>(CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0)   " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i956: "((CSTATE SIAC T 0 \<and> nextGOPendingIs GO T 0 \<and> nextGOPendingState Invalid T 0 \<and> \<not> CSTATE IIA T 1 \<and> GTS T 1) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or>(CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i957: "((CSTATE SIAC T 1 \<and> nextGOPendingIs GO T 1 \<and> nextGOPendingState Invalid T 1 \<and> \<not> CSTATE IIA T 0 \<and> GTS T 0) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or>(CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0)   " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i958: "((CSTATE SIAC T 0 \<and> nextGOPendingIs GO T 0 \<and> nextGOPendingState Invalid T 0 \<and> \<not> CSTATE IIA T 1 \<and> GTS T 1) \<and> HSTATE MD T \<longrightarrow> dthdatas1 T \<noteq> []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i959: "((CSTATE SIAC T 1 \<and> nextGOPendingIs GO T 1 \<and> nextGOPendingState Invalid T 1 \<and> \<not> CSTATE IIA T 0 \<and> GTS T 0) \<and> HSTATE MD T \<longrightarrow> dthdatas2 T \<noteq> [])  " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i960: "((CSTATE SIAC T 0 \<and> nextGOPendingIs GO T 0 \<and> nextGOPendingState Invalid T 0 \<and> \<not> CSTATE IIA T 1 \<and> GTS T 1) \<and> HSTATE MA T \<longrightarrow> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i961: "((CSTATE SIAC T 1 \<and> nextGOPendingIs GO T 1 \<and> nextGOPendingState Invalid T 1 \<and> \<not> CSTATE IIA T 0 \<and> GTS T 0) \<and> HSTATE MA T \<longrightarrow> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i962: "(HSTATE SD T \<and> nextDTHDataFrom 0 T \<longrightarrow> snps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i963: "(HSTATE SD T \<and> nextDTHDataFrom 1 T \<longrightarrow> snps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i964: "(HSTATE SD T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i965: "(HSTATE SD T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i966: "(HSTATE ID T \<and> nextDTHDataFrom 0 T \<longrightarrow> (\<not> CSTATE SIA T 1 \<or> nextGOPendingIs GO_WritePullDrop T 1) ) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i967: "(HSTATE ID T \<and> nextDTHDataFrom 1 T \<longrightarrow> (\<not> CSTATE SIA T 0 \<or> nextGOPendingIs GO_WritePullDrop T 0) ) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i968: "(CSTATE MIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<and> HSTATE ID T \<longrightarrow> (\<not> CSTATE SIA T 1 \<or> nextGOPendingIs GO_WritePullDrop T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i969: "(CSTATE MIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<and> HSTATE ID T \<longrightarrow> (\<not> CSTATE SIA T 0 \<or> nextGOPendingIs GO_WritePullDrop T 0))  " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i970: "(HSTATE SAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i971: "(CSTATE SIAC T 0 \<and> nextGOPendingIs GO T 0 \<longrightarrow> (\<not> HSTATE SAD T \<and> \<not> HSTATE MD T \<and> \<not> HSTATE MA T \<and> (CSTATE IIA T 1 \<longrightarrow> \<not> HSTATE SharedM T))) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i972: "(CSTATE SIAC T 1 \<and> nextGOPendingIs GO T 1 \<longrightarrow> (\<not> HSTATE SAD T \<and> \<not> HSTATE MD T \<and> \<not> HSTATE MA T \<and> (CSTATE IIA T 0 \<longrightarrow> \<not> HSTATE SharedM T)))  " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i201: " HSTATE IB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])" by simp
have i205: "\<not> nextReqIs RdShared T 0" by (metis C_msg_state_def i2x i47 i91)
have i206: "\<not> nextReqIs RdOwn T 0" by (metis ReqType.distinct(39) assms nextReqIs_invariant)
have i207: "\<not> CSTATE ISAD T 0" by (smt (verit) assms i91)
have i208aux: "length (reqs1 T) \<le> 1" by (metis i57)
have i208: "reqs1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []" by (smt (verit) reqlength1_minus i208aux)
have i209: "\<forall>X. \<not> nextReqIs X ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
using empty_reqs_nextReqIs i208
by presburger
have i210: " (reqresps1 T ) = []"
using empty_reqs_nextReqIs i2x i94
by blast
have i211: "(snps2 T ) = []"
using i2x i55
by fastforce
have i212: "snpresps2 T = []"
using assms empty_reqs_nextReqIs i98
by blast
have i213: "   snps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
using i211 snps2_HostInvalidDirtyEvict
by presburger
have i214: " snpresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] "
using i212 snpresps2_HostInvalidDirtyEvict
by presburger
have i2150: "htddatas1 T = []"
using assms empty_reqs_nextReqIs i100
by blast
have i215: "   htddatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
using htddatas1_HostInvalidDirtyEvict i2150
by presburger
have aux_r34_7: "reqresps1 T = []" by (simp add: i210)
have aux_r34_8: "nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0" by (metis aux_r34_3 i210)
have aux_r34_9: "\<not>nextGOPendingIs GO_WritePullDrop ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
using aux_r34_8 nextGOPendingIs_inequality
by blast
have aux_r34_10: "(CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and>
  nextGOPendingIs GO_WritePullDrop ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow>
  HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or>
  HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or>
  HSTATE MD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or>
  HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]))"
using aux_r34_9
by blast
have aux_r46: "(CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and>
  nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow>
  HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or>
  HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])) "
using i215 nextHTDDataPending_def
by presburger
have aux3_r46: " \<not> ((CSTATE IMAD T 1 \<and> nextHTDDataPending T 1))" by (metis i1x i673)
have aux2_r46: "\<not>(CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and>
  nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1)"
using aux3_r46
by force
have "\<not> nextReqIs RdOwn ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
using i209
by blast
show ?thesis
unfolding SWMR_state_machine_def
proof (intro conjI)
show goal1: "SWMR ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 CSTATE_various_forms1 MESI_State.distinct(121) MESI_State.distinct(31) assms)
done
show goal2: "C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i603 i611 i676)
done
show goal3: "H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i493 i676)
done
show goal4: "H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i493 i676)
done
show goal5: "C_msg_P_oppo ISAD nextGOPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i665 i676 nextGOPending_HostInvalidDirtyEvict)
done
show goal6: "H_msg_P_same SharedM (nextReqIs RdShared) (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i209 i676)
done
show goal7: "H_msg_P_oppo SharedM (nextReqIs RdShared) (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i209 i493)
done
show goal8: "H_msg_P_same ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i209 i676)
done
show goal9: "H_msg_P_oppo ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> nextDTHDataPending T i) ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) HOST_State.distinct(169) HOST_State.distinct(37) HSTATE_invariant3 i201 i208 reqs1_empty_not_nextReqIs_general_invariant)
done
show goal10: "H_msg_P_oppo ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> nextSnpRespIs RspIFwdM T i) ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) HOST_State.distinct(197) HOST_State.distinct(37) HSTATE_invariant3 i201 i214 nextSnpRespIs_invariant2)
done
show goal11: "H_msg_P_same ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> nextSnpRespIs RspIFwdM T i) ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) HOST_State.distinct(197) HOST_State.distinct(37) HSTATE_invariant3 i201 i208 nextReqIs_not_various_forms1)
done
show goal12: "C_H_state IMAD (nextReqIs RdOwn) Modified SD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 \<open>\<not> nextReqIs RdOwn ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0\<close> assms i493 i699)
done
show goal13: "C_H_state IMAD (nextReqIs RdOwn) Modified SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 \<open>\<not> nextReqIs RdOwn ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0\<close> assms i493 i699)
done
show goal14: "C_H_state IMAD (nextReqIs RdOwn) Modified SA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 \<open>\<not> nextReqIs RdOwn ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0\<close> assms i493 i699)
done
show goal15: "C_H_state Invalid nextStore Modified SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i493 i676)
done
show goal16: "C_H_state Invalid nextStore Modified SA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i493 i676)
done
show goal17: "C_H_state Invalid nextStore Modified SD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i493 i676)
done
show goal18: "HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i493 i676)
done
show goal19: "HSTATE SD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i493 i676)
done
show goal20: "HSTATE MD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i493 i676)
done
show goal21: "C_msg_not RdShared IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_inequality_invariant MESI_State.distinct(261) assms i209 i572 nextReqIs_HostInvalidDirtyEvict_otherside_1)
done
show goal22: "C_msg_not RdShared Invalid ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_inequality_invariant MESI_State.distinct(143) assms i209 i572 nextReqIs_HostInvalidDirtyEvict_otherside_1)
done
show goal23: "H_msg_P_same ModifiedM (nextReqIs DirtyEvict) (\<lambda>T i. CSTATE MIA T i \<or> CSTATE IIA T i) ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) assms i199 i209 i872 nextReqIs_HostInvalidDirtyEvict_otherside_1)
done
show goal24: "C_msg_P_host MIA (nextGOPendingIs GO_WritePull) (\<lambda>T. \<not> HSTATE ModifiedM T) ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 HostInvalidDirtyEvict_nextGOPendingIs_otherside assms i575 i661)
done
show goal25: "C_msg_P_same MIA (nextGOPendingIs GO_WritePull) nextEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) HostInvalidDirtyEvict_nextGOPendingIs_otherside assms i538 i575 nextEvict_HostInvalidDirtyEvict_invariant)
done
show goal26: "C_msg_P_host MIA (nextGOPendingIs GO_WritePull) (HSTATE ID) ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 HostInvalidDirtyEvict_nextGOPendingIs_otherside assms i575 i661)
done
show goal27: "C_state_not MIA RdShared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i209 i661)
done
show goal28: "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) nextEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms aux_r34_9 i199)
done
show goal29: "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextReqIs RdShared T i) ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms aux_r34_9 i199)
done
show goal30: "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextDTHDataPending T i) ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms aux_r34_9 i199)
done
show goal31: "H_C_state_msg_same ModifiedM Modified (\<lambda>T i. \<not> nextReqIs RdShared T i) ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i209 i676)
done
show goal32: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) nextEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) HostInvalidDirtyEvict_nextGOPendingIs_otherside assms i538 i575 nextEvict_HostInvalidDirtyEvict_invariant)
done
show goal33: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextReqIs RdShared T i) ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) HostInvalidDirtyEvict_nextGOPendingIs_otherside assms i209 i575)
done
show goal34: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextDTHDataPending T i) ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (metis CSTATE_general_rule_3_0 DIRTYEVICT_COL_def dthdatas1_general_rule_5_0 i1x i200 i4x i591 nextDTHDataPending_def numeral_One zero_neq_numeral)
done
show goal35: "H_C_state_msg_oppo ModifiedM IIA (\<lambda>T i. \<not> nextReqIs RdShared T i) ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) HOST_State.distinct(169) HOST_State.distinct(37) HSTATE_invariant3 i201)
done
show goal36: "C_msg_P_host Shared (nextSnoopIs SnpInv) (HSTATE MA) ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i674 i675)
done
show goal37: "C_msg_state RdShared ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i209 i572 nextReqIs_HostInvalidDirtyEvict_otherside_1)
done
show goal38: "C_not_C_msg Modified ISAD nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i665 i676 nextGOPending_HostInvalidDirtyEvict)
done
show goal39: "C_msg_P_same Invalid nextStore (\<lambda>T i. \<not> nextHTDDataPending T i) ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) assms i672 i673 nextHTDDataPending_general_rule_6_0)
done
show goal40: "C_msg_P_same Invalid nextStore (\<lambda>T i. \<not> nextSnoopIs SnpInv T i) ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 i592 i593 nextSnoopIs_general_rule_8_0)
done
show goal41: "C_msg_P_same ISAD nextGOPending (\<lambda>T i. \<not> nextReqIs RdShared T i) ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) assms i209 i572 i665 nextGOPending_HostInvalidDirtyEvict nextReqIs_HostInvalidDirtyEvict_otherside_1)
done
show goal42: "snps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<longrightarrow> reqs1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snpresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> dthdatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> reqresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) i213)
done
show goal43: "snps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<longrightarrow> reqs2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snpresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> dthdatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> reqresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) dthdatas1_HostInvalidDirtyEvict i208 i56 reqresps2_HostInvalidDirtyEvict reqs2_HostInvalidDirtyEvict snpresps1_HostInvalidDirtyEvict snps1_HostInvalidDirtyEvict)
done
show goal44: "length (reqs1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])) \<le> 1"
apply  (insert assms)
apply (smt (verit) i208 i211 i60)
done
show goal45: "length (reqs2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])) \<le> 1"
apply  (insert assms)
apply (smt (verit) i58 reqs2_HostInvalidDirtyEvict)
done
show goal46: "length (snps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])) \<le> 1"
apply  (insert assms)
apply (smt (verit) i211 i213 i60)
done
show goal47: "length (snps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])) \<le> 1"
apply  (insert assms)
apply (smt (verit) i61 snps1_HostInvalidDirtyEvict)
done
show goal48: "C_msg_P_same Shared (nextSnoopIs SnpInv) (\<lambda>T i. \<not> nextHTDDataPending T i) ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i674 i675)
done
show goal49: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextSnoopPending T i) ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (cases "dthdatas1 T")
apply  (auto)
apply (smt (verit) GTS_def i3x i4x i618old)
apply (smt (verit) i211)
apply (smt (verit) i210 i56 list.discI)
apply (smt (verit) i211)
done
show goal50: "C_msg_P_oppo Invalid nextStore (\<lambda>T i. \<not> nextSnoopPending T i) ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (cases "dthdatas1 T")
apply  (auto)
apply (smt (verit) i211)
apply (smt (verit) CSTATE_various_forms4 i614old)
apply (smt (verit) i211)
apply (smt (verit) i211 i56 list.distinct(1))
done
show goal51: "CSTATE Invalid ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> snps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snpresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> reqresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> htddatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i68 reqs1_empty_not_nextReqIs_general_invariant)
done
show goal52: "CSTATE Invalid ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> snps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snpresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> reqresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> htddatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 htddatas2_HostInvalidDirtyEvict i208 i382 i614old reqresps2_HostInvalidDirtyEvict snpresps1_HostInvalidDirtyEvict snps1_HostInvalidDirtyEvict)
done
show goal53: "CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> snps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snpresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> reqresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> htddatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i674)
done
show goal54: "CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> snps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snpresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> reqresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> htddatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i675)
done
show goal55: "CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> snps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snpresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> htddatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) i213 i214 i215)
done
show goal56: "CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> snps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snpresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> htddatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i199)
done
show goal57: "CSTATE Invalid ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> reqs1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) i208)
done
show goal58: "CSTATE Invalid ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> reqs2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 i69 reqs2_HostInvalidDirtyEvict)
done
show goal59: "CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> reqs1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) i208)
done
show goal60: "CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> reqs2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i675)
done
show goal61: "CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i676)
done
show goal62: "CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i676)
done
show goal63: "CSTATE ISD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i602 i611)
done
show goal64: "CSTATE ISD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i603 i611)
done
show goal65: "CSTATE ISD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> nextLoad ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i602 i609)
done
show goal66: "CSTATE ISD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> nextLoad ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i603 i609)
done
show goal67: "C_msg_P_host ISD (nextSnoopIs SnpInv) (HSTATE MA) ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i602 i603 i609)
done
show goal68: "length (htddatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])) \<le> 1"
apply  (insert assms)
apply (smt (verit) i215 i2150 i77)
done
show goal69: "length (htddatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])) \<le> 1"
apply  (insert assms)
apply (smt (verit) htddatas2_HostInvalidDirtyEvict i78)
done
show goal70: "CSTATE ISD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> snps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snpresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> reqresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i602 i609)
done
show goal71: "CSTATE ISD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> snps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snpresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> reqresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i603 i609)
done
show goal72: "CSTATE ISD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> reqs1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) i208)
done
show goal73: "CSTATE ISD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> reqs2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i603 i609)
done
show goal74: "CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> reqs1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) i208)
done
show goal75: "CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> reqs2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r46)
done
show goal76: "length (reqresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])) \<le> 1"
apply  (insert assms)
apply (smt (verit) i210 reqresps1_HostInvalidDirtyEvict)
done
show goal77: "length (reqresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])) \<le> 1"
apply  (insert assms)
apply (smt (verit) i86 reqresps2_HostInvalidDirtyEvict)
done
show goal78: "CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> snps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i661)
done
show goal79: "CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> snps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) i213)
done
show goal80: "CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> snps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snpresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> htddatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) i213 i214 i215)
done
show goal81: "CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> snps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snpresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> htddatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) HostInvalidDirtyEvict_nextGOPendingIs_otherside assms i575)
done
show goal82: "CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) i209)
done
show goal83: "CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) assms i199 i872 nextReqIs_HostInvalidDirtyEvict_otherside_1)
done
show goal84: "C_msg_P_same MIA (nextReqIs DirtyEvict) nextEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) assms i199 i209 i872 nextReqIs_HostInvalidDirtyEvict_otherside_1)
done
show goal85: "reqs1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<longrightarrow> reqresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) i208)
done
show goal86: "reqs2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<longrightarrow> reqresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) i208 i95 reqresps2_HostInvalidDirtyEvict reqs2_HostInvalidDirtyEvict)
done
show goal87: "reqs1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<longrightarrow> snpresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) i214)
done
show goal88: "reqs2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<longrightarrow> snpresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) i208 i99 reqs2_HostInvalidDirtyEvict snpresps1_HostInvalidDirtyEvict)
done
show goal89: "reqs1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<longrightarrow> htddatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) i215)
done
show goal90: "reqs2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<longrightarrow> htddatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) htddatas2_HostInvalidDirtyEvict i101 i208 reqs2_HostInvalidDirtyEvict)
done
show goal91: "HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextReqIs RdOwn ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> (CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> (CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextReqIs RdOwn ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0\<close>)
done
show goal92: "HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextReqIs RdOwn ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> (CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> (CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(169) HOST_State.distinct(37) HSTATE_invariant3 i201)
done
show goal93: "HSTATE MB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> (CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> (CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(169) HOST_State.distinct(377) HSTATE_invariant3 i201)
done
show goal94: "HSTATE MB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> (CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> (CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) assms i540 nextDTHDataFrom_general_rule_5_0)
done
show goal95: "HSTATE MB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> (CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> (CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(169) HOST_State.distinct(377) HSTATE_invariant3 i201)
done
show goal96: "HSTATE MB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> (CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> (CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i199)
done
show goal97: "reqs1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<longrightarrow> reqresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) i208)
done
show goal98: "reqs2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<longrightarrow> reqresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) i208 i95 reqresps2_HostInvalidDirtyEvict reqs2_HostInvalidDirtyEvict)
done
show goal99: "HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(169) HOST_State.distinct(197) HSTATE_invariant3 i201)
done
show goal100: "HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i674 i675)
done
show goal101: "HSTATE SD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> dthdatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<longrightarrow> htddatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(197) HSTATE_invariant4 i201)
done
show goal102: "HSTATE SD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> dthdatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<longrightarrow> htddatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) i215)
done
show goal103: "length (dthdatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])) \<le> 1"
apply  (insert assms)
apply (smt (verit) assms dthdatas1_HostInvalidDirtyEvict i211 i2150 i591 i60)
done
show goal104: "length (dthdatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])) \<le> 1"
apply  (insert assms)
apply (smt (verit) assms dthdatas2_HostInvalidDirtyEvict i211 i2150 i591 i60)
done
show goal105: "HSTATE SD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE ISD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(169) HOST_State.distinct(197) HSTATE_invariant3 i201)
done
show goal106: "HSTATE SD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE ISD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) assms i540 nextDTHDataFrom_general_rule_5_0)
done
show goal107: "HSTATE SA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> (nextSnpRespIs RspIFwdM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> nextSnpRespIs RspSFwdM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<longrightarrow> CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE ISA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(197) HOST_State.distinct(223) HSTATE_invariant3 i201)
done
show goal108: "HSTATE SA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> (nextSnpRespIs RspIFwdM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> nextSnpRespIs RspSFwdM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<longrightarrow> CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE ISA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(197) HOST_State.distinct(223) HSTATE_invariant3 i201)
done
show goal109: "nextSnpRespIs RspIFwdM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> nextSnpRespIs RspIHitSE ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> CSTATE Invalid ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE ISDI ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms)
done
show goal110: "nextSnpRespIs RspIFwdM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> nextSnpRespIs RspIHitSE ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> CSTATE Invalid ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE ISDI ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 HostInvalidDirtyEvict_nextSnpRespIs_otherside assms i199 i457 i542)
done
show goal111: "nextReqIs DirtyEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) i209)
done
show goal112: "nextReqIs DirtyEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) assms i199 i872 nextReqIs_HostInvalidDirtyEvict_otherside_1)
done
show goal113: "snpresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<longrightarrow> reqresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) i118 i208 reqresps2_HostInvalidDirtyEvict snpresps1_HostInvalidDirtyEvict)
done
show goal114: "snpresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<longrightarrow> reqresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) i214)
done
show goal115: "length (snpresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])) \<le> 1"
apply  (insert assms)
apply (smt (verit) i120 snpresps1_HostInvalidDirtyEvict)
done
show goal116: "length (snpresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])) \<le> 1"
apply  (insert assms)
apply (smt (verit) i121 i212 i214)
done
show goal117: "HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> (nextSnpRespIs RspIFwdM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> nextSnpRespIs RspSFwdM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<longrightarrow> CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(169) HOST_State.distinct(197) HSTATE_invariant3 i201)
done
show goal118: "HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> (nextSnpRespIs RspIFwdM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> nextSnpRespIs RspSFwdM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<longrightarrow> CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(169) HOST_State.distinct(197) HSTATE_invariant3 i201)
done
show goal119: "HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextSnpRespIs RspIFwdM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> dthdatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<and> htddatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(269) HSTATE_invariant4 i201)
done
show goal120: "HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextSnpRespIs RspIFwdM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> dthdatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<and> htddatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) HostInvalidDirtyEvict_nextSnpRespIs_otherside i212 nextSnpRespIs_invariant2)
done
show goal121: "HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> snpresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<longrightarrow> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> htddatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<or> (CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> htddatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(289) HSTATE_invariant4 i201)
done
show goal122: "HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> snpresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<longrightarrow> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> htddatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<or> (CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> htddatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) i214)
done
show goal123: "HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> snpresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<longrightarrow> htddatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) HTDDataPending_htddatas_invariant2 assms i673 nextHTDDataPending_general_rule_6_0)
done
show goal124: "HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> snpresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<longrightarrow> htddatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) i215)
done
show goal125: "HSTATE MD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> reqs1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<longrightarrow> dthdatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> []"
apply  (insert assms)
apply (smt (verit) i208)
done
show goal126: "HSTATE MD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> reqs2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<longrightarrow> dthdatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> []"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(169) HOST_State.distinct(307) HSTATE_invariant3 i201)
done
show goal127: "HSTATE ID ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> dthdatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<longrightarrow> CSTATE Invalid ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) assms dthdatas1_HostInvalidDirtyEvict i208 i591)
done
show goal128: "HSTATE ID ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> dthdatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<longrightarrow> CSTATE Invalid ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) assms dthdatas2_HostInvalidDirtyEvict i208 i591)
done
show goal129: "HSTATE ID ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> dthdatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<longrightarrow> \<not> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) assms dthdatas1_HostInvalidDirtyEvict i208 i591)
done
show goal130: "HSTATE ID ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> dthdatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<longrightarrow> \<not> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) assms dthdatas2_HostInvalidDirtyEvict i208 i591)
done
show goal131: "dthdatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<and> HSTATE SD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> snpresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) i214)
done
show goal132: "dthdatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<and> HSTATE SD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> snpresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) assms dthdatas2_HostInvalidDirtyEvict i208 i591)
done
show goal133: "CSTATE ISD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> nextLoad ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i662)
done
show goal134: "CSTATE ISD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> nextLoad ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i663)
done
show goal135: "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextSnoopPending T i) ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms aux_r34_9 i199)
done
show goal136: "CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> HSTATE SD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE SB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 i207)
done
show goal137: "CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> HSTATE SD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE SB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i665 nextGOPending_HostInvalidDirtyEvict)
done
show goal138: "CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> nextLoad ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 i207)
done
show goal139: "CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> nextLoad ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 i146 nextLoad_HostInvalidDirtyEvict)
done
show goal140: "CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 i207)
done
show goal141: "CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i148 i601 i670 i672 nextSnoopIs_general_rule_8_0)
done
show goal142: "CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> snps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snpresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) i213 i214)
done
show goal143: "CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> snps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snpresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i665 nextGOPending_HostInvalidDirtyEvict)
done
show goal144: "(CSTATE Invalid ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE ISDI ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> (CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> (CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(169) HOST_State.distinct(37) HSTATE_invariant3 i201)
done
show goal145: "(CSTATE Invalid ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE ISDI ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> (CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> (CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(169) HOST_State.distinct(37) HSTATE_invariant3 i201)
done
show goal146: "(CSTATE Invalid ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE ISDI ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> HSTATE MD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> dthdatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> []"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(197) HOST_State.distinct(307) HSTATE_invariant3 i201)
done
show goal147: "(CSTATE Invalid ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE ISDI ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> HSTATE MD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> dthdatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> []"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(197) HOST_State.distinct(307) HSTATE_invariant3 i201)
done
show goal148: "HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> snpresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snpresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(197) HOST_State.distinct(37) HSTATE_invariant3 i201)
done
show goal149: "HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(169) HOST_State.distinct(307) HSTATE_invariant3 i201)
done
show goal150: "HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) assms i540 nextDTHDataFrom_general_rule_5_0)
done
show goal151: "HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> htddatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) HTDDataPending_htddatas_invariant2 assms i673 nextHTDDataPending_general_rule_6_0)
done
show goal152: "HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> htddatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) i215)
done
show goal153: "HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> reqs2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(169) HOST_State.distinct(247) HSTATE_invariant3 i201)
done
show goal154: "HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> reqs1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) i208)
done
show goal155: "HSTATE SD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> reqs2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(169) HOST_State.distinct(197) HSTATE_invariant3 i201)
done
show goal156: "HSTATE SD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> reqs1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) i208)
done
show goal157: "HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextReqIs RdOwn ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> dthdatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextReqIs RdOwn ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0\<close>)
done
show goal158: "HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextReqIs RdOwn ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> dthdatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) assms dthdatas1_HostInvalidDirtyEvict i208 i591)
done
show goal159: "HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextReqIs RdShared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> dthdatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) i209)
done
show goal160: "HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextReqIs RdShared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> dthdatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) assms dthdatas1_HostInvalidDirtyEvict i208 i591)
done
show goal161: "CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> (CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> (CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(169) HOST_State.distinct(37) HSTATE_invariant3 i201)
done
show goal162: "CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> (CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> (CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i199)
done
show goal163: "CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> reqs2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<or> nextReqIs CleanEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> nextReqIs CleanEvictNoData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> nextReqIs RdOwn ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(107) HOST_State.distinct(197) HSTATE_invariant3 i201)
done
show goal164: "CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> reqs1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<or> nextReqIs CleanEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> nextReqIs CleanEvictNoData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> nextReqIs RdOwn ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) i208)
done
show goal165: "CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> HSTATE IB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE SB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE MB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) i201)
done
show goal166: "CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> HSTATE IB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE SB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE MB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) i201)
done
show goal167: "CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPendingIs GO_WritePullDrop ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE SB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE ID ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) aux_r34_9)
done
show goal168: "CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPendingIs GO_WritePullDrop ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE SB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE ID ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i199)
done
show goal169: "CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) aux_r46)
done
show goal170: "CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) aux2_r46)
done
show goal171: "CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE ISA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE ISD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SIAC ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(107) HOST_State.distinct(197) HSTATE_invariant3 i201)
done
show goal172: "CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE ISA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE ISD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SIAC ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i199)
done
show goal173: "HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> dthdatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> dthdatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) assms dthdatas1_HostInvalidDirtyEvict dthdatas2_HostInvalidDirtyEvict i591)
done
show goal174: "CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i661)
done
show goal175: "CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i661)
done
show goal176: "HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> dthdatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> dthdatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) assms dthdatas1_HostInvalidDirtyEvict dthdatas2_HostInvalidDirtyEvict i591)
done
show goal177: "HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> dthdatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> dthdatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) assms dthdatas1_HostInvalidDirtyEvict dthdatas2_HostInvalidDirtyEvict i591)
done
show goal178: "nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) assms i672 nextHTDDataPending_general_rule_6_0)
done
show goal179: "nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) assms i673 nextHTDDataPending_general_rule_6_0)
done
show goal180: "nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) assms i540 nextDTHDataFrom_general_rule_5_0)
done
show goal181: "nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) assms i540 nextDTHDataFrom_general_rule_5_0)
done
show goal182: "HSTATE SA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> dthdatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> dthdatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) assms dthdatas1_HostInvalidDirtyEvict dthdatas2_HostInvalidDirtyEvict i591)
done
show goal183: "HSTATE SD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> \<not> CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i199)
done
show goal184: "HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> (\<not> CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> nextSnpRespIs RspIFwdM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> (\<not> CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> nextSnpRespIs RspIFwdM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1)"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(169) HOST_State.distinct(197) HSTATE_invariant3 i201)
done
show goal185: "CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) assms i540 nextDTHDataFrom_general_rule_5_0)
done
show goal186: "CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) HostInvalidDirtyEvict_nextGOPendingIs_otherside assms i575)
done
show goal187: "CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i199)
done
show goal188: "CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i199)
done
show goal189: "CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i661)
done
show goal190: "CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) HostInvalidDirtyEvict_nextGOPendingIs_otherside assms i575)
done
show goal191: "snpresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<longrightarrow> reqresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) GTS_def i199 i3x i4x snpresps1_HostInvalidDirtyEvict)
done
show goal192: "snpresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<longrightarrow> reqresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) i214)
done
show goal193: "HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextReqIs RdShared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(107) HOST_State.distinct(169) HSTATE_invariant3 i201)
done
show goal194: "HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextReqIs RdShared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) i209)
done
show goal195: "HSTATE SD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) assms i540 nextDTHDataFrom_general_rule_5_0)
done
show goal196: "HSTATE SD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) HostInvalidDirtyEvict_nextGOPendingIs_otherside assms i575)
done
show goal197: "HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> (nextSnpRespIs RspIFwdM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> nextSnpRespIs RspSFwdM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) HostInvalidDirtyEvict_nextGOPendingIs_otherside assms i575)
done
show goal198: "HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> (nextSnpRespIs RspIFwdM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> nextSnpRespIs RspSFwdM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(169) HOST_State.distinct(197) HSTATE_invariant3 i201)
done
show goal199: "HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(169) HOST_State.distinct(37) HSTATE_invariant3 i201)
done
show goal200: "C_msg_P_same SIA (nextGOPendingIs GO_WritePull) nextEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) HostInvalidDirtyEvict_nextGOPendingIs_otherside assms i538 i575 nextEvict_HostInvalidDirtyEvict_invariant)
done
show goal201: "C_msg_P_same SIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextReqIs RdShared T i) ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) HostInvalidDirtyEvict_nextGOPendingIs_otherside assms i209 i575)
done
show goal202: "CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> snps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snpresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> htddatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) i213 i214 i215)
done
show goal203: "CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> snps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snpresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> htddatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 htddatas2_HostInvalidDirtyEvict i208 i317 i618old snpresps1_HostInvalidDirtyEvict snps1_HostInvalidDirtyEvict)
done
show goal204: "C_msg_P_same SIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextSnoopPending T i) ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) CSTATE_different1 CSTATE_general_rule_3_0 MESI_State.distinct(539) i211 i4x nextSnoopPending_empty_not_rule_8_1)
done
show goal205: "CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> HSTATE IB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE SB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE MB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) i201)
done
show goal206: "CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> HSTATE IB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE SB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE MB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) i201)
done
show goal207: "C_msg_P_same SIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextDTHDataPending T i) ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) CSTATE_different1 CSTATE_general_rule_3_0 MESI_State.distinct(539) i1x i4x i575 nextGOPendingIs_general_rule_8_0)
done
show goal208: "CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) assms i540 nextDTHDataFrom_general_rule_5_0)
done
show goal209: "CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) HostInvalidDirtyEvict_nextGOPendingIs_otherside assms i575)
done
show goal210: "C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) nextEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (metis CSTATE_general_rule_3_0 C_msg_P_same_def HostInvalidDirtyEvict_nextEvict_otherside aux_r34_9 i1x i324 i873)
done
show goal211: "C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextReqIs RdShared T i) ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) CSTATE_different2 CSTATE_general_rule_3_0 MESI_State.distinct(289) aux_r34_9 i1x i4x i572 nextReqIs_otherside_rule_1_0)
done
show goal212: "C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextSnoopPending T i) ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) aux_r34_9 i211 nextSnoopPending_empty_not_rule_8_1)
done
show goal213:  "CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPendingIs GO_WritePullDrop ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE SB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE IB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE ID ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) i201)
done
show goal214:  "CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPendingIs GO_WritePullDrop ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE SB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE IB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE ID ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) i201)
done
show goal215: "C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextDTHDataPending T i) ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (metis HostInvalidDirtyEvict_nextHTDDataPending_otherside aux_r34_9 i1x i591 nextDTHDataPending_def numeral_One sendEvictResp_def zero_neq_numeral)
done
show goal216: "CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i915)
done
show goal217: "CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE SA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE SB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 i207)
done
show goal218: "CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE SA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE SB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) assms i673 nextHTDDataPending_general_rule_6_0)
done
show goal219: "CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1)"
apply  (insert assms)
apply (smt (verit) aux2_r46)
done
show goal220: "CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0)"
apply  (insert assms)
apply (smt (verit) assms i673 nextHTDDataPending_general_rule_6_0)
done
show goal221: "C_not_C_msg Modified IMAD nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i667 i676 nextGOPending_HostInvalidDirtyEvict)
done
show goal222: "CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> HSTATE MD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i339 i538 nextStore_nextEvict_exclusive)
done
show goal223: "CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> nextStore ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 CSTATE_inequality_invariant MESI_State.distinct(343) assms)
done
show goal224: "CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> nextStore ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 i340 nextStore_general_rule_5_0)
done
show goal225: "CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> snps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snpresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) i213 i214)
done
show goal226: "CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> snps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snpresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i667 nextGOPending_HostInvalidDirtyEvict)
done
show goal227: "snpresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<longrightarrow> reqresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) GTS_def i199 i3x i4x snpresps1_HostInvalidDirtyEvict)
done
show goal228: "snpresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<longrightarrow> reqresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) i214)
done
show goal229: "CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i915)
done
show goal230: "CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> HSTATE MD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i667 nextGOPending_HostInvalidDirtyEvict)
done
show goal231: "CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> HSTATE MD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i915)
done
show goal232: "CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> HSTATE MD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i915)
done
show goal233: "CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> nextStore ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i915)
done
show goal234: "CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> nextStore ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i915)
done
show goal235: "C_msg_P_same IMA nextGOPending nextStore ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i670 i671)
done
show goal236: "CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE ISA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i670)
done
show goal237: "CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE ISA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i671)
done
show goal238: "C_msg_P_oppo IMA nextGOPending (\<lambda>T i. \<not> nextSnoopPending T i) ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i670 i671)
done
show goal239: "C_msg_P_oppo SMA nextGOPending (\<lambda>T i. \<not> nextSnoopPending T i) ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i670 i671)
done
show goal240: "C_msg_P_oppo ISA nextGOPending (\<lambda>T i. \<not> nextSnoopPending T i) ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i670 i671)
done
show goal241: "CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i670)
done
show goal242: "CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i671)
done
show goal243: "CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE ISD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> \<not> CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> \<not> CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> \<not> ((CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> \<not> CSTATE ISA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> \<not> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> \<not> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> \<not> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> \<not> CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> \<not> CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (metis CSTATE_general_rule_3_0 CSTATE_inequality_invariant i199 i1x i4x i603 i604 i605 i606 i607 i665 i673 i675 i676 i915 nextGOPending_yes_reqresp_rule_8_1 nextHTDDataPending_general_rule_6_0)
done
show goal244: "CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE ISD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> ((CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> \<not> CSTATE ISA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (metis CSTATE_general_rule_3_0 i1x i605 i607 i667 i915 nextGOPending_yes_reqresp_rule_8_1)
done
show goal245: "CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> dthdatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> (dthdatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<or> HSTATE MB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]))"
apply  (insert assms)
apply (smt (verit) assms dthdatas1_HostInvalidDirtyEvict dthdatas2_HostInvalidDirtyEvict i591)
done
show goal246: "CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> dthdatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> (dthdatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<or> HSTATE MB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]))"
apply  (insert assms)
apply (smt (verit) assms dthdatas1_HostInvalidDirtyEvict dthdatas2_HostInvalidDirtyEvict i591)
done
show goal247: "CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> dthdatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) assms dthdatas1_HostInvalidDirtyEvict i208 i591)
done
show goal248: "CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> dthdatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) assms dthdatas2_HostInvalidDirtyEvict i208 i591)
done
show goal249: "C_msg_P_same SMA nextGOPending nextStore ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i670 i671)
done
show goal250: "CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i573)
done
show goal251: "CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i573)
done
show goal252: "CSTATE ISD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE ISA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE ISDI ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> nextLoad ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i207 i368 i602 nextLoad_HostInvalidDirtyEvict)
done
show goal253: "CSTATE ISD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE ISA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE ISDI ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> nextLoad ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i146 i542 i602 i603 nextLoad_HostInvalidDirtyEvict)
done
show goal254: "CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> nextStore ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i339 i573 i915 nextStore_general_rule_5_0)
done
show goal255: "CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> nextStore ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i340 i573 i915 nextStore_general_rule_5_0)
done
show goal256: "CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE ISA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> (dthdatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<or> nextSnpRespIs RspSFwdM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> HSTATE SD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]))"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms dthdatas1_HostInvalidDirtyEvict i208 i591 i676)
done
show goal257: "CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE ISA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> (dthdatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<or> nextSnpRespIs RspSFwdM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> HSTATE SD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]))"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms dthdatas2_HostInvalidDirtyEvict i208 i493 i591)
done
show goal258: "CSTATE ISA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE SB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i670)
done
show goal259: "CSTATE ISA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE SB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i671)
done
show goal260: "CSTATE ISDI ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE MD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE ID ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE SB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) assms i672 nextHTDDataPending_general_rule_6_0)
done
show goal261: "CSTATE ISDI ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE MD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE ID ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE SB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i542)
done
show goal262: "CSTATE ISDI ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> snps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snpresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> reqresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_different1 CSTATE_general_rule_3_0 MESI_State.distinct(311) i4x)
done
show goal263: "CSTATE ISDI ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> snps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snpresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> reqresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i542)
done
show goal264: "CSTATE ISDI ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> nextReqIs RdOwn ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> \<not> HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(169) HOST_State.distinct(37) HSTATE_invariant3 i201)
done
show goal265: "CSTATE ISDI ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> nextReqIs RdOwn ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> \<not> HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextReqIs RdOwn ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0\<close>)
done
show goal266: "CSTATE Invalid ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> reqresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i68 reqs1_empty_not_nextReqIs_general_invariant)
done
show goal267: "CSTATE Invalid ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> reqresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 i382 reqresps2_HostInvalidDirtyEvict)
done
show goal268: "CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i674)
done
show goal269: "CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i675)
done
show goal270: "CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i674)
done
show goal271: "CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i675)
done
show goal272: "CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> snps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snpresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) i213 i214)
done
show goal273: "CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> snps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snpresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i915)
done
show goal274: "CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> reqresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> htddatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i915)
done
show goal275: "CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> reqresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> htddatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i915)
done
show goal276: "nextReqIs RdOwn ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextReqIs RdOwn ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0\<close>)
done
show goal277: "nextReqIs RdOwn ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i393 i915 nextReqIs_HostInvalidDirtyEvict_otherside_1)
done
show goal278: "CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> CXL_SPG_used ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> nextReqIs RdOwn ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i915)
done
show goal279: "CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> CXL_SPG_used ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> nextReqIs RdOwn ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i915)
done
show goal280: "CSTATE ISD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i602 i609)
done
show goal281: "CSTATE ISD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i603 i609)
done
show goal282: "CSTATE ISD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i602)
done
show goal283: "CSTATE ISD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i602 i603)
done
show goal284: "HSTATE MD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> snpresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snpresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(169) HOST_State.distinct(307) HSTATE_invariant3 i201)
done
show goal285: "HSTATE MD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(107) HOST_State.distinct(307) HSTATE_invariant3 i201)
done
show goal286: "HSTATE MD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) assms i540 nextDTHDataFrom_general_rule_5_0)
done
show goal287: "HSTATE MD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> nextReqIs CleanEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> nextReqIs CleanEvictNoData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) i209)
done
show goal288: "HSTATE MD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> nextReqIs CleanEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> \<not> nextReqIs CleanEvictNoData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) assms i540 nextDTHDataFrom_general_rule_5_0)
done
show goal289: "HSTATE MD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(169) HOST_State.distinct(307) HSTATE_invariant3 i201)
done
show goal290: "HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(169) HOST_State.distinct(269) HSTATE_invariant3 i201)
done
show goal291: "HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) assms i540 nextDTHDataFrom_general_rule_5_0)
done
show goal292: "HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> snpresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) i214)
done
show goal293: "HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> snpresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) assms i540 nextDTHDataFrom_general_rule_5_0)
done
show goal294: "HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> nextReqIs CleanEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> nextReqIs CleanEvictNoData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) i209)
done
show goal295: "HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> nextReqIs CleanEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> \<not> nextReqIs CleanEvictNoData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) assms i540 nextDTHDataFrom_general_rule_5_0)
done
show goal296: "HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> reqs2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(169) HOST_State.distinct(269) HSTATE_invariant3 i201)
done
show goal297: "HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> reqs1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i208 i676)
done
show goal298: "HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> reqresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(169) HOST_State.distinct(269) HSTATE_invariant3 i201)
done
show goal299: "HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> reqresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) assms i540 nextDTHDataFrom_general_rule_5_0)
done
show goal300: "(HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE SA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])) \<and> snpresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<longrightarrow> htddatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<or> CSTATE ISDI ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) i215)
done
show goal301: "(HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE SA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])) \<and> snpresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<longrightarrow> htddatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<or> CSTATE ISDI ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) i214)
done
show goal302: "nextSnpRespIs RspSFwdM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SIAC ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 HostInvalidDirtyEvict_nextSnpRespIs_sameside assms i441 i674 i915)
done
show goal303: "nextSnpRespIs RspSFwdM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SIAC ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 HostInvalidDirtyEvict_nextSnpRespIs_otherside assms i442 i675 i915)
done
show goal304: "(CSTATE Invalid ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE ISDI ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> nextReqIs RdOwn ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(197) HOST_State.distinct(289) HSTATE_invariant3 i201)
done
show goal305: "(CSTATE Invalid ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE ISDI ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> nextReqIs RdOwn ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(197) HOST_State.distinct(289) HSTATE_invariant3 i201)
done
show goal306: "CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i493)
done
show goal307: "CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i676)
done
show goal308: "CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i493 i699)
done
show goal309: "CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i676)
done
show goal310: "CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i573)
done
show goal311: "CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i573)
done
show goal312: "CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i606)
done
show goal313: "CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i606 i607)
done
show goal314: "CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_general_rule_3_0 i2x i339 i538 nextStore_nextEvict_exclusive)
done
show goal315: "CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) empty_no_snoop_variant2 i213)
done
show goal316: "CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_general_rule_3_0 i2x i339 i538 nextStore_nextEvict_exclusive)
done
show goal317: "CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) empty_no_snoop2 i213)
done
show goal318: "CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i606 i609)
done
show goal319: "CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i607 i609)
done
show goal320: "CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i670)
done
show goal321: "CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i671)
done
show goal322: "CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i661)
done
show goal323: "CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i661)
done
show goal324: "CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i661)
done
show goal325: "CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i661)
done
show goal326: "CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i493)
done
show goal327: "CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i676)
done
show goal328: "CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i493)
done
show goal329: "CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i676)
done
show goal330: "CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> reqs1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) i208)
done
show goal331: "CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> reqs2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i676)
done
show goal332: "CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> snps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snpresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> reqresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> htddatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i493)
done
show goal333: "CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> snps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snpresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> reqresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> htddatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i676)
done
show goal334: "HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextReqIs RdShared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> dthdatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) i209)
done
show goal335: "HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextReqIs RdShared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> dthdatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) assms dthdatas1_HostInvalidDirtyEvict i208 i591)
done
show goal336: "HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> \<not> CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i493 i674 i675 i676)
done
show goal337: "nextReqIs RdOwn ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE Invalid ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextReqIs RdOwn ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0\<close>)
done
show goal338: "nextReqIs RdOwn ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> \<not> CSTATE Invalid ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 i495 nextReqIs_HostInvalidDirtyEvict_otherside_1)
done
show goal339: "HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextReqIs RdOwn ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextReqIs RdOwn ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0\<close>)
done
show goal340: "HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextReqIs RdOwn ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i497 nextReqIs_HostInvalidDirtyEvict_otherside_1)
done
show goal341: "HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextReqIs RdOwn ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> dthdatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextReqIs RdOwn ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0\<close>)
done
show goal342: "HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextReqIs RdOwn ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> dthdatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) assms dthdatas1_HostInvalidDirtyEvict i208 i591)
done
show goal343: "CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> snps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snpresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) i213 i214)
done
show goal344: "CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> snps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snpresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 i208 i317 i583 snpresps1_HostInvalidDirtyEvict snps1_HostInvalidDirtyEvict)
done
show goal345: "CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i502 i600 i606 i607 i671 i673 nextSnoopIs_general_rule_8_0)
done
show goal346: "CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i503 i601 i606 i670 i672 nextSnoopIs_general_rule_8_0)
done
show goal347: "CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> CXL_SPG_used ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> nextReqIs CleanEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> nextReqIs CleanEvictNoData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i502 i506 i600 i671 i673 nextSnoopIs_general_rule_8_0)
done
show goal348: "CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> CXL_SPG_used ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> nextReqIs CleanEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> nextReqIs CleanEvictNoData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i503 i507 i601 i670 i672 nextSnoopIs_general_rule_8_0)
done
show goal349: "CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i502 i506 i600 i671 i673 nextSnoopIs_general_rule_8_0)
done
show goal350: "CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i503 i507 i560 i601 i670 i672 nextSnoopIs_general_rule_8_0)
done
show goal351: "CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i915)
done
show goal352: "CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i915)
done
show goal353: "HSTATE ID ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> \<not> CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i493 i674 i675 i676)
done
show goal354: "HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextReqIs DirtyEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> (\<not> CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> \<not> CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> \<not> CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) i209)
done
show goal355: "HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextReqIs DirtyEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> (\<not> CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> \<not> CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> \<not> CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) assms i199 i872 nextReqIs_HostInvalidDirtyEvict_otherside_1)
done
show goal356: "HSTATE ID ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextReqIs RdOwn ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextReqIs RdOwn ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0\<close>)
done
show goal357: "HSTATE ID ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextReqIs RdOwn ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i497 nextReqIs_HostInvalidDirtyEvict_otherside_1)
done
show goal358: "CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i915)
done
show goal359: "CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i915)
done
show goal360: "C_msg_P_oppo SMAD nextGOPending (\<lambda>T i. \<not> nextSnoopPending T i) ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i915)
done
show goal361: "HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextReqIs CleanEvictNoData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> CSTATE SIAC ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) i209)
done
show goal362: "HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextReqIs CleanEvictNoData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> CSTATE SIAC ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 i947 nextReqIs_HostInvalidDirtyEvict_otherside_1)
done
show goal363: "nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> reqresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<or> nextReqRespStateIs Invalid (reqresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]))"
apply  (insert assms)
apply (smt (verit) assms i522 i544 reqresps2_HostInvalidDirtyEvict)
done
show goal364: "nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> reqresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<or> nextReqRespStateIs Invalid (reqresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]))"
apply  (insert assms)
apply (smt (verit) HostInvalidDirtyEvict_nextGOPendingIs_otherside assms i575)
done
show goal365: "HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextReqIs CleanEvictNoData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> nextEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) i209)
done
show goal366: "HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextReqIs CleanEvictNoData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> nextEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) HostInvalidDirtyEvict_nextEvict_otherside i562 nextReqIs_HostInvalidDirtyEvict_otherside_1)
done
show goal367: "HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextReqIs CleanEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> nextEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) i209)
done
show goal368: "HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextReqIs CleanEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> nextEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) HostInvalidDirtyEvict_nextEvict_otherside i557 i562 nextReqIs_HostInvalidDirtyEvict_otherside_1)
done
show goal369: "HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextReqIs CleanEvictNoData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE ISDI ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) i209)
done
show goal370: "HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextReqIs CleanEvictNoData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE ISDI ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i542)
done
show goal371: "HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextReqIs CleanEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE ISDI ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) i209)
done
show goal372: "HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextReqIs CleanEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE ISDI ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i542)
done
show goal373: "HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextReqIs CleanEvictNoData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) i209)
done
show goal374: "HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextReqIs CleanEvictNoData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i661)
done
show goal375: "HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextReqIs CleanEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) i209)
done
show goal376: "HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextReqIs CleanEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i661)
done
show goal377: "CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> htddatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<or> (CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> htddatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i674)
done
show goal378: "CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> htddatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<or> (CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> htddatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i675)
done
show goal379: "nextReqIs DirtyEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> nextEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) i209)
done
show goal380: "nextReqIs DirtyEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> nextEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) assms i199 i872 nextReqIs_HostInvalidDirtyEvict_otherside_1)
done
show goal381: "nextReqIs DirtyEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) i209)
done
show goal382: "nextReqIs DirtyEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) assms i199 i872 nextReqIs_HostInvalidDirtyEvict_otherside_1)
done
show goal383: "nextReqIs DirtyEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE ISDI ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) i209)
done
show goal384: "nextReqIs DirtyEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE ISDI ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) assms i199 i872 nextReqIs_HostInvalidDirtyEvict_otherside_1)
done
show goal385: "nextReqIs DirtyEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> reqresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<or> nextReqRespStateIs Invalid (reqresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]))"
apply  (insert assms)
apply (smt (verit) i209)
done
show goal386: "nextReqIs DirtyEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> reqresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<or> nextReqRespStateIs Invalid (reqresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]))"
apply  (insert assms)
apply (smt (verit) assms i199 i872 nextReqIs_HostInvalidDirtyEvict_otherside_1)
done
show goal387: "CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> (CSTATE ISA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1)"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i604 i609)
done
show goal388: "CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> (CSTATE ISA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0)"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i605 i609)
done
show goal389: "CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i604 i609)
done
show goal390: "CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i605 i609)
done
show goal391: "CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i604 i609)
done
show goal392: "CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i605 i609)
done
show goal393: "CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> snps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snpresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> reqresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i573)
done
show goal394: "CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> snps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snpresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> reqresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i605 i606)
done
show goal395: "CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) assms i199 i872 nextReqIs_HostInvalidDirtyEvict_otherside_1)
done
show goal396: "CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) i209)
done
show goal397: "nextReqIs CleanEvictNoData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> nextReqIs CleanEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SIAC ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) i209)
done
show goal398: "nextReqIs CleanEvictNoData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> nextReqIs CleanEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SIAC ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i199 i557 i947 nextReqIs_HostInvalidDirtyEvict_otherside_1)
done
show goal399: "CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> HSTATE MD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i674 i675)
done
show goal400: "CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i674)
done
show goal401: "CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i675)
done
show goal402: "nextReqIs CleanEvictNoData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> nextReqIs CleanEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> nextEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) i209)
done
show goal403: "nextReqIs CleanEvictNoData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> nextReqIs CleanEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> nextEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) HostInvalidDirtyEvict_nextEvict_otherside i562 nextReqIs_HostInvalidDirtyEvict_otherside_1)
done
show goal404: "nextReqIs CleanEvictNoData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> nextReqIs CleanEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE ISDI ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) i209)
done
show goal405: "nextReqIs CleanEvictNoData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> nextReqIs CleanEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE ISDI ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i542)
done
show goal406: "nextReqIs CleanEvictNoData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> nextReqIs CleanEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) i209)
done
show goal407: "nextReqIs CleanEvictNoData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> nextReqIs CleanEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i661)
done
show goal408: "CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextReqIs RdShared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) i209)
done
show goal409: "CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextReqIs RdShared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i572 nextReqIs_HostInvalidDirtyEvict_otherside_1)
done
show goal410: "HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> \<not> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> \<not> CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> \<not> CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i573)
done
show goal411: "HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> ((CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> (nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0)) \<and> \<not> ((CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> (nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1))"
apply  (insert assms)
apply (metis CSTATE_general_rule_3_0 i1x i2x i370 i538 i667 i673 i915 nextGOPending_yes_reqresp_rule_8_1 nextHTDDataPending_general_rule_6_0 nextStore_nextEvict_exclusive)
done
show goal412: "nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(139) HOST_State.distinct(169) HSTATE_invariant3 i201)
done
show goal413: "CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> \<not> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> \<not> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i661)
done
show goal414: "CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i661)
done
show goal415: "nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) HostInvalidDirtyEvict_nextGOPendingIs_otherside assms i575)
done
show goal416: "nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) HostInvalidDirtyEvict_nextGOPendingIs_otherside assms i575)
done
show goal417: "CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE MB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (metis CSTATE_general_rule_3_0 i1x i604 i606 i672 nextHTDDataPending_general_rule_6_0)
done
show goal418: "CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE MB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (metis CSTATE_general_rule_3_0 i1x i605 i607 i673 nextHTDDataPending_general_rule_6_0)
done
show goal419: "CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> snps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snpresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> htddatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) i213 i214 i215)
done
show goal420: "CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> snps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snpresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> htddatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i661)
done
show goal421: "CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i661)
done
show goal422: "CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i661)
done
show goal423: "CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i661)
done
show goal424: "CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i661)
done
show goal425: "HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(107) HOST_State.distinct(139) HOST_State.distinct(169) HOST_State.distinct(37) HSTATE_invariant3 i201)
done
show goal426: "CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPendingIs GO_WritePullDrop ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE IB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) i201)
done
show goal427: "CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPendingIs GO_WritePullDrop ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE IB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) i201)
done
show goal428: "HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> dthdatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> dthdatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) assms dthdatas1_HostInvalidDirtyEvict dthdatas2_HostInvalidDirtyEvict i591)
done
show goal429: "CSTATE Invalid ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 i592 nextSnoopIs_general_rule_8_0)
done
show goal430: "CSTATE Invalid ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 i593 nextSnoopIs_general_rule_8_0)
done
show goal431: "CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i661)
done
show goal432: "CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i676)
done
show goal433: "HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> htddatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<or> (CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> htddatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(247) HOST_State.distinct(289) HSTATE_invariant3 i201)
done
show goal434: "HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> htddatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<or> (CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> htddatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) empty_no_snoop_variant2 i213)
done
show goal435: "CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> snps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snpresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) i213 i214)
done
show goal436: "CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> snps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snpresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i915)
done
show goal437: "HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(197) HOST_State.distinct(289) HSTATE_invariant3 i201)
done
show goal438: "HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) empty_no_snoop_variant2 i213)
done
show goal439: "HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE ID ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE ISD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE ISA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i602)
done
show goal440: "HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE ID ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE ISD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> \<not> CSTATE ISA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i602 i603)
done
show goal441: "HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE ID ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i604)
done
show goal442: "HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE ID ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> \<not> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i604 i605)
done
show goal443: "HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE ID ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i606)
done
show goal444: "HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE ID ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> \<not> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i606 i607)
done
show goal445: "HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE ID ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> (CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> (nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0))"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 i207)
done
show goal446: "HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE ID ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> (nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0))"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 CSTATE_inequality_invariant MESI_State.distinct(343) assms)
done
show goal447: "HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE ID ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> (CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> (nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0))"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i915)
done
show goal448: "HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE ID ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> (CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> (nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1))"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i665 i673 nextGOPending_HostInvalidDirtyEvict nextHTDDataPending_general_rule_6_0)
done
show goal449: "HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE ID ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> (nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1))"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms aux2_r46 i667 nextGOPending_HostInvalidDirtyEvict)
done
show goal450: "HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<or> HSTATE ID ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> (CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> (nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1))"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i915)
done
show goal451: "CSTATE ISD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> htddatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<or> (CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> htddatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i662)
done
show goal452: "CSTATE ISD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> htddatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<or> (CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> htddatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i663)
done
show goal453: "CSTATE ISA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> htddatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<or> (CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> htddatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i670)
done
show goal454: "CSTATE ISA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> htddatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<or> (CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> htddatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i671)
done
show goal455: "CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> htddatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<or> (CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> htddatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 i207)
done
show goal456: "CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> htddatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<or> (CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> htddatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) empty_no_snoop_variant2 i213)
done
show goal457: "CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> htddatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 htddatas2_HostInvalidDirtyEvict i208 i620 nextSnoopIs_general_rule_8_0)
done
show goal458: "CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> htddatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) empty_no_snoop_variant2 i213)
done
show goal459: "CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> htddatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i573)
done
show goal460: "CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> htddatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i573)
done
show goal461: "CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> htddatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i573)
done
show goal462: "CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> htddatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i573)
done
show goal463: "CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> htddatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i915)
done
show goal464: "CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> htddatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i915)
done
show goal465: "CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> htddatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i662)
done
show goal466: "CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> htddatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i663)
done
show goal467: "CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> htddatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i573)
done
show goal468: "CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> htddatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i573)
done
show goal469: "CSTATE ISD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE ISA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> HSTATE MD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i602)
done
show goal470: "CSTATE ISD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE ISA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> HSTATE MD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i602 i603)
done
show goal471: "CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> (nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<longrightarrow> \<not> HSTATE MD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 i207)
done
show goal472: "CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> (nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<longrightarrow> \<not> HSTATE MD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i665 i673 nextGOPending_HostInvalidDirtyEvict nextHTDDataPending_general_rule_6_0)
done
show goal473: "CSTATE ISD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i602)
done
show goal474: "CSTATE ISD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i602 i603)
done
show goal475: "CSTATE ISA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i670)
done
show goal476: "CSTATE ISA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i671)
done
show goal477: "CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> (CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1)"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i665 nextGOPending_HostInvalidDirtyEvict)
done
show goal478: "CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> (CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0)"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i607 i611)
done
show goal479: "CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE ISA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> \<not> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i606 i609)
done
show goal480: "CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE ISA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i607 i609)
done
show goal481: "CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i675)
done
show goal482: "CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i606 i607)
done
show goal483: "CSTATE ISD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i602 i609)
done
show goal484: "CSTATE ISD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i603 i609)
done
show goal485: "CSTATE ISA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i670)
done
show goal486: "CSTATE ISA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i671)
done
show goal487: "CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 i207)
done
show goal488: "CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i665 nextGOPending_HostInvalidDirtyEvict)
done
show goal489: "CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 i207)
done
show goal490: "CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) assms i673 nextHTDDataPending_general_rule_6_0)
done
show goal491: "HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i670)
done
show goal492: "HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> \<not> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i671)
done
show goal493: "HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i604 i606 i611)
done
show goal494: "HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> \<not> CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i605 i607 i611)
done
show goal495: "HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> (nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0))"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 CSTATE_inequality_invariant MESI_State.distinct(343) assms)
done
show goal496: "HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> (nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1))"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms aux2_r46 i667 nextGOPending_HostInvalidDirtyEvict)
done
show goal497: "HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> (CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> (nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0))"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i915)
done
show goal498: "HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> (CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> (nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1))"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i915)
done
show goal499: "HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i661)
done
show goal500: "HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i661)
done
show goal501: "HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE ISD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i662)
done
show goal502: "HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE ISD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> \<not> CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> \<not> CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i663)
done
show goal503: "HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> (CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0)"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 i207)
done
show goal504: "HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> (CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1)"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i665 nextGOPending_HostInvalidDirtyEvict)
done
show goal505: "HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0)"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 CSTATE_inequality_invariant MESI_State.distinct(343) assms)
done
show goal506: "HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1)"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i667 nextGOPending_HostInvalidDirtyEvict)
done
show goal507: "HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> (CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0)"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i915)
done
show goal508: "HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> (CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1)"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i915)
done
show goal509: "HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE ISA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i670)
done
show goal510: "HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE ISA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> \<not> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> \<not> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i671)
done
show goal511: "HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) assms i672 nextHTDDataPending_general_rule_6_0)
done
show goal512: "HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) assms i673 nextHTDDataPending_general_rule_6_0)
done
show goal513: "HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i674)
done
show goal514: "HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i675)
done
show goal515: "HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i493)
done
show goal516: "HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i676)
done
show goal517: "CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> snpresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> reqresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i606 i609)
done
show goal518: "CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> snpresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> reqresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i606 i607)
done
show goal519: "CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> snpresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) i213 i214)
done
show goal520: "CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> snpresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r46)
done
show goal521: "CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i606)
done
show goal522: "CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i606 i607)
done
show goal523: "CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i670)
done
show goal524: "CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i671)
done
show goal525: "CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 i685 nextSnoopIs_general_rule_8_0)
done
show goal526: "CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 i207 i686 nextSnoopIs_general_rule_8_0)
done
show goal527: "CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i606)
done
show goal528: "CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i606 i607)
done
show goal529: "CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i606 i609)
done
show goal530: "CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i607 i609)
done
show goal531: "CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_general_rule_3_0 i2x i339 i538 nextStore_nextEvict_exclusive)
done
show goal532: "CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 i207 i686 i698 nextSnoopIs_general_rule_8_0)
done
show goal533: "HSTATE IB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> \<not> CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i493 i674 i675 i676)
done
show goal534: "HSTATE IB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextReqIs RdOwn ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextReqIs RdOwn ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0\<close>)
done
show goal535: "HSTATE IB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextReqIs RdOwn ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i497 nextReqIs_HostInvalidDirtyEvict_otherside_1)
done
show goal536: "HSTATE SB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i493 i676 i699)
done
show goal537: "HSTATE SB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> length (dthdatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])) \<le> 1 \<and> length (dthdatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])) \<le> 1"
apply  (insert assms)
apply (smt (verit) assms dthdatas1_HostInvalidDirtyEvict dthdatas2_HostInvalidDirtyEvict i591 i884)
done
show goal538: "HSTATE IB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> length (dthdatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])) \<le> 1 \<and> length (dthdatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])) \<le> 1"
apply  (insert assms)
apply (smt (verit) assms dthdatas1_HostInvalidDirtyEvict dthdatas2_HostInvalidDirtyEvict i591 i884)
done
show goal539: "HSTATE SB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i199)
done
show goal540: "HSTATE SB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) assms i540 nextDTHDataFrom_general_rule_5_0)
done
show goal541: "HSTATE MB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> length (dthdatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])) \<le> 1 \<and> length (dthdatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])) \<le> 1"
apply  (insert assms)
apply (smt (verit) assms dthdatas1_HostInvalidDirtyEvict dthdatas2_HostInvalidDirtyEvict i591 i884)
done
show goal542: "HSTATE SB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> dthdatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) assms dthdatas2_HostInvalidDirtyEvict i208 i591)
done
show goal543: "HSTATE SB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> dthdatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) assms dthdatas1_HostInvalidDirtyEvict i208 i591)
done
show goal544: "HSTATE IB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> dthdatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) assms dthdatas2_HostInvalidDirtyEvict i208 i591)
done
show goal545: "HSTATE IB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> dthdatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) assms dthdatas1_HostInvalidDirtyEvict i208 i591)
done
show goal546: "HSTATE MB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> dthdatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) assms dthdatas2_HostInvalidDirtyEvict i208 i591)
done
show goal547: "HSTATE MB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> dthdatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) assms dthdatas1_HostInvalidDirtyEvict i208 i591)
done
show goal548: "HSTATE SB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> snps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(197) HOST_State.distinct(379) HSTATE_invariant3 i201)
done
show goal549: "HSTATE IB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> snps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) GTS_def assms i199 i211 i213 snps1_HostInvalidDirtyEvict)
done
show goal550: "HSTATE MB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> snps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(197) HOST_State.distinct(377) HSTATE_invariant3 i201)
done
show goal551: "HSTATE SB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> reqresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(197) HOST_State.distinct(379) HSTATE_invariant3 i201)
done
show goal552: "HSTATE SB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> reqresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) assms i540 nextDTHDataFrom_general_rule_5_0)
done
show goal553: "HSTATE MB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> reqresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(197) HOST_State.distinct(377) HSTATE_invariant3 i201)
done
show goal554: "HSTATE MB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> reqresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) assms i540 nextDTHDataFrom_general_rule_5_0)
done
show goal555: "HSTATE IB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> reqresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) i1x i591 nextDTHDataFrom_def nextDTHDataFrom_general_rule_5_0)
done
show goal556: "HSTATE IB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> reqresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) assms i540 nextDTHDataFrom_general_rule_5_0)
done
show goal557: "HSTATE SB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i573)
done
show goal558: "HSTATE SB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> \<not> CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i573)
done
show goal559: "HSTATE IB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i573)
done
show goal560: "HSTATE IB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> \<not> CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i573)
done
show goal561: "HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> lastSharer ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextReqIs CleanEvictNoData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) i209)
done
show goal562: "HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> lastSharer ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextReqIs CleanEvictNoData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i674 i675)
done
show goal563: "HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> lastSharer ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextReqIs CleanEvictNoData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> (CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1)"
apply  (insert assms)
apply (smt (verit) i209)
done
show goal564: "HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> lastSharer ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextReqIs CleanEvictNoData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> (CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0)"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 i207)
done
show goal565: "CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> snpresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 i207)
done
show goal566: "CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> snpresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) i214)
done
show goal567: "HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> snpresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) i214)
done
show goal568: "HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> snpresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) assms i540 nextDTHDataFrom_general_rule_5_0)
done
show goal569: "CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 i207)
done
show goal570: "CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) assms i673 nextHTDDataPending_general_rule_6_0)
done
show goal571: "HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> (\<not> CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> nextGOPendingIs GO_WritePullDrop ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> (\<not> CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> nextGOPendingIs GO_WritePullDrop ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1)"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(169) HOST_State.distinct(37) HSTATE_invariant3 i201)
done
show goal572: "HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> snpresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<longrightarrow> \<not> CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(197) HOST_State.distinct(289) HSTATE_invariant3 i201)
done
show goal573: "HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> snpresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<longrightarrow> \<not> CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) i214)
done
show goal574: "HSTATE MD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(169) HOST_State.distinct(307) HSTATE_invariant3 i201)
done
show goal575: "CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1)"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i667 i741 nextGOPending_HostInvalidDirtyEvict)
done
show goal576: "CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0)"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i661)
done
show goal577: "CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> (CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1)"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i915)
done
show goal578: "CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> (CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0)"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i661)
done
show goal579: "HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextReqIs RdOwn ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextReqIs RdOwn ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0\<close>)
done
show goal580: "HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextReqIs RdOwn ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i497 nextReqIs_HostInvalidDirtyEvict_otherside_1)
done
show goal581: "HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE ISA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE ISA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i670 i671)
done
show goal582: "HSTATE MD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE ISA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE ISA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i602 i603 i609)
done
show goal583: "HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> snpresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<longrightarrow> \<not> CSTATE ISA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE ISA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i670 i671)
done
show goal584: "HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> snpresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<longrightarrow> \<not> CSTATE ISA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE ISA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) i214)
done
show goal585: "CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> \<not> CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i604 i605)
done
show goal586: "CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i661)
done
show goal587: "CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> \<not> CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i606 i607)
done
show goal588: "CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i661)
done
show goal589: "CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> (nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1))"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms aux2_r46 i667 i741 nextGOPending_HostInvalidDirtyEvict)
done
show goal590: "CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> (nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0))"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i661)
done
show goal591: "CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i915)
done
show goal592: "CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i661)
done
show goal593: "CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> reqresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i606 i607)
done
show goal594: "CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> reqresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i606)
done
show goal595: "HSTATE IB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) HostInvalidDirtyEvict_nextGOPendingIs_otherside assms i575)
done
show goal596: "HSTATE IB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) assms i540 nextDTHDataFrom_general_rule_5_0)
done
show goal597: "HSTATE IB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE ISA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE ISD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i602)
done
show goal598: "HSTATE IB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE ISA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> \<not> CSTATE ISD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i602 i603)
done
show goal599: "HSTATE IB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i604)
done
show goal600: "HSTATE IB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> \<not> CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i604 i605)
done
show goal601: "HSTATE IB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i606)
done
show goal602: "HSTATE IB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> \<not> CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i606 i607)
done
show goal603: "HSTATE IB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i661)
done
show goal604: "HSTATE IB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) assms i672 i673 nextHTDDataPending_general_rule_6_0)
done
show goal605: "HSTATE ID ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) HostInvalidDirtyEvict_nextGOPendingIs_otherside assms i575)
done
show goal606: "HSTATE ID ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) assms i540 nextDTHDataFrom_general_rule_5_0)
done
show goal607: "HSTATE ID ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> reqresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(169) HOST_State.distinct(247) HSTATE_invariant3 i201)
done
show goal608: "HSTATE ID ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> reqresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) assms i540 nextDTHDataFrom_general_rule_5_0)
done
show goal609: "HSTATE ID ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) assms i673 nextHTDDataPending_general_rule_6_0)
done
show goal610: "HSTATE ID ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) assms i672 nextHTDDataPending_general_rule_6_0)
done
show goal611: "HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextReqIs RdShared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE ISDI ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) i209)
done
show goal612: "HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextReqIs RdShared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE ISDI ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(169) HOST_State.distinct(37) HSTATE_invariant3 i201)
done
show goal613: "HSTATE SD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i661)
done
show goal614: "HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> snpresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<longrightarrow> \<not> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i661)
done
show goal615: "HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> snpresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<longrightarrow> \<not> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) i214)
done
show goal616: "HSTATE MD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i661)
done
show goal617: "snpresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<and> HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i661)
done
show goal618: "snpresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<and> HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) i214)
done
show goal619: "CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> HSTATE MD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> snpresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> reqresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i573)
done
show goal620: "CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> HSTATE MD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> snpresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> reqresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i607 i609)
done
show goal621: "nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> HSTATE MD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextReqIs RdOwn ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextReqIs RdOwn ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0\<close>)
done
show goal622: "nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> HSTATE MD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextReqIs RdOwn ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i497 nextReqIs_HostInvalidDirtyEvict_otherside_1)
done
show goal623: "HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextSnpRespIs RspSFwdM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i676)
done
show goal624: "HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextSnpRespIs RspSFwdM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i493)
done
show goal625: "CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> \<not> CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i675 i676)
done
show goal626: "CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i671)
done
show goal627: "HSTATE MB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> dthdatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) assms dthdatas2_HostInvalidDirtyEvict i208 i591)
done
show goal628: "HSTATE MB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> dthdatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) assms dthdatas1_HostInvalidDirtyEvict i208 i591)
done
show goal629: "HSTATE SA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(169) HOST_State.distinct(223) HSTATE_invariant3 i201)
done
show goal630: "HSTATE SharedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(107) HOST_State.distinct(169) HSTATE_invariant3 i201)
done
show goal631: "CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> HSTATE SA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE ISA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(169) HOST_State.distinct(223) HSTATE_invariant3 i201)
done
show goal632: "CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> HSTATE SA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE ISA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i199)
done
show goal633: "HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> snpresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<longrightarrow> htddatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<or> CSTATE ISDI ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) i215)
done
show goal634: "HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> snpresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<longrightarrow> htddatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<or> CSTATE ISDI ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) i214)
done
show goal635: "HSTATE MB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE ISD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE ISD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i602 i603 i609)
done
show goal636: "HSTATE MB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> CSTATE Invalid ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(169) HOST_State.distinct(377) HSTATE_invariant3 i201)
done
show goal637: "HSTATE MB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> CSTATE Invalid ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) assms i540 nextDTHDataFrom_general_rule_5_0)
done
show goal638: "HSTATE MB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i674 i675)
done
show goal639: "HSTATE MB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> snpresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snpresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(169) HOST_State.distinct(377) HSTATE_invariant3 i201)
done
show goal640: "HSTATE MB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(169) HOST_State.distinct(377) HSTATE_invariant3 i201)
done
show goal641: "HSTATE MB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) assms i540 nextDTHDataFrom_general_rule_5_0)
done
show goal642: "HSTATE MB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(169) HOST_State.distinct(377) HSTATE_invariant3 i201)
done
show goal643: "HSTATE MB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> nextReqIs RdOwn ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(169) HOST_State.distinct(377) HSTATE_invariant3 i201)
done
show goal644: "HSTATE MB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> nextReqIs RdOwn ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextReqIs RdOwn ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0\<close>)
done
show goal645: "HSTATE MB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE ISA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE ISA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i670 i671)
done
show goal646: "CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> HSTATE SB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i199)
done
show goal647: "CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> HSTATE SB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) HostInvalidDirtyEvict_nextGOPendingIs_otherside assms i575)
done
show goal648: "HSTATE IB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> nextReqIs DirtyEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) assms i199 i872 nextReqIs_HostInvalidDirtyEvict_otherside_1)
done
show goal649: "HSTATE IB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> nextReqIs DirtyEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) i209)
done
show goal650: "HSTATE SB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(169) HOST_State.distinct(379) HSTATE_invariant3 i201)
done
show goal651: "HSTATE SB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) assms i540 nextDTHDataFrom_general_rule_5_0)
done
show goal652: "HSTATE SB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i661)
done
show goal653: "HSTATE SB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i661)
done
show goal654: "HSTATE ID ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(169) HOST_State.distinct(247) HSTATE_invariant3 i201)
done
show goal655: "HSTATE ID ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) assms i540 nextDTHDataFrom_general_rule_5_0)
done
show goal656: "CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> nextReqIs RdOwn ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextReqIs RdOwn ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0\<close>)
done
show goal657: "CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> nextReqIs RdOwn ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i676)
done
show goal658: "CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE ISD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i603 i609)
done
show goal659: "CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE ISD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i671)
done
show goal660: "CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> (CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1)"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i665 i827 nextGOPending_HostInvalidDirtyEvict)
done
show goal661: "CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> (CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0)"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i671)
done
show goal662: "CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> (CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1)"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i671)
done
show goal663: "CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> (CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0)"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i671)
done
show goal664: "CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> (CSTATE ISA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1)"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i671)
done
show goal665: "CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> (CSTATE ISA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0)"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i671)
done
show goal666: "CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE ISA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> (CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1)"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i671)
done
show goal667: "CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE ISA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> (CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0)"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i670)
done
show goal668: "HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> snps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) i213)
done
show goal669: "HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> snps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) assms i540 nextDTHDataFrom_general_rule_5_0)
done
show goal670: "HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i661)
done
show goal671: "HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i661)
done
show goal672: "HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(169) HOST_State.distinct(269) HSTATE_invariant3 i201)
done
show goal673: "HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> \<not> CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) assms i540 nextDTHDataFrom_general_rule_5_0)
done
show goal674: "CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> \<not> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> (htddatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<or> CSTATE ISDI ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1)"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i493)
done
show goal675: "CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> (htddatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<or> CSTATE ISDI ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0)"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i676)
done
show goal676: "CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i915)
done
show goal677: "CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i676)
done
show goal678: "CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> snpresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i493)
done
show goal679: "CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> snpresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) i214)
done
show goal680: "CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> (CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1)"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i665 i847 nextGOPending_HostInvalidDirtyEvict)
done
show goal681: "CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> (CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0)"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i671)
done
show goal682: "CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE ISA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> \<not> CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i671 i675)
done
show goal683: "CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE ISA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i671)
done
show goal684: "CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> htddatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i670)
done
show goal685: "CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> htddatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) i215)
done
show goal686: "CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i671)
done
show goal687: "CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i671)
done
show goal688: "CSTATE Invalid ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> snps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 i208 i855 snps1_HostInvalidDirtyEvict)
done
show goal689: "CSTATE Invalid ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> snps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) i213)
done
show goal690: "HSTATE SD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> CSTATE ISD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(169) HOST_State.distinct(197) HSTATE_invariant3 i201)
done
show goal691: "HSTATE SD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> CSTATE ISD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) assms i540 nextDTHDataFrom_general_rule_5_0)
done
show goal692: "HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(169) HOST_State.distinct(197) HSTATE_invariant3 i201)
done
show goal693: "HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i661)
done
show goal694: "CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i915)
done
show goal695: "CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> CSTATE ISAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i915)
done
show goal696: "CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) assms i199 i872 nextReqIs_HostInvalidDirtyEvict_otherside_1)
done
show goal697: "CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) i209)
done
show goal698: "CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> snps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snpresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) i213 i214)
done
show goal699: "CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> snps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snpresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i915)
done
show goal700: "CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> HSTATE IB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> nextReqIs DirtyEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) assms i199 i872 nextReqIs_HostInvalidDirtyEvict_otherside_1)
done
show goal701: "CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> HSTATE IB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> nextReqIs DirtyEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) i209)
done
show goal702: "CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> HSTATE SB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i661)
done
show goal703: "CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> HSTATE SB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) HostInvalidDirtyEvict_nextGOPendingIs_otherside assms i575)
done
show goal704: "HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextReqIs DirtyEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) i209)
done
show goal705: "HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextReqIs DirtyEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) assms i199 i872 nextReqIs_HostInvalidDirtyEvict_otherside_1)
done
show goal706: "HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> (\<not> CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> nextGOPendingIs GO_WritePullDrop ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> (\<not> CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> nextGOPendingIs GO_WritePullDrop ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1)"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(139) HOST_State.distinct(169) HSTATE_invariant3 i201)
done
show goal707: "HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextSnpRespIs RspIFwdM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(197) HOST_State.distinct(289) HSTATE_invariant3 i201)
done
show goal708: "HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextSnpRespIs RspIFwdM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) i214 nextSnpRespIs_property2)
done
show goal709: "length (dthdatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])) \<le> 1"
apply  (insert assms)
apply (smt (verit) assms dthdatas1_HostInvalidDirtyEvict i211 i2150 i591 i60)
done
show goal710: "length (dthdatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])) \<le> 1"
apply  (insert assms)
apply (smt (verit) assms dthdatas2_HostInvalidDirtyEvict i211 i2150 i591 i60)
done
show goal711: "HSTATE IB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) assms i199 i872 nextReqIs_HostInvalidDirtyEvict_otherside_1)
done
show goal712: "HSTATE IB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) i209)
done
show goal713: "HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i674 i675)
done
show goal714: "HSTATE MAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i674 i675)
done
show goal715: "HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> snpresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<longrightarrow> \<not> CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i674 i675)
done
show goal716: "HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> snpresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [] \<longrightarrow> \<not> CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE Shared ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) i214)
done
show goal717: "CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> HSTATE MD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> snpresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> reqresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(197) HOST_State.distinct(307) HSTATE_invariant3 i201)
done
show goal718: "CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> HSTATE MD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> snpresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> reqresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i667 nextGOPending_HostInvalidDirtyEvict)
done
show goal719: "CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> \<not> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> (htddatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<or> CSTATE ISDI ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1)"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i670)
done
show goal720: "CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> (htddatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<or> CSTATE ISDI ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0)"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i671)
done
show goal721: "CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> \<not> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> (htddatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<or> CSTATE ISDI ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1)"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i670)
done
show goal722: "CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> (htddatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<or> CSTATE ISDI ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0)"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i671)
done
show goal723: "CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> dthdatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) assms dthdatas1_HostInvalidDirtyEvict i208 i591)
done
show goal724: "CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> dthdatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) assms dthdatas2_HostInvalidDirtyEvict i208 i591)
done
show goal725: "nextSnpRespIs RspIHitSE ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i670)
done
show goal726: "nextSnpRespIs RspIHitSE ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> \<not> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i671)
done
show goal727: "CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i915)
done
show goal728: "CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i607 i613)
done
show goal729: "CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i915)
done
show goal730: "CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i605 i613)
done
show goal731: "CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i915)
done
show goal732: "CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i607 i613)
done
show goal733: "CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i915)
done
show goal734: "CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i605 i613)
done
show goal735: "CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i915)
done
show goal736: "CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i667 i910 nextGOPending_HostInvalidDirtyEvict)
done
show goal737: "HSTATE MD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i915)
done
show goal738: "HSTATE MD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i915)
done
show goal739: "CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i915)
done
show goal740: "CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i915)
done
show goal741: "HSTATE InvalidM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> \<not> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i915)
done
show goal742: "HSTATE IB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> \<not> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i915)
done
show goal743: "HSTATE ID ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> \<not> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i915)
done
show goal744: "HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextSnpRespIs RspIHitSE ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) i209)
done
show goal745: "HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextSnpRespIs RspIHitSE ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) assms i199 i872 nextReqIs_HostInvalidDirtyEvict_otherside_1)
done
show goal746: "CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> htddatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i493)
done
show goal747: "CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> htddatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) i215)
done
show goal748: "HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> snps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(197) HOST_State.distinct(37) HSTATE_invariant3 i201)
done
show goal749: "CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> htddatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i915)
done
show goal750: "CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> htddatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i915)
done
show goal751: "CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextSnpRespIs RspIFwdM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) i209)
done
show goal752: "CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextSnpRespIs RspIFwdM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) assms i199 i872 nextReqIs_HostInvalidDirtyEvict_otherside_1)
done
show goal753: "CSTATE SIAC ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> HSTATE SA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 assms i676)
done
show goal754: "CSTATE SIAC ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> HSTATE SA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i493 i699)
done
show goal755: "CSTATE SIAC ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) assms i672 nextHTDDataPending_general_rule_6_0)
done
show goal756: "CSTATE SIAC ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) assms i673 nextHTDDataPending_general_rule_6_0)
done
show goal757: "CSTATE SIAC ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPendingState Invalid ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> snps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snpresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> htddatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) i213 i214 i215)
done
show goal758: "CSTATE SIAC ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPendingState Invalid ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> snps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> snpresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = [] \<and> htddatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 htddatas2_HostInvalidDirtyEvict i208 i618old i932 nextGOPending_HostInvalidDirtyEvict nextGOPending_overlooked_reqresp_rule_8_0 snpresps1_HostInvalidDirtyEvict snps1_HostInvalidDirtyEvict)
done
show goal759: "(CSTATE SIAC ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPendingState Invalid ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> (CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> (CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(169) HOST_State.distinct(37) HSTATE_invariant3 i201)
done
show goal760: "(CSTATE SIAC ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPendingState Invalid ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> (CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> (CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(169) HOST_State.distinct(37) HSTATE_invariant3 i201)
done
show goal761: "(CSTATE SIAC ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPendingState Invalid ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> HSTATE MD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> dthdatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> []"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(197) HOST_State.distinct(307) HSTATE_invariant3 i201)
done
show goal762: "(CSTATE SIAC ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPendingState Invalid ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> HSTATE MD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> dthdatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> []"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(197) HOST_State.distinct(307) HSTATE_invariant3 i201)
done
show goal763: "(CSTATE SIAC ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPendingState Invalid ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(197) HOST_State.distinct(289) HSTATE_invariant3 i201)
done
show goal764: "(CSTATE SIAC ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPendingState Invalid ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) HOST_State.distinct(197) HOST_State.distinct(289) HSTATE_invariant3 i201)
done
show goal765: "CSTATE SIAC ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPendingState Invalid ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> snps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_different1 CSTATE_general_rule_3_0 MESI_State.distinct(543) i4x)
done
show goal766: "CSTATE SIAC ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPendingState Invalid ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> snps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) i213)
done
show goal767: "CSTATE SIAC ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPendingState Invalid ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> reqs1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) i208)
done
show goal768: "CSTATE SIAC ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPendingState Invalid ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> reqs2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 i942 nextGOPending_HostInvalidDirtyEvict nextGOPending_overlooked_reqresp_rule_8_0 reqs2_HostInvalidDirtyEvict)
done
show goal769: "HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextSnpRespIs RspIFwdM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) assms i672 nextHTDDataPending_general_rule_6_0)
done
show goal770: "HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextSnpRespIs RspIFwdM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) assms i673 nextHTDDataPending_general_rule_6_0)
done
show goal771: "HSTATE SB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 CSTATE_HostInvalidDirtyEvict_otherside_invariant3 assms i661)
done
show goal772: "nextReqIs CleanEvictNoData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> CSTATE SIAC ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) i209)
done
show goal773: "nextReqIs CleanEvictNoData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> CSTATE SIAC ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant2 i947 nextReqIs_HostInvalidDirtyEvict_otherside_1)
done
show goal774: "nextSnpRespIs RspIHitSE ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) HostInvalidDirtyEvict_nextSnpRespIs_sameside i948 nextDTHDataFrom_general_rule_5_0)
done
show goal775: "nextSnpRespIs RspIHitSE ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
apply  (insert assms)
apply (smt (verit) assms i540 nextDTHDataFrom_general_rule_5_0)
done
show goal776: "nextSnpRespIs RspIFwdM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> nextReqIs CleanEvictNoData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
apply  (insert assms)
apply (smt (verit) i209)
done
show goal777: "nextSnpRespIs RspIFwdM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> nextReqIs CleanEvictNoData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
apply  (insert assms)
apply (smt (verit) HostInvalidDirtyEvict_nextSnpRespIs_otherside i951 nextReqIs_HostInvalidDirtyEvict_otherside_1)
done
show goal778: "(CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])) "
by (smt (verit) goal599 i201)
show goal779: "(CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpData ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])) "
by (smt (verit) goal600 i201)
show goal780: "((CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPendingIs GO_WritePullDrop ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or>(CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> (CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) "
by (smt (verit) aux_r34_9)
show goal781: "((CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPendingIs GO_WritePullDrop ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or>(CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> (CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0)   "
by (smt (verit) aux_r34_8 goal199)
show goal782: "((CSTATE SIAC ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPendingIs GO ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPendingState Invalid ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> GTS ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or>(CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> (CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) "
by (smt (verit) aux_r34_8 goal199)
show goal783: "((CSTATE SIAC ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPendingIs GO ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPendingState Invalid ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> \<not> CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> GTS ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> HSTATE ModifiedM ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> CSTATE Modified ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> (CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or>(CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> (CSTATE IMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0)   "
by (smt (verit) aux_r34_8 goal199)
show goal784: "((CSTATE SIAC ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPendingIs GO ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPendingState Invalid ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> GTS ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> HSTATE MD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> dthdatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> []) "
by (smt (verit) aux_r34_8 goal289)
show goal785: "((CSTATE SIAC ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPendingIs GO ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPendingState Invalid ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> \<not> CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> GTS ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> HSTATE MD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> dthdatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<noteq> [])  "
by (smt (verit) aux_r34_8 goal289)
show goal786: "((CSTATE SIAC ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPendingIs GO ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPendingState Invalid ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> GTS ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> ((CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1)) "
apply simp
done
show goal787: "((CSTATE SIAC ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPendingIs GO ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPendingState Invalid ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> \<not> CSTATE IIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> GTS ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> HSTATE MA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> ((CSTATE IMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) \<and> nextHTDDataPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE IMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0)) "
by (smt (verit) CSTATE_HostInvalidDirtyEvict_otherside_invariant3 i4x)
show goal788: "(HSTATE SD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> snps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []) "
by (smt (verit) i213)
show goal789: "(HSTATE SD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> snps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []) "
by (metis HostInvalidDirtyEvict_HSTATE aux_r34_8 goal596)
show goal790: "(HSTATE SD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> reqresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []) "
by (metis goal555 i201)
show goal791: "(HSTATE SD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> reqresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []) "
by (smt (verit) goal556 i201)
show goal792: "(HSTATE ID ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> (\<not> CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> nextGOPendingIs GO_WritePullDrop ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) ) "
by (smt (verit) aux_r34_8 goal605 goal654)
show goal793: "(HSTATE ID ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> (\<not> CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> nextGOPendingIs GO_WritePullDrop ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0) ) "
by (smt (verit) aux_r34_8 goal596 i201)
show goal794: "(CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> HSTATE ID ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> (\<not> CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<or> nextGOPendingIs GO_WritePullDrop ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1)) "
by (metis goal603 i201)
show goal795: "(CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> nextGOPendingIs GO_WritePull ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<and> HSTATE ID ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> (\<not> CSTATE SIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<or> nextGOPendingIs GO_WritePullDrop ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0))  "
by (smt (verit) aux_r34_8 goal415)
show goal796: "(HSTATE SAD ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<and> \<not> CSTATE MIA ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1) "
by (metis CSTATE_HostInvalidDirtyEvict_otherside_invariant3 goal150 i207)
qed
qed
lemma helper: "f T \<Longrightarrow>
 (\<And>T txid.
  f T \<and> HSTATE InvalidM T \<and> nextReqIs DirtyEvict T 0 \<and> GTS T 1 \<and> CSTATE IIA T 0 \<Longrightarrow>
  f ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])) \<Longrightarrow>
 Lall
  (if HSTATE InvalidM T \<and> nextReqIs DirtyEvict T 0 \<and> GTS T ((0 + 1) mod 2) \<and> CSTATE IIA T 0
   then [clearBuffer ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid nextReqID T 0] [ 0 -=req ])] else [])
  f"
by simp
lemma HostInvalidDirtyEvict'_coherent: shows "
SWMR_state_machine T \<Longrightarrow> Lall (HostInvalidDirtyEvict' T 0) SWMR_state_machine
"
unfolding HostInvalidDirtyEvict'_def sendEvictResp_def
apply(insert HostInvalidDirtyEvict'_coherent_aux_simpler)
by (smt (verit) helper)
end