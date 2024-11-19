
theory  FixIMADGOFilled imports  BaseProof1.BasicInvariants  begin
sledgehammer_params[timeout=10, dont_minimize, "try0" = false]
lemma devcache2_buffer1_invariant: shows "devcache2 ( T \<lparr>buffer1 := Some m\<rparr> ) = devcache2 T"
by simp
lemma devcache2_sequals1_invariant: shows "devcache2 ( T [ 0 s= IMD] ) = devcache2 T"
by simp
lemma devcache2_consume_reqresps1_invariant: shows "devcache2 ( T [ 0 -=reqresp ] ) = devcache2 T"
apply simp
done
lemma devcache1_consume_reqresps1_invariant: shows "CLEntry.block_state  (devcache1 T) = CLEntry.block_state  (devcache1 ( T  [ 0 -=reqresp ] ))"
by simp
lemma devcache1_IMADGO_invariant_aux1: shows "CLEntry.block_state  (devcache1 T) = IMD \<Longrightarrow> 
  CLEntry.block_state (devcache1 ( T  [ 0 -=reqresp ] )) \<noteq> Modified"
by simp
lemma devcache1_IMADGO_invariant_aux: shows "CLEntry.block_state  (devcache1 T) = Shared \<Longrightarrow> 
  CLEntry.block_state (devcache1 ( T  [ 0 -=reqresp ] [ 0 -=devd ])) \<noteq> Modified"
by simp
lemma devcache1_IMADGO_invariant: shows "CLEntry.block_state  (devcache1 T) = Shared \<Longrightarrow> 
  CLEntry.block_state (devcache1 ( T [ 0 :=dd msg ] [ 0 -=reqresp ] [ 0 -=devd ])) \<noteq> Modified"
apply(subgoal_tac "CLEntry.block_state  (devcache1 (T  [ 0 :=dd msg ])) = Shared")
using devcache1_IMADGO_invariant_aux
apply blast
by simp
lemma IMADGO'_nextDTHDataPending: "nextDTHDataPending T i = nextDTHDataPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) i"
by simp
lemma IMADGO'_nextEvict: "nextEvict T i = nextEvict ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) i"
by simp
lemma IMADGO'_nextStore: "nextStore T i = nextStore ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) i"
by simp
lemma IMADGO'_not_nextGOPending: "length (reqresps1 T) \<le> 1 \<Longrightarrow> \<not> nextGOPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply(subgoal_tac " reqresps1 (T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD]) = reqresps1 T")
apply(subgoal_tac " length (reqresps1 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD])) \<le> 1")
apply(case_tac "reqresps1  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD])")
by simp+
lemma IMADGO'_nextGOPending1: "nextGOPending  T 1 = nextGOPending  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
by simp
lemma IMADGO'_nextGOPendingIs: "nextGOPendingIs X T 1 = nextGOPendingIs X ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
by simp
lemma IMADGO'_nextHTDDataPending: "nextHTDDataPending T i = nextHTDDataPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) i"
apply  simp
done
lemma IMADGO'_HSTATE: "HSTATE X T  = HSTATE X ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) "
apply  simp
done
lemma IMADGO'_CSTATE_otherside: "CSTATE X T 1 = CSTATE X ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  simp
done
lemma IMADGO'_CSTATE_sameside: "CSTATE IMD ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
by simp
lemma IMADGO'_nextSnoopIs: "nextSnoopIs X T i = nextSnoopIs X ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) i"
apply  simp
done
lemma IMADGO'_nextReqIs: "nextReqIs X T i = nextReqIs X ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) i"
apply  simp
done
lemma IMADGO'_nextSnpRespIs: "nextSnpRespIs X T i = nextSnpRespIs X ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) i"
apply  simp
done
lemma IMADGO'_nextReqIs_invariant1: shows "nextReqIs x T i = nextReqIs x ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) i"
apply(case_tac i)
apply simp
apply simp
done
lemma IMADGO'_nextReqIs_invariant_DirtyEvict: shows "nextReqIs DirtyEvict T i = nextReqIs DirtyEvict ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) i"
apply(case_tac i)
apply simp+
done
lemma IMADGO'_nextReqIs_invariant_not_RdOwn: shows "X \<noteq> RdOwn \<Longrightarrow> nextReqIs X T i = nextReqIs X ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) i"
apply(case_tac i)
apply simp+
done
lemma reqs2_IMADGO: shows "reqs2 T = reqs2 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
by simp
lemma nextStore_IMADGO: shows "nextLoad ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 = nextLoad T 0"
by simp
lemma nextLoad2_IMADGO: shows "nextLoad ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 = nextLoad T 1"
by simp
lemma nextLoad_DeviceIMADGO: "nextLoad (  T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ] ) i = nextLoad T i"
apply(case_tac i)
apply simp+
done
lemma nextGOPending_DeviceIMADGO: "nextGOPending (  T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ] ) 1 = nextGOPending T 1"
apply simp+
done
lemma IMADGO'_coherent_aux_simpler:  assumes "SWMR_state_machine T \<and>  CSTATE IMAD T 0 \<and> nextGOPending T 0" shows
  "SWMR_state_machine ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
proof -
have i0: "SWMR T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i1x: "CSTATE IMAD T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i2x: "nextGOPending T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
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
have i814: "(CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<and> HSTATE SB T \<longrightarrow> \<not> CSTATE IIA T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
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
have i922: "(HSTATE ModifiedM T \<longrightarrow> snps1 T = [] \<and> snps2 T = [])  " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
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
have i201: "nextSnoopPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 = nextSnoopPending T 1" by simp
have "\<not> nextGOPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [0 -=reqresp ]) 0"
using IMADGO'_not_nextGOPending i85
by blast
have aux_r77: "HSTATE MAD T \<or> HSTATE MD T \<or> HSTATE SAD T \<or> HSTATE ModifiedM T"
using i1x i2x i338
by blast
have aux_r79: "nextStore T 0"
using i1x i339
by blast
have aux2_r79: "nextStore ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
using IMADGO'_nextStore aux_r79
by blast
have aux2_r84: "snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and>
 snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and>
 reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply simp
by (metis One_nat_def Suc_length_conv assms i341 i85 le_Suc_eq le_zero_eq length_0_conv list.sel(2) list.sel(3) tl_def)
have aux116: " \<not> nextSnpRespIs RspIFwdM T 0"
using i2x i343
by force
have aux1162: " \<not> nextSnpRespIs RspIFwdM ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
using aux116
by simp
show ?thesis
unfolding SWMR_state_machine_def
proof (intro conjI)
show goal1: "SWMR ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (metis CSTATE_assign_rule_4 CSTATE_various_forms1 IMADGO'_CSTATE_sameside MESI_State.distinct(109) MESI_State.distinct(19) SharedSnpInv'_CSTATE_invariant5 \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> devcache1_consume_reqresps1_invariant)
done
show goal2: "C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(19) MESI_State.distinct(191) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal3: "H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
by (metis CSTATE_assign_rule_4 CSTATE_different1 IMADGO'_CSTATE_otherside IMADGO'_HSTATE MESI_State.distinct(19) i23)
show goal4: "H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
by (metis IMADGO'_CSTATE_otherside IMADGO'_HSTATE IMADGO'_nextDTHDataPending i1x i2x i435 i898 nextDTHDataPending_def nextDTHDataPending_general_rule_2_0)
show goal5: "C_msg_P_oppo ISAD nextGOPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(19) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal6: "H_msg_P_same SharedM (nextReqIs RdShared) (\<lambda>T i. \<not> CSTATE Modified T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i656 nextGOPending_yes_reqresp_rule_6_1)
done
show goal7: "H_msg_P_oppo SharedM (nextReqIs RdShared) (\<lambda>T i. \<not> CSTATE Modified T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i656 nextGOPending_yes_reqresp_rule_6_1)
done
show goal8: "H_msg_P_same ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> CSTATE Modified T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant C_not_C_msg_def IMADGO'_CSTATE_otherside IMADGO'_HSTATE MESI_State.distinct(19) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i337 nextGOPending_yes_reqresp_rule_6_1)
done
show goal9: "H_msg_P_oppo ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> nextDTHDataPending T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (metis C_msg_not_def H_msg_P_oppo_def IMADGO'_HSTATE IMADGO'_nextDTHDataPending IMADGO'_nextReqIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i13 i25 nextGOPending_yes_reqresp_rule_6_1)
done
show goal10: "H_msg_P_oppo ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> nextSnpRespIs RspIFwdM T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (metis C_msg_not_def IMADGO'_HSTATE IMADGO'_nextReqIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms aux1162 i25 nextGOPending_yes_reqresp_rule_6_1)
done
show goal11: "H_msg_P_same ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> nextSnpRespIs RspIFwdM T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (metis H_msg_P_same_def IMADGO'_HSTATE IMADGO'_nextReqIs IMADGO'_nextSnpRespIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux1162 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i14 i15 nextGOPending_yes_reqresp_rule_6_1)
done
show goal12: "C_H_state IMAD (nextReqIs RdOwn) Modified SD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(19) MESI_State.distinct(331) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal13: "C_H_state IMAD (nextReqIs RdOwn) Modified SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant IMADGO'_HSTATE MESI_State.distinct(19) MESI_State.distinct(331) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal14: "C_H_state IMAD (nextReqIs RdOwn) Modified SA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(19) MESI_State.distinct(331) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal15: "C_H_state Invalid nextStore Modified SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant IMADGO'_HSTATE MESI_State.distinct(151) MESI_State.distinct(19) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal16: "C_H_state Invalid nextStore Modified SA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(151) MESI_State.distinct(19) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal17: "C_H_state Invalid nextStore Modified SD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(151) MESI_State.distinct(19) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal18: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i656 nextGOPending_yes_reqresp_rule_6_1)
done
show goal19: "HSTATE SD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant C_not_C_msg_def IMADGO'_CSTATE_otherside IMADGO'_HSTATE MESI_State.distinct(19) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i337 nextGOPending_yes_reqresp_rule_6_1)
done
show goal20: "HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(19) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i24 nextGOPending_yes_reqresp_rule_6_1)
done
show goal21: "C_msg_not RdShared IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (metis C_msg_not_def IMADGO'_CSTATE_otherside IMADGO'_nextReqIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i25 nextGOPending_yes_reqresp_rule_6_1 nextReqIs_general_rule_6_0)
done
show goal22: "C_msg_not RdShared Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant C_msg_not_def IMADGO'_CSTATE_otherside IMADGO'_nextReqIs MESI_State.distinct(151) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i25 i26 nextGOPending_yes_reqresp_rule_6_1)
done
show goal23: "H_msg_P_same ModifiedM (nextReqIs DirtyEvict) (\<lambda>T i. CSTATE MIA T i \<or> CSTATE IIA T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
proof (intro conjI)
show goal1: "HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
 if "SWMR_state_machine T \<and> CSTATE IMAD T 0 \<and> nextGOPending T 0"
using that
apply  (-)
apply (metis CSTATE_def IMADGO'_nextReqIs_invariant_DirtyEvict MESI_State.distinct(339) MESI_State.distinct(343) MESI_State.distinct(355) i1x i453)
done
show goal2: "HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
 if "SWMR_state_machine T \<and> CSTATE IMAD T 0 \<and> nextGOPending T 0"
using that
apply  (-)
apply (metis CSTATE_otherside_rule_6 HSTATE_XYADGO1 H_msg_P_same_def assms i27 i742 nextReqIs_general_rule_6_0)
done
qed
show goal24: "C_msg_P_host MIA (nextGOPendingIs GO_WritePull) (\<lambda>T. \<not> HSTATE ModifiedM T) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_HSTATE IMADGO'_nextGOPendingIs MESI_State.distinct(397) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i313 nextGOPendingIs_XYADGO_agnostic1)
done
show goal25: "C_msg_P_same MIA (nextGOPendingIs GO_WritePull) nextEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_nextEvict MESI_State.distinct(397) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i742 nextGOPendingIs_XYADGO_agnostic1)
done
show goal26: "C_msg_P_host MIA (nextGOPendingIs GO_WritePull) (HSTATE ID) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant IMADGO'_CSTATE_otherside IMADGO'_HSTATE MESI_State.distinct(397) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i742 nextGOPendingIs_XYADGO_agnostic1)
done
show goal27: "C_state_not MIA RdShared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (metis C_msg_not_def IMADGO'_CSTATE_otherside IMADGO'_nextReqIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i25 i742 nextGOPending_yes_reqresp_rule_6_1)
done
show goal28: "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) nextEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (metis CSTATE_assign_rule_4 CSTATE_disj1 CSTATE_otherside_rule_4_0 C_msg_P_same_def IMADGO'_nextEvict MESI_State.distinct(401) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux2_r84 i32 nextGOPendingIs_XYADGO_agnostic1 reqresps_empty_noGOPendingIs1)
done
show goal29: "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextReqIs RdShared T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (metis CSTATE_inequality_invariant C_msg_state_def IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_nextReqIs MESI_State.distinct(277) MESI_State.distinct(401) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i47 nextGOPendingIs_XYADGO_agnostic1)
done
show goal30: "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextDTHDataPending T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (metis C_msg_P_same_def IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_nextDTHDataPending IMADGO'_nextGOPendingIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux2_r84 i35 nextGOPendingIs_XYADGO_agnostic1 reqresps_empty_noGOPendingIs1)
done
show goal31: "H_C_state_msg_same ModifiedM Modified (\<lambda>T i. \<not> nextReqIs RdShared T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
by (smt (verit) H_msg_P_same_def goal8)
show goal32: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) nextEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
by (metis CSTATE_assign_rule_4 CSTATE_different1 C_msg_P_same_def IMADGO'_CSTATE_otherside IMADGO'_nextEvict IMADGO'_nextGOPendingIs MESI_State.simps(402) i37)
show goal33: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextReqIs RdShared T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (metis CSTATE_inequality_invariant C_msg_not_def C_msg_state_def IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_nextReqIs MESI_State.distinct(277) MESI_State.distinct(401) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i25 i47 nextGOPendingIs_XYADGO_agnostic1)
done
show goal34: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextDTHDataPending T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant C_msg_P_same_def IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_nextDTHDataPending IMADGO'_nextGOPendingIs MESI_State.distinct(401) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i321 i40 nextGOPendingIs_XYADGO_agnostic1)
done
show goal35: "H_C_state_msg_oppo ModifiedM IIA (\<lambda>T i. \<not> nextReqIs RdShared T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (metis (lifting) CSTATE_inequality_invariant H_C_state_msg_oppo_def IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_HSTATE IMADGO'_nextReqIs MESI_State.distinct(401) ext i41)
done
show goal36: "C_msg_P_host Shared (nextSnoopIs SnpInv) (HSTATE MA) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(109) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i385 i465 nextGOPending_yes_reqresp_rule_6_1)
done
show goal37: "C_msg_state RdShared ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply simp
by (smt (verit) CSTATE_different1 CSTATE_various_forms3 C_msg_state_def MESI_State.distinct(261) i1x i47 nextReqIs_various_forms2 nextReqIs_various_forms3)
show goal38: "C_not_C_msg Modified ISAD nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(19) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal39: "C_msg_P_same Invalid nextStore (\<lambda>T i. \<not> nextHTDDataPending T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_nextHTDDataPending IMADGO'_nextStore MESI_State.distinct(151) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i465 i593 nextGOPending_yes_reqresp_rule_6_1)
done
show goal40: "C_msg_P_same Invalid nextStore (\<lambda>T i. \<not> nextSnoopIs SnpInv T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_nextSnoopIs IMADGO'_nextStore MESI_State.distinct(151) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i593 nextGOPending_yes_reqresp_rule_6_1)
done
show goal41: "C_msg_P_same ISAD nextGOPending (\<lambda>T i. \<not> nextReqIs RdShared T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (metis C_msg_P_same_def IMADGO'_CSTATE_otherside IMADGO'_nextReqIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i52 nextGOPending_DeviceIMADGO nextGOPending_yes_reqresp_rule_6_1)
done
show goal42: "snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<longrightarrow> reqs1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r84)
done
show goal43: "snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<longrightarrow> reqs2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (cases "dthdatas1 T")
apply  (auto)
apply (smt (verit) i56)
apply (smt (verit) i56)
apply (smt (verit) i56)
apply (smt (verit) butlast.simps(1) i56 list.distinct(1))
done
show goal44: "length (reqs1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])) \<le> 1"
apply  (cases "dthdatas1 T")
apply  (auto)
apply (smt (verit) One_nat_def i57)
apply (smt (verit) One_nat_def i57)
done
show goal45: "length (reqs2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])) \<le> 1"
apply  (insert assms)
apply (metis \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i58 nextGOPending_yes_reqresp_rule_6_1 reqs2_IMADGO)
done
show goal46: "length (snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])) \<le> 1"
apply  (insert assms)
apply (smt (verit) assms aux2_r84 i341 i435 i465 i500 i883 i909)
done
show goal47: "length (snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])) \<le> 1"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_sameside \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i61 nextGOPending_yes_reqresp_rule_6_1 snps1_general_rule_6_0)
done
show goal48: "C_msg_P_same Shared (nextSnoopIs SnpInv) (\<lambda>T i. \<not> nextHTDDataPending T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (metis CSTATE_inequality_invariant C_msg_P_same_def IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_nextHTDDataPending IMADGO'_nextSnoopIs MESI_State.distinct(107) MESI_State.distinct(109) MESI_State.distinct(127) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i385 i465 i59 i600 nextGOPending_yes_reqresp_rule_6_1)
done
show goal49: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextSnoopPending T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (metis CSTATE_inequality_invariant C_msg_P_same_def IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_nextGOPendingIs MESI_State.distinct(401) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i201 i517 i611old nextGOPendingIs_XYADGO_agnostic1)
done
show goal50: "C_msg_P_oppo Invalid nextStore (\<lambda>T i. \<not> nextSnoopPending T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply simp
by (metis CSTATE_various_forms4 i614old)
show goal51: "CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(151) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> htddatas1_general_rule_5_0)
done
show goal52: "CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (cases "dthdatas1 T")
apply  (auto)
apply (smt (verit) CSTATE_various_forms4 i614old)
apply (smt (verit) CSTATE_various_forms4 i614old)
apply (smt (verit) CSTATE_various_forms6 i382)
apply (smt (verit) CSTATE_various_forms4 i614old)
apply (smt (verit) i1x i2x i435 list.distinct(1))
apply (smt (verit) i1x i2x i435 i99 list.discI)
apply (smt (verit) i1x i2x i435 i95 list.discI)
apply (smt (verit) i101 i1x i2x i435 list.distinct(1))
done
show goal53: "CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(109) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> htddatas1_general_rule_5_0)
done
show goal54: "CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms empty_no_snoop_variant2 i341 i465 nextGOPending_yes_reqresp_rule_6_1)
done
show goal55: "CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(401) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> htddatas1_general_rule_5_0)
done
show goal56: "CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (cases "dthdatas1 T")
apply  (auto)
apply (smt (verit) CSTATE_various_forms4 i618old)
apply (smt (verit) CSTATE_various_forms4 i618old)
apply (smt (verit) CSTATE_various_forms5 i618old)
apply (smt (verit) CSTATE_various_forms5 i618old)
apply (smt (verit) i1x i2x i435 i99 list.discI)
apply (smt (verit) i101 i1x i2x i435 i580 list.distinct(1))
done
show goal57: "CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> reqs1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(151) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal58: "CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> reqs2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i69 nextGOPending_yes_reqresp_rule_6_1 reqs2_IMADGO)
done
show goal59: "CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> reqs1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(109) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal60: "CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> reqs2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms empty_no_snoop2 i341 i465 nextGOPending_yes_reqresp_rule_6_1 reqs2_IMADGO)
done
show goal61: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(19) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal62: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(19) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal63: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant HSTATE_XYADGO1 IMADGO'_HSTATE MESI_State.distinct(191) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal64: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis CSTATE_otherside_rule_6 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i75 nextGOPending_yes_reqresp_rule_6_1)
done
show goal65: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> nextLoad ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(191) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextLoad_general_rule_4_0 nextStore_IMADGO)
done
show goal66: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> nextLoad ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i752old nextGOPending_yes_reqresp_rule_6_1 nextLoad2_IMADGO nextLoad_DeviceIMADGO)
done
show goal67: "C_msg_P_host ISD (nextSnoopIs SnpInv) (HSTATE MA) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant CSTATE_otherside_rule_6 MESI_State.distinct(191) aux2_r84 empty_no_snoop2 i1x i2x i465 snps2_general_rule_6_0)
done
show goal68: "length (htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])) \<le> 1"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_sameside \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> htddatas1_general_rule_5_0 i77 nextGOPending_yes_reqresp_rule_6_1)
done
show goal69: "length (htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])) \<le> 1"
apply  (insert assms)
apply (metis HTDDataPending_htddatas_invariant2 IMADGO'_CSTATE_sameside IMADGO'_nextHTDDataPending \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms bot_nat_0.extremum empty_no_snoop2 i341 i435 i465 i77 i884 le_antisym list.size(3) nat_le_linear nextGOPending_DeviceIMADGO nextGOPending_yes_reqresp_rule_6_1 no2Datas_def)
done
show goal70: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r84)
done
show goal71: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms empty_no_snoop2 i341 i465 nextGOPending_yes_reqresp_rule_6_1)
done
show goal72: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> reqs1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(191) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal73: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> reqs2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms empty_no_snoop2 i341 i465 nextGOPending_yes_reqresp_rule_6_1 reqs2_IMADGO)
done
show goal74: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> reqs1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(331) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal75: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> reqs2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis IMADGO'_nextHTDDataPending \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms empty_no_snoop2 i341 i465 nextGOPending_yes_reqresp_rule_6_1 reqs2_IMADGO)
done
show goal76: "length (reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])) \<le> 1"
apply  (insert assms)
apply (smt (verit) assms aux2_r84 i435 i883)
done
show goal77: "length (reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])) \<le> 1"
apply  (cases "dthdatas1 T")
apply  (auto)
apply (smt (verit) One_nat_def i86)
apply (smt (verit) One_nat_def i86)
done
show goal78: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r84 reqresps_empty_noGOPendingIs1)
done
show goal79: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r84)
done
show goal80: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r84 reqresps_empty_noGOPendingIs1)
done
show goal81: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i742 nextGOPendingIs_XYADGO_agnostic1)
done
show goal82: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant IMADGO'_nextReqIs MESI_State.distinct(265) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextReqIs_general_rule_6_0)
done
show goal83: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_nextReqIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i92 nextGOPending_yes_reqresp_rule_6_1)
done
show goal84: "C_msg_P_same MIA (nextReqIs DirtyEvict) nextEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant IMADGO'_CSTATE_otherside IMADGO'_nextEvict MESI_State.distinct(397) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i742 nextGOPending_yes_reqresp_rule_6_1)
done
show goal85: "reqs1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<longrightarrow> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r84)
done
show goal86: "reqs2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<longrightarrow> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (cases "dthdatas1 T")
apply  (auto)
apply (smt (verit) i95)
apply (smt (verit) i95)
done
show goal87: "reqs1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<longrightarrow> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r84)
done
show goal88: "reqs2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<longrightarrow> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 SARspSFwdM_invariant1 \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i99 nextSnpRespIs_general_rule_6_0 nextSnpRespIs_invariant1 reqs2_IMADGO)
done
show goal89: "reqs1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<longrightarrow> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (cases "dthdatas1 T")
apply  (auto)
apply (smt (verit) i100)
apply (smt (verit) i100)
done
show goal90: "reqs2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<longrightarrow> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 HTDDataPending_htddatas_invariant2 IMADGO'_nextHTDDataPending \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms empty_no_snoop2 i341 i465 reqs2_IMADGO)
done
show goal91: "HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> (CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis C_not_C_msg_def IMADGO'_CSTATE_otherside IMADGO'_HSTATE IMADGO'_nextHTDDataPending IMADGO'_nextReqIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i337 i415 i742 i909 nextGOPending_DeviceIMADGO nextGOPending_yes_reqresp_rule_6_1)
done
show goal92: "HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> (CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_HSTATE IMADGO'_nextHTDDataPending IMADGO'_nextReqIs MESI_State.distinct(15) MESI_State.distinct(329) MESI_State.distinct(339) MESI_State.distinct(349) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i416 nextGOPending_yes_reqresp_rule_6_1)
done
show goal93: "HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> (CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply simp
by (metis assms i1x i435)
show goal94: "HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> (CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant HOST_State.distinct(165) HOST_State.distinct(265) HOST_State.distinct(33) HSTATE_invariant3 IMADGO'_CSTATE_sameside IMADGO'_HSTATE IMADGO'_nextHTDDataPending MESI_State.distinct(329) MESI_State.distinct(349) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms aux_r77 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i24 i782 i801 nextDTHDataFrom2_XYADGO1 nextDTHDataFrom_IXADGO_invariant1)
done
show goal95: "HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> (CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(401) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal96: "HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> (CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant HOST_State.distinct(151) HOST_State.distinct(165) HOST_State.distinct(19) HOST_State.distinct(251) HOST_State.distinct(265) HOST_State.distinct(271) HOST_State.distinct(33) HSTATE_invariant3 IMADGO'_CSTATE_otherside IMADGO'_HSTATE IMAD_HTDData_overall_def MESI_State.distinct(163) MESI_State.distinct(329) MESI_State.distinct(343) MESI_State.distinct(349) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms aux_r77 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i182 i24 i782 i878 nextGOPending_yes_reqresp_rule_6_1)
done
show goal97: "reqs1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<longrightarrow> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r84)
done
show goal98: "reqs2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<longrightarrow> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (cases "dthdatas1 T")
apply  (auto)
apply (smt (verit) i95)
apply (smt (verit) i95)
done
show goal99: "HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_otherside IMADGO'_HSTATE MESI_State.distinct(261) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i106 nextGOPending_yes_reqresp_rule_6_1)
done
show goal100: "HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(109) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i107 nextGOPending_yes_reqresp_rule_6_1)
done
show goal101: "HSTATE SD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<longrightarrow> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms dthdatas1_general_rule_3_0 i435)
done
show goal102: "HSTATE SD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<longrightarrow> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant HOST_State.distinct(175) HOST_State.distinct(179) HOST_State.distinct(9) HSTATE_invariant3 IMADGO'_HSTATE IMADGO'_nextDTHDataPending MESI_State.distinct(261) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms aux_r77 dthdatas1_general_rule_3_0 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) htddatas1_general_rule_5_0 i106 i109 nextDTHDataPending_def)
done
show goal103: "length (dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])) \<le> 1"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_sameside \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms bot_nat_0.extremum dthdatas1_general_rule_3_0 i435 list.size(3) nextGOPending_yes_reqresp_rule_6_1)
done
show goal104: "length (dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])) \<le> 1"
apply  (cases "dthdatas1 T")
apply  (auto)
apply (smt (verit) One_nat_def i884)
apply (smt (verit) One_nat_def i884)
done
show goal105: "HSTATE SD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis HOST_State.distinct(141) HOST_State.distinct(175) HOST_State.distinct(179) HOST_State.distinct(9) HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 nextDTHDataFrom2_XYADGO1)
done
show goal106: "HSTATE SD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis HOST_State.distinct(141) HOST_State.distinct(175) HOST_State.distinct(179) HOST_State.distinct(9) HSTATE_XYADGO1 HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 nextDTHDataFrom2_XYADGO1)
done
show goal107: "HSTATE SA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> (nextSnpRespIs RspIFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> nextSnpRespIs RspSFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<longrightarrow> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_otherside_rule_6 IMADGO'_HSTATE IMADGO'_nextSnpRespIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux1162 i114 nextGOPending_yes_reqresp_rule_6_1)
done
show goal108: "HSTATE SA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> (nextSnpRespIs RspIFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> nextSnpRespIs RspSFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<longrightarrow> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_HSTATE IMADGO'_nextSnpRespIs MESI_State.distinct(225) MESI_State.distinct(261) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i115 nextGOPending_yes_reqresp_rule_6_1)
done
show goal109: "nextSnpRespIs RspIFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> nextSnpRespIs RspIHitSE ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis assms aux1162 i343 nextSnpRespIs_general_rule_6_0 nextSnpRespIs_property1 reqresps_empty_noGOPending1)
done
show goal110: "nextSnpRespIs RspIFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> nextSnpRespIs RspIHitSE ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_otherside_rule_6 IMADGO'_nextSnpRespIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i457 nextGOPending_yes_reqresp_rule_6_1)
done
show goal111: "nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_nextReqIs MESI_State.distinct(339) MESI_State.distinct(343) MESI_State.distinct(355) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i453 nextReqIs_general_rule_6_0)
done
show goal112: "nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_nextReqIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i454 i742 nextGOPending_yes_reqresp_rule_6_1 nextReqIs_general_rule_6_0)
done
show goal113: "snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<longrightarrow> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 IMADGO'_CSTATE_sameside SARspSFwdM_invariant1 \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i2x i343 nextSnpRespIs_general_rule_6_0 reqresps_empty_noGOPending1)
done
show goal114: "snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<longrightarrow> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r84)
done
show goal115: "length (snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])) \<le> 1"
apply  (cases "dthdatas1 T")
apply  (auto)
apply (smt (verit) One_nat_def i120)
apply (smt (verit) One_nat_def i120)
done
show goal116: "length (snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])) \<le> 1"
apply  (insert assms)
apply (smt (verit) assms aux2_r84 i121 i341 i435 i865 i909)
done
show goal117: "HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> (nextSnpRespIs RspIFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> nextSnpRespIs RspSFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<longrightarrow> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_HSTATE IMADGO'_nextSnpRespIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux1162 i437 nextGOPending_yes_reqresp_rule_6_1)
done
show goal118: "HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> (nextSnpRespIs RspIFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> nextSnpRespIs RspSFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<longrightarrow> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_HSTATE IMADGO'_nextSnpRespIs MESI_State.distinct(261) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i438 nextGOPending_yes_reqresp_rule_6_1)
done
show goal119: "HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextSnpRespIs RspIFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux1162)
done
show goal120: "HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextSnpRespIs RspIFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r84 nextSnpRespIs_property2)
done
show goal121: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis CSTATE_otherside_rule_6 HOST_State.distinct(149) HOST_State.distinct(17) HOST_State.distinct(249) HOST_State.distinct(271) HSTATE_invariant4 aux_r77 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i1x i2x i909)
done
show goal122: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r84)
done
show goal123: "HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<longrightarrow> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis HSTATE_XYADGO1 IMADGO'_HSTATE IMADGO'_nextHTDDataPending \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> empty_no_snoop2 i1x i2x i341 i465 nextHTDDataPending_various_forms2)
done
show goal124: "HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<longrightarrow> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r84)
done
show goal125: "HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> reqs1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<longrightarrow> dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> []"
apply  (cases "dthdatas1 T")
apply  (auto)
apply  (smt (verit) HSTATE_def i128)
done
show goal126: "HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> reqs2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<longrightarrow> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> []"
apply  (insert assms)
apply (metis HSTATE_XYADGO1 \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i129 i892 nextDTHDataFrom_IXADGO_invariant1 nextDTHDataFrom_def reqresps_empty_noGOPending1 reqs2_IMADGO)
done
show goal127: "HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<longrightarrow> CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms dthdatas1_general_rule_3_0 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i609)
done
show goal128: "HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<longrightarrow> CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i609 nextGOPending_yes_reqresp_rule_6_1)
done
show goal129: "HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms dthdatas1_general_rule_3_0 i435 nextGOPending_yes_reqresp_rule_6_1)
done
show goal130: "HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis HSTATE_XYADGO1 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i609)
done
show goal131: "dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<and> HSTATE SD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r84)
done
show goal132: "dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<and> HSTATE SD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis HOST_State.distinct(141) HOST_State.distinct(173) HOST_State.distinct(175) HOST_State.distinct(179) HOST_State.distinct(9) HSTATE_general_rule_4_0 HSTATE_invariant3 aux_r77)
done
show goal133: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> nextLoad ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(191) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextLoad_general_rule_4_0 nextStore_IMADGO)
done
show goal134: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> nextLoad ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i752old nextGOPending_yes_reqresp_rule_6_1 nextLoad2_IMADGO nextLoad_DeviceIMADGO)
done
show goal135: "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextSnoopPending T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) aux2_r84 nextSnoopPending_def reqresps_empty_noGOPendingIs1)
done
show goal136: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> HSTATE SD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal137: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> HSTATE SD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i144 i656 nextGOPending_yes_reqresp_rule_6_1)
done
show goal138: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> nextLoad ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant MESI_State.distinct(265) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextLoad_general_rule_4_0 nextStore_IMADGO)
done
show goal139: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> nextLoad ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i146 nextGOPending_yes_reqresp_rule_6_1 nextLoad2_IMADGO nextLoad_general_rule_4_0)
done
show goal140: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(265) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextSnoopIs_general_rule_6_0)
done
show goal141: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_HSTATE IMADGO'_nextSnoopIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i148 nextGOPending_yes_reqresp_rule_6_1)
done
show goal142: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal143: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms empty_no_snoop_variant2 i341 i465 nextGOPending_DeviceIMADGO nextGOPending_yes_reqresp_rule_6_1)
done
show goal144: "(CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> (CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(151) MESI_State.distinct(299) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal145: "(CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> (CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_HSTATE IMADGO'_nextHTDDataPending MESI_State.distinct(15) MESI_State.distinct(329) MESI_State.distinct(331) MESI_State.distinct(339) MESI_State.distinct(349) MESI_State.distinct(351) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i418 nextGOPending_yes_reqresp_rule_6_1)
done
show goal146: "(CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> []"
apply  (insert assms)
apply (metis CSTATE_disj1 IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(151) MESI_State.distinct(299) dthdatas1_general_rule_3_0)
done
show goal147: "(CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> []"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i154 i760 nextDTHDataFrom_IXADGO_invariant1_neg nextDTHDataFrom_def nextGOPending_yes_reqresp_rule_6_1 reqresps_empty_noGOPending1)
done
show goal148: "HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis HSTATE_XYADGO1 SARspSFwdM_invariant1 \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux2_r84 i159 nextSnpRespIs_general_rule_6_0 nextSnpRespIs_invariant1)
done
show goal149: "HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_otherside IMADGO'_HSTATE MESI_State.distinct(261) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i106 nextDTHDataFrom2_XYADGO1)
done
show goal150: "HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_HSTATE MESI_State.distinct(261) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i161 nextDTHDataFrom2_XYADGO1 nextDTHDataFrom_IXADGO_invariant1)
done
show goal151: "HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis HTDDataPending_htddatas_invariant2 IMADGO'_HSTATE IMADGO'_nextHTDDataPending \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i164 nextDTHDataFrom1_XYADGO1 nextDTHDataFrom_IXADGO_invariant1 nextHTDDataPending_various_forms2)
done
show goal152: "HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) htddatas1_general_rule_5_0 i165 nextDTHDataFrom2_XYADGO1 nextDTHDataFrom_IXADGO_invariant1)
done
show goal153: "HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> reqs2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i166 nextDTHDataFrom1_XYADGO1 nextDTHDataFrom_IXADGO_invariant1 reqs2_IMADGO)
done
show goal154: "HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> reqs1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_HSTATE MESI_State.distinct(261) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i161 nextDTHDataFrom2_XYADGO1 nextDTHDataFrom_IXADGO_invariant1)
done
show goal155: "HSTATE SD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> reqs2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis HOST_State.distinct(141) HOST_State.distinct(175) HOST_State.distinct(179) HOST_State.distinct(9) HSTATE_invariant3 \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) nextDTHDataFrom1_XYADGO1 reqs2_IMADGO)
done
show goal156: "HSTATE SD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> reqs1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis HOST_State.distinct(141) HOST_State.distinct(175) HOST_State.distinct(179) HOST_State.distinct(9) HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) nextDTHDataFrom2_XYADGO1)
done
show goal157: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i656 nextReqIs_general_rule_6_0)
done
show goal158: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i656 nextGOPending_yes_reqresp_rule_6_1)
done
show goal159: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextReqIs RdShared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i656 nextReqIs_general_rule_6_0)
done
show goal160: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextReqIs RdShared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i656 nextGOPending_yes_reqresp_rule_6_1)
done
show goal161: "CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> (CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(401) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal162: "CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> (CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_HSTATE IMADGO'_nextHTDDataPending MESI_State.distinct(15) MESI_State.distinct(329) MESI_State.distinct(331) MESI_State.distinct(339) MESI_State.distinct(349) MESI_State.distinct(351) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i420 nextGOPending_yes_reqresp_rule_6_1)
done
show goal163: "CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> reqs2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<or> nextReqIs CleanEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i656 nextGOPending_yes_reqresp_rule_6_1 reqs2_IMADGO)
done
show goal164: "CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> reqs1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<or> nextReqIs CleanEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i656 nextGOPending_yes_reqresp_rule_6_1)
done
show goal165: "CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (smt (verit) aux2_r84 reqresps_empty_noGOPendingIs1)
done
show goal166: "CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_HSTATE IMADGO'_nextGOPendingIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i179 nextGOPendingIs_XYADGO_agnostic1)
done
show goal167: "CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPendingIs GO_WritePullDrop ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (smt (verit) aux2_r84 reqresps_empty_noGOPendingIs1)
done
show goal168: "CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPendingIs GO_WritePullDrop ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_HSTATE IMADGO'_nextGOPendingIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i181 i609 i656 i666 nextGOPendingIs_XYADGO_agnostic1)
done
show goal169: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant HSTATE_XYADGO1 IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(331) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal170: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_HSTATE IMADGO'_nextHTDDataPending \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i183 nextGOPending_yes_reqresp_rule_6_1)
done
show goal171: "CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(401) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal172: "CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i656 nextGOPending_yes_reqresp_rule_6_1)
done
show goal173: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms dthdatas1_general_rule_3_0 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i656)
done
show goal174: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(397) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal175: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(397) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal176: "HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply simp
by (metis HSTATE_def i189)
show goal177: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis HOST_State.distinct(149) HOST_State.distinct(17) HOST_State.distinct(249) HOST_State.distinct(271) HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 dthdatas1_general_rule_3_0 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24))
done
show goal178: "nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_sameside IMADGO'_nextHTDDataPending \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i190 nextDTHDataFrom1_XYADGO1 nextDTHDataFrom_IXADGO_invariant1)
done
show goal179: "nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_sameside IMADGO'_nextHTDDataPending \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i191 nextDTHDataFrom2_XYADGO1 nextDTHDataFrom_IXADGO_invariant1)
done
show goal180: "nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_sameside \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i192 nextDTHDataFrom2_XYADGO1 nextDTHDataFrom_IXADGO_invariant1)
done
show goal181: "nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_sameside \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i192 nextDTHDataFrom2_XYADGO1 nextDTHDataFrom_IXADGO_invariant1)
done
show goal182: "HSTATE SA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis HOST_State.distinct(11) HOST_State.distinct(143) HOST_State.distinct(199) HOST_State.distinct(201) HOST_State.distinct(205) HOST_State.distinct(79) HSTATE_XYADGO1 HSTATE_invariant3 aux_r77)
done
show goal183: "HSTATE SD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> \<not> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant IMADGO'_HSTATE MESI_State.distinct(401) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal184: "HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> (\<not> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> nextSnpRespIs RspIFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> (\<not> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> nextSnpRespIs RspIFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1)"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(261) MESI_State.distinct(277) MESI_State.distinct(401) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i106 nextGOPending_yes_reqresp_rule_6_1)
done
show goal185: "CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(401) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextDTHDataFrom2_XYADGO1)
done
show goal186: "CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_nextGOPendingIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i198 nextDTHDataFrom2_XYADGO1 nextDTHDataFrom_IXADGO_invariant1)
done
show goal187: "CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(401) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal188: "CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(401) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal189: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(397) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextDTHDataFrom2_XYADGO1)
done
show goal190: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i742 nextDTHDataFrom2_XYADGO1)
done
show goal191: "snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<longrightarrow> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r84)
done
show goal192: "snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<longrightarrow> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r84)
done
show goal193: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextReqIs RdShared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i656 nextGOPendingIs_XYADGO_agnostic1)
done
show goal194: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextReqIs RdShared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i656 nextGOPendingIs_XYADGO_agnostic1)
done
show goal195: "HSTATE SD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_HSTATE MESI_State.distinct(187) MESI_State.distinct(261) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i113 nextDTHDataFrom2_XYADGO1 nextDTHDataFrom_IXADGO_invariant1)
done
show goal196: "HSTATE SD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_HSTATE IMADGO'_nextGOPendingIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i310 nextDTHDataFrom2_XYADGO1 nextDTHDataFrom_IXADGO_invariant1)
done
show goal197: "HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> (nextSnpRespIs RspIFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> nextSnpRespIs RspSFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_HSTATE IMADGO'_nextGOPendingIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i859 nextGOPendingIs_XYADGO_agnostic1)
done
show goal198: "HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> (nextSnpRespIs RspIFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> nextSnpRespIs RspSFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_HSTATE IMADGO'_nextSnpRespIs MESI_State.distinct(261) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i438 nextGOPendingIs_XYADGO_agnostic1)
done
show goal199: "HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis HSTATE_XYADGO1 \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux2_r84 i313 nextGOPendingIs_XYADGO_agnostic1 reqresps_empty_noGOPendingIs1)
done
show goal200: "C_msg_P_same SIA (nextGOPendingIs GO_WritePull) nextEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply simp
by (smt (verit) CSTATE_various_forms6 C_msg_P_same_def i314 nextEvict_various_forms2 nextGOPendingIs_various_forms4)
show goal201: "C_msg_P_same SIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextReqIs RdShared T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (metis CSTATE_inequality_invariant C_msg_state_def IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_nextReqIs MESI_State.distinct(289) MESI_State.distinct(413) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i47 nextGOPendingIs_XYADGO_agnostic1)
done
show goal202: "CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(413) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> htddatas1_general_rule_5_0)
done
show goal203: "CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (cases "dthdatas1 T")
apply  (auto)
apply (smt (verit) CSTATE_various_forms4 i317)
apply (smt (verit) CSTATE_various_forms4 i317)
apply (smt (verit) CSTATE_various_forms5 i317)
apply (smt (verit) butlast.simps(1) i56 list.distinct(1))
apply (smt (verit) i1x i2x i435 i99 list.discI)
apply (smt (verit) i101 i1x i2x i435 i580 list.distinct(1))
done
show goal204: "C_msg_P_same SIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextSnoopPending T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (metis CSTATE_inequality_invariant C_msg_P_same_def IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_nextGOPendingIs MESI_State.distinct(413) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i201 i318 i517 nextGOPendingIs_XYADGO_agnostic1)
done
show goal205: "CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (smt (verit) aux2_r84 reqresps_empty_noGOPendingIs1)
done
show goal206: "CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_HSTATE IMADGO'_nextGOPendingIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i320 i809 nextGOPendingIs_XYADGO_agnostic1)
done
show goal207: "C_msg_P_same SIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextDTHDataPending T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (metis CSTATE_inequality_invariant C_msg_P_same_def IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_nextDTHDataPending IMADGO'_nextGOPendingIs MESI_State.distinct(413) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i321 nextGOPendingIs_XYADGO_agnostic1)
done
show goal208: "CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(413) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextDTHDataFrom2_XYADGO1)
done
show goal209: "CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i323 nextDTHDataFrom2_XYADGO1 nextDTHDataFrom_IXADGO_invariant1 nextGOPendingIs_XYADGO_agnostic1)
done
show goal210: "C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) nextEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (metis CSTATE_otherside_rule_4_0 C_msg_P_same_def IMADGO'_nextEvict \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux2_r84 i324 nextGOPendingIs_XYADGO_agnostic1 reqresps_empty_noGOPendingIs1)
done
show goal211: "C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextReqIs RdShared T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (metis CSTATE_inequality_invariant C_msg_state_def IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_nextReqIs MESI_State.distinct(289) MESI_State.distinct(413) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i47 nextGOPendingIs_XYADGO_agnostic1)
done
show goal212: "C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextSnoopPending T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (smt (verit) aux2_r84 nextSnoopPending_def reqresps_empty_noGOPendingIs1)
done
show goal213:  "CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPendingIs GO_WritePullDrop ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (smt (verit) aux2_r84 reqresps_empty_noGOPendingIs1)
done
show goal214:  "CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPendingIs GO_WritePullDrop ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_HSTATE IMADGO'_nextGOPendingIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i328 i656 i666 nextGOPendingIs_XYADGO_agnostic1)
done
show goal215: "C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextDTHDataPending T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (metis C_msg_P_same_def IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_nextDTHDataPending IMADGO'_nextGOPendingIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux2_r84 i329 nextGOPendingIs_XYADGO_agnostic1 reqresps_empty_noGOPendingIs1)
done
show goal216: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant HSTATE_XYADGO1 IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(405) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal217: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE SA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant HSTATE_XYADGO1 IMADGO'_HSTATE MESI_State.distinct(265) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal218: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE SA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_HSTATE IMADGO'_nextHTDDataPending \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i334 i656 nextGOPending_yes_reqresp_rule_6_1)
done
show goal219: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1)"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(265) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal220: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0)"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_nextHTDDataPending \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i336 nextGOPending_yes_reqresp_rule_6_1)
done
show goal221: "C_not_C_msg Modified IMAD nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(19) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal222: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal223: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> nextStore ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (smt (verit) aux2_r79)
done
show goal224: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> nextStore ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_nextStore \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i340 nextGOPending_yes_reqresp_rule_6_1 nextStore_general_rule_4_0)
done
show goal225: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal226: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms empty_no_snoop_variant2 i341 i465 nextGOPending_DeviceIMADGO nextGOPending_yes_reqresp_rule_6_1)
done
show goal227: "snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<longrightarrow> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r84)
done
show goal228: "snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<longrightarrow> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r84)
done
show goal229: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i909 nextGOPending_yes_reqresp_rule_6_1)
done
show goal230: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i466 i694 nextGOPending_DeviceIMADGO nextGOPending_yes_reqresp_rule_6_1)
done
show goal231: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal232: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i909 nextGOPending_yes_reqresp_rule_6_1)
done
show goal233: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> nextStore ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (smt (verit) aux2_r79)
done
show goal234: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> nextStore ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_otherside_rule_6 IMADGO'_nextStore \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i909 nextGOPending_yes_reqresp_rule_6_1)
done
show goal235: "C_msg_P_same IMA nextGOPending nextStore ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (metis CSTATE_otherside_rule_6 IMADGO'_nextStore \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux2_r79 i371 nextGOPending_yes_reqresp_rule_6_1 nextStore_general_rule_4_0)
done
show goal236: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(229) MESI_State.distinct(361) MESI_State.distinct(407) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal237: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_nextHTDDataPending \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i353 nextGOPending_yes_reqresp_rule_6_1)
done
show goal238: "C_msg_P_oppo IMA nextGOPending (\<lambda>T i. \<not> nextSnoopPending T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply simp
by (metis i56 nextReqRespIs.simps(1))
show goal239: "C_msg_P_oppo SMA nextGOPending (\<lambda>T i. \<not> nextSnoopPending T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply simp
by (metis i56 nextReqRespIs.simps(1))
show goal240: "C_msg_P_oppo ISA nextGOPending (\<lambda>T i. \<not> nextSnoopPending T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply simp
by (smt (verit) i56 nextReqRespIs.simps(1))
show goal241: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal242: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i358 nextGOPending_yes_reqresp_rule_6_1)
done
show goal243: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> \<not> CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> \<not> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> \<not> ((CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> \<not> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis C_not_C_msg_def IMADGO'_CSTATE_otherside IMADGO'_nextHTDDataPending IMADGO'_nextSnoopIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i337 i465 i51 i909 nextGOPending_yes_reqresp_rule_6_1 nextSnoopIs_general_rule_6_0)
done
show goal244: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> ((CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> \<not> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_nextSnoopIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i466 i51 i909 nextGOPending_yes_reqresp_rule_6_1 nextSnoopIs_general_rule_6_0)
done
show goal245: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> (dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<or> HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]))"
apply  (insert assms)
apply (metis CSTATE_disj1 IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(331) MESI_State.distinct(361) MESI_State.distinct(405) MESI_State.distinct(407) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal246: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> (dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<or> HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]))"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_HSTATE IMADGO'_nextHTDDataPending aux2_r84 empty_no_snoop_variant2 i1x i2x i465 nextGOPending_yes_reqresp_rule_6_1 snps2_general_rule_6_0)
done
show goal247: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_sameside IXADGO_dthdatas1_invariant \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms dthdatas1_general_rule_3_0 i435)
done
show goal248: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms empty_no_snoop_variant2 i341 i465 i909 nextGOPending_DeviceIMADGO nextGOPending_yes_reqresp_rule_6_1)
done
show goal249: "C_msg_P_same SMA nextGOPending nextStore ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_nextStore \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux2_r79 i371 nextGOPending_yes_reqresp_rule_6_1)
done
show goal250: "CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis HOST_State.distinct(271) HSTATE_XYADGO1 HSTATE_invariant3 IMADGO'_HSTATE IMADGO'_nextHTDDataPending \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i182 i338)
done
show goal251: "CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis CSTATE_otherside_rule_6 HOST_State.distinct(151) HSTATE_invariant3 IMADGO'_CSTATE_otherside IMADGO'_HSTATE IMADGO'_nextHTDDataPending \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i338 i353 i367 nextGOPending_yes_reqresp_rule_6_1)
done
show goal252: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> nextLoad ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(191) MESI_State.distinct(229) MESI_State.distinct(265) MESI_State.distinct(299) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextLoad_general_rule_4_0 nextStore_IMADGO)
done
show goal253: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> nextLoad ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_otherside_rule_6 \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i146 i369 i752old nextGOPending_yes_reqresp_rule_6_1 nextLoad2_IMADGO nextLoad_DeviceIMADGO)
done
show goal254: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> nextStore ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (smt (verit) aux2_r79)
done
show goal255: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> nextStore ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_nextStore \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i340 i371 i909 nextGOPending_yes_reqresp_rule_6_1)
done
show goal256: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> (dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<or> nextSnpRespIs RspSFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> HSTATE SD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]))"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_HSTATE IMADGO'_nextHTDDataPending MESI_State.distinct(109) MESI_State.distinct(229) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms dthdatas1_general_rule_3_0 i435 i462 nextGOPending_yes_reqresp_rule_6_1)
done
show goal257: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> (dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<or> nextSnpRespIs RspSFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> HSTATE SD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]))"
apply  (insert assms)
apply (metis CSTATE_otherside_rule_4_0 IMADGO'_CSTATE_otherside IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux2_r84 empty_no_snoop2 i1x i2x i465 nextGOPending_yes_reqresp_rule_6_1 snps2_general_rule_6_0 xyad_go_invariant2)
done
show goal258: "CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal259: "CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i375 i656 nextGOPending_yes_reqresp_rule_6_1)
done
show goal260: "CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis CSTATE_disj1 IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(299) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal261: "CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_HSTATE IMADGO'_nextHTDDataPending \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i383 i609 i656 i666 nextGOPending_yes_reqresp_rule_6_1)
done
show goal262: "CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(299) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> snps1_general_rule_6_0)
done
show goal263: "CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (cases "dthdatas1 T")
apply  (auto)
apply (smt (verit) CSTATE_various_forms4 i378)
apply (smt (verit) CSTATE_various_forms4 i378)
apply (smt (verit) CSTATE_various_forms4 i378)
apply (smt (verit) i1x i2x i341 i909)
apply (smt (verit) butlast.simps(1) i56 list.distinct(1))
apply (smt (verit) i1x i2x i435 i99 list.discI)
apply (smt (verit) i1x i2x i435 i95 list.discI)
apply (smt (verit) i1x i2x i341)
done
show goal264: "CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> \<not> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant MESI_State.distinct(299))
done
show goal265: "CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> \<not> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_HSTATE IMADGO'_nextReqIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i380 nextGOPending_yes_reqresp_rule_6_1)
done
show goal266: "CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r84)
done
show goal267: "CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (cases "dthdatas1 T")
apply  (auto)
apply (smt (verit) CSTATE_various_forms6 i382)
apply (smt (verit) i1x i2x i435 i95 list.discI)
done
show goal268: "CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(109) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextSnoopIs_general_rule_6_0)
done
show goal269: "CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i385 i465 nextGOPending_yes_reqresp_rule_6_1)
done
show goal270: "CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_nextSnoopIs MESI_State.distinct(109) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal271: "CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (smt (verit) aux2_r84 empty_no_snoop_variant2)
done
show goal272: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r84)
done
show goal273: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r84 empty_no_snoop2)
done
show goal274: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant MESI_State.distinct(405))
done
show goal275: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (smt (verit) aux2_r84 empty_no_snoop_variant2)
done
show goal276: "nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis i100 i2x i760 i94 nextReqIs_general_rule_6_0 nextReqIs_not_various_forms1 reqresps_empty_noGOPending1)
done
show goal277: "nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_nextReqIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i393 i909 nextGOPending_yes_reqresp_rule_6_1)
done
show goal278: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> CXL_SPG_used ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_nextReqIs MESI_State.distinct(405) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextSnoopIs_general_rule_6_0)
done
show goal279: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> CXL_SPG_used ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_nextReqIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i909 nextGOPending_yes_reqresp_rule_6_1)
done
show goal280: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant MESI_State.distinct(191))
done
show goal281: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i401 i465 nextGOPending_yes_reqresp_rule_6_1)
done
show goal282: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_nextSnoopIs MESI_State.distinct(191) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal283: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (smt (verit) aux2_r84 empty_no_snoop_variant2)
done
show goal284: "HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis HSTATE_XYADGO1 SARspSFwdM_invariant1 \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux2_r84 i408 nextSnpRespIs_general_rule_6_0 nextSnpRespIs_invariant1)
done
show goal285: "HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i422 nextDTHDataFrom2_XYADGO1 nextDTHDataFrom_IXADGO_invariant1 nextGOPending_DeviceIMADGO)
done
show goal286: "HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_sameside IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextDTHDataFrom2_XYADGO1)
done
show goal287: "HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> nextReqIs CleanEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis IMADGO'_HSTATE IMADGO'_nextReqIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i471 nextDTHDataFrom1_XYADGO1 nextDTHDataFrom_IXADGO_invariant1)
done
show goal288: "HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> nextReqIs CleanEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> \<not> nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_HSTATE IMADGO'_nextReqIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i472 nextDTHDataFrom2_XYADGO1 nextDTHDataFrom_IXADGO_invariant1)
done
show goal289: "HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis HSTATE_XYADGO1 IMADGO'_HSTATE IMADGO'_nextGOPendingIs aux2_r84 i421 nextGOPendingIs_XYADGO_agnostic1 reqresps_empty_noGOPendingIs1)
done
show goal290: "HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i424 nextDTHDataFrom2_XYADGO1 nextDTHDataFrom_IXADGO_invariant1)
done
show goal291: "HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis HSTATE_general_rule_4_0 i2x i433 nextDTHDataFrom2_XYADGO1 reqresps_empty_noGOPending1)
done
show goal292: "HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r84)
done
show goal293: "HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis HSTATE_general_rule_4_0 i2x i433 nextDTHDataFrom2_XYADGO1 reqresps_empty_noGOPending1)
done
show goal294: "HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> nextReqIs CleanEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis IMADGO'_HSTATE IMADGO'_nextReqIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i473 nextDTHDataFrom1_XYADGO1 nextDTHDataFrom_IXADGO_invariant1)
done
show goal295: "HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> nextReqIs CleanEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> \<not> nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_HSTATE IMADGO'_nextReqIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i474 nextDTHDataFrom2_XYADGO1 nextDTHDataFrom_IXADGO_invariant1)
done
show goal296: "HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> reqs2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant MESI_State.distinct(19) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i430 nextDTHDataFrom1_XYADGO1 nextDTHDataFrom_IXADGO_invariant1 reqs2_IMADGO)
done
show goal297: "HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> reqs1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis HSTATE_general_rule_4_0 i2x i433 nextDTHDataFrom2_XYADGO1 reqresps_empty_noGOPending1)
done
show goal298: "HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis assms dthdatas1_general_rule_3_0 ext i435 nextDTHDataFrom_def)
done
show goal299: "HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r84)
done
show goal300: "(HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE SA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])) \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<longrightarrow> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<or> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis IMADGO'_HSTATE SARspSFwdM_invariant1 \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> htddatas1_general_rule_5_0 i2x i343 nextSnpRespIs_general_rule_6_0 nextSnpRespIs_invariant1 reqresps_empty_noGOPending1)
done
show goal301: "(HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE SA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])) \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<longrightarrow> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<or> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis HTDDataPending_htddatas_invariant2 IMADGO'_CSTATE_otherside IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 i159 i408 i444 nextGOPending_yes_reqresp_rule_6_1 nextHTDDataPending_various_forms2 snpresps2_xyad_go_invariant xyad_go_invariant2)
done
show goal302: "nextSnpRespIs RspSFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_nextSnpRespIs MESI_State.distinct(105) MESI_State.distinct(347) MESI_State.distinct(355) MESI_State.distinct(359) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i441 nextSnpRespIs_general_rule_6_0)
done
show goal303: "nextSnpRespIs RspSFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_otherside_rule_6 IMADGO'_nextSnpRespIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i442 i909 nextGOPending_yes_reqresp_rule_6_1)
done
show goal304: "(CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_disj1 HSTATE_general_rule_4_0 IMADGO'_HSTATE IMADGO'_nextReqIs_invariant1 MESI_State.distinct(151) MESI_State.distinct(299) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux2_r84 empty_no_snoop_variant2 i1x i2x i460 i465 nextGOPending_yes_reqresp_rule_6_1 snps2_general_rule_6_0)
done
show goal305: "(CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_otherside_rule_6 HOST_State.distinct(149) HOST_State.distinct(17) HOST_State.distinct(249) HOST_State.distinct(271) HSTATE_invariant4 IMADGO'_HSTATE aux_r77 hstate_invariants(14) i148 i1x i2x i460 i909 nextReqIs_general_rule_6_0 xyad_go_invariant2)
done
show goal306: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(19) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextSnoopIs_general_rule_6_0)
done
show goal307: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis C_not_C_msg_def IMADGO'_CSTATE_otherside IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i337 nextGOPending_yes_reqresp_rule_6_1)
done
show goal308: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant IMADGO'_nextSnoopIs MESI_State.distinct(19) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal309: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis C_not_C_msg_def IMADGO'_CSTATE_otherside IMADGO'_nextSnoopIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i337 nextGOPending_yes_reqresp_rule_6_1)
done
show goal310: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis IMADGO'_HSTATE IMADGO'_nextSnoopIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i694 nextSnoopIs_general_rule_6_0)
done
show goal311: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i465 i693 nextGOPending_yes_reqresp_rule_6_1)
done
show goal312: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant CSTATE_otherside_rule_6 IMADGO'_nextSnoopIs assms i620)
done
show goal313: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (smt (verit) aux2_r84 empty_no_snoop_variant2)
done
show goal314: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(331) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextSnoopIs_general_rule_6_0)
done
show goal315: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_HSTATE IMADGO'_nextSnoopIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i695 nextGOPending_yes_reqresp_rule_6_1)
done
show goal316: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_nextSnoopIs MESI_State.distinct(331) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal317: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (smt (verit) aux2_r84 empty_no_snoop_variant2)
done
show goal318: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(361) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextSnoopIs_general_rule_6_0)
done
show goal319: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i465 i697 nextGOPending_yes_reqresp_rule_6_1)
done
show goal320: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_nextSnoopIs MESI_State.distinct(361) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal321: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (smt (verit) aux2_r84 empty_no_snoop_variant2)
done
show goal322: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis IMADGO'_HSTATE IMADGO'_nextSnoopIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i691 nextSnoopIs_general_rule_6_0)
done
show goal323: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i742 nextGOPending_yes_reqresp_rule_6_1)
done
show goal324: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_nextSnoopIs MESI_State.distinct(397) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal325: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_nextSnoopIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i742 nextGOPending_yes_reqresp_rule_6_1)
done
show goal326: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis IMADGO'_HSTATE IMADGO'_nextSnoopIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i691 nextSnoopIs_general_rule_6_0)
done
show goal327: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis C_not_C_msg_def IMADGO'_CSTATE_otherside IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i337 nextGOPending_yes_reqresp_rule_6_1)
done
show goal328: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_nextSnoopIs MESI_State.distinct(19) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal329: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis C_not_C_msg_def IMADGO'_CSTATE_otherside IMADGO'_nextSnoopIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i337 nextGOPending_yes_reqresp_rule_6_1)
done
show goal330: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> reqs1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(19) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal331: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> reqs2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms empty_no_snoop2 i341 i465 nextGOPending_yes_reqresp_rule_6_1 reqs2_IMADGO)
done
show goal332: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(19) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> htddatas1_general_rule_5_0)
done
show goal333: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms empty_no_snoop_variant2 i341 i465 nextGOPending_yes_reqresp_rule_6_1)
done
show goal334: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextReqIs RdShared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i666 nextReqIs_general_rule_6_0)
done
show goal335: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextReqIs RdShared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i666 nextGOPending_yes_reqresp_rule_6_1)
done
show goal336: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i666 nextGOPending_yes_reqresp_rule_6_1)
done
show goal337: "nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_nextReqIs MESI_State.distinct(151) MESI_State.distinct(265) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextReqIs_general_rule_6_0)
done
show goal338: "nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> \<not> CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_nextReqIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i495 nextGOPending_yes_reqresp_rule_6_1)
done
show goal339: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i666 nextReqIs_general_rule_6_0)
done
show goal340: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i666 nextGOPending_yes_reqresp_rule_6_1)
done
show goal341: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i666 nextReqIs_general_rule_6_0)
done
show goal342: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i666 nextGOPending_yes_reqresp_rule_6_1)
done
show goal343: "CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r84)
done
show goal344: "CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r84 empty_no_snoop2)
done
show goal345: "CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant IMADGO'_HSTATE MESI_State.distinct(413) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextSnoopIs_general_rule_6_0)
done
show goal346: "CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_HSTATE IMADGO'_nextSnoopIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i503 nextGOPending_yes_reqresp_rule_6_1)
done
show goal347: "CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> CXL_SPG_used ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> nextReqIs CleanEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant IMADGO'_nextReqIs MESI_State.distinct(413) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextSnoopIs_general_rule_6_0)
done
show goal348: "CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> CXL_SPG_used ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> nextReqIs CleanEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (smt (verit) aux2_r84 empty_no_snoop2)
done
show goal349: "CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_nextSnoopIs MESI_State.distinct(413) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal350: "CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (smt (verit) aux2_r84 empty_no_snoop_variant2)
done
show goal351: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_nextSnoopIs MESI_State.distinct(405) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal352: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_nextSnoopIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i909 nextGOPending_yes_reqresp_rule_6_1)
done
show goal353: "HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i609 nextGOPending_yes_reqresp_rule_6_1)
done
show goal354: "HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> (\<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply simp
by (metis CSTATE_various_forms4 HSTATE_various_forms2 i107)
show goal355: "HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> (\<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply simp
by (metis CSTATE_various_forms6 i71 startsWithProp.simps(1))
show goal356: "HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i609 nextReqIs_general_rule_6_0)
done
show goal357: "HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i609 nextGOPending_yes_reqresp_rule_6_1)
done
show goal358: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal359: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i909 nextGOPending_yes_reqresp_rule_6_1)
done
show goal360: "C_msg_P_oppo SMAD nextGOPending (\<lambda>T i. \<not> nextSnoopPending T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i909 nextGOPending_yes_reqresp_rule_6_1)
done
show goal361: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i656 nextReqIs_general_rule_6_0)
done
show goal362: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i656 nextGOPending_yes_reqresp_rule_6_1)
done
show goal363: "nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<or> nextReqRespStateIs Invalid (reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]))"
apply  (insert assms)
apply (smt (verit) aux2_r84 reqresps_empty_noGOPendingIs1)
done
show goal364: "nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<or> nextReqRespStateIs Invalid (reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]))"
apply  (insert assms)
apply (smt (verit) aux2_r84)
done
show goal365: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> nextEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i656 nextReqIs_general_rule_6_0)
done
show goal366: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> nextEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i656 nextGOPending_yes_reqresp_rule_6_1)
done
show goal367: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextReqIs CleanEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> nextEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i656 nextReqIs_general_rule_6_0)
done
show goal368: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextReqIs CleanEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> nextEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i656 nextGOPending_yes_reqresp_rule_6_1)
done
show goal369: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i656 nextReqIs_general_rule_6_0)
done
show goal370: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i656 nextGOPending_yes_reqresp_rule_6_1)
done
show goal371: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextReqIs CleanEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i656 nextReqIs_general_rule_6_0)
done
show goal372: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextReqIs CleanEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i656 nextGOPending_yes_reqresp_rule_6_1)
done
show goal373: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i656 nextReqIs_general_rule_6_0)
done
show goal374: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i656 nextGOPending_yes_reqresp_rule_6_1)
done
show goal375: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextReqIs CleanEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i656 nextReqIs_general_rule_6_0)
done
show goal376: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextReqIs CleanEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i656 nextGOPending_yes_reqresp_rule_6_1)
done
show goal377: "CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant IMADGO'_nextSnoopIs MESI_State.distinct(109) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal378: "CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r84 empty_no_snoop2)
done
show goal379: "nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> nextEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis IMADGO'_nextEvict IMADGO'_nextReqIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i538 nextReqIs_general_rule_6_0)
done
show goal380: "nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> nextEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_nextEvict IMADGO'_nextReqIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i539 nextGOPending_yes_reqresp_rule_6_1)
done
show goal381: "nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i574 nextDTHDataFrom2_XYADGO1)
done
show goal382: "nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i574 nextDTHDataFrom2_XYADGO1)
done
show goal383: "nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i666 nextGOPending_yes_reqresp_rule_6_1)
done
show goal384: "nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i666 nextGOPending_yes_reqresp_rule_6_1)
done
show goal385: "nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<or> nextReqRespStateIs Invalid (reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]))"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i666 nextReqIs_general_rule_6_0)
done
show goal386: "nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<or> nextReqRespStateIs Invalid (reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]))"
apply  (insert assms)
apply (smt (verit) aux2_r84)
done
show goal387: "CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> (CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1)"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(409) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal388: "CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> (CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0)"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_nextHTDDataPending MESI_State.distinct(229) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i547 nextGOPending_yes_reqresp_rule_6_1)
done
show goal389: "CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(409) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal390: "CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (smt (verit) aux2_r84 empty_no_snoop2)
done
show goal391: "CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_HSTATE IMADGO'_nextSnoopIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i685 i691 nextGOPending_yes_reqresp_rule_6_1)
done
show goal392: "CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis HOST_State.distinct(249) HSTATE_invariant3 IMADGO'_CSTATE_otherside IMADGO'_HSTATE IMADGO'_nextHTDDataPending IMADGO'_nextSnoopIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i148 i465 i466 i685 i694 nextGOPending_yes_reqresp_rule_6_1 nextSnoopIs_invariant_variant1)
done
show goal393: "CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r84)
done
show goal394: "CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_sameside IMADGO'_nextHTDDataPending \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms empty_no_snoop2 i341 i465 nextGOPending_yes_reqresp_rule_6_1)
done
show goal395: "CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_nextReqIs MESI_State.distinct(409) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal396: "CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_nextHTDDataPending IMADGO'_nextReqIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i555 nextGOPending_yes_reqresp_rule_6_1)
done
show goal397: "nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> nextReqIs CleanEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_nextReqIs MESI_State.distinct(343) MESI_State.distinct(355) MESI_State.distinct(359) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i556 i946 nextReqIs_general_rule_6_0)
done
show goal398: "nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> nextReqIs CleanEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_nextReqIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i557 i947 nextGOPending_yes_reqresp_rule_6_1)
done
show goal399: "CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(109) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i558 nextGOPending_yes_reqresp_rule_6_1)
done
show goal400: "CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(109) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal401: "CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis HOST_State.distinct(149) HOST_State.distinct(17) HOST_State.distinct(249) HOST_State.distinct(271) HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 nextGOPending_yes_reqresp_rule_6_1)
done
show goal402: "nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> nextReqIs CleanEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> nextEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis IMADGO'_nextEvict \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i561 nextReqIs_general_rule_6_0)
done
show goal403: "nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> nextReqIs CleanEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> nextEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_nextEvict IMADGO'_nextReqIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i562 nextGOPending_yes_reqresp_rule_6_1)
done
show goal404: "nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> nextReqIs CleanEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_nextReqIs MESI_State.distinct(299) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextReqIs_general_rule_6_0)
done
show goal405: "nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> nextReqIs CleanEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_nextReqIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i564 nextGOPending_yes_reqresp_rule_6_1)
done
show goal406: "nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> nextReqIs CleanEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant IMADGO'_nextReqIs MESI_State.distinct(397) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextReqIs_general_rule_6_0)
done
show goal407: "nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> nextReqIs CleanEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_nextReqIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i742 nextGOPending_yes_reqresp_rule_6_1)
done
show goal408: "CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextReqIs RdShared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i666 nextGOPending_yes_reqresp_rule_6_1)
done
show goal409: "CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextReqIs RdShared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i666 nextGOPending_yes_reqresp_rule_6_1)
done
show goal410: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> \<not> CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> \<not> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i666 nextGOPending_yes_reqresp_rule_6_1)
done
show goal411: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> ((CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> (nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0)) \<and> \<not> ((CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> (nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1))"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i574 nextGOPending_yes_reqresp_rule_6_1)
done
show goal412: "nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i666 nextGOPendingIs_XYADGO_agnostic1)
done
show goal413: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(397) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal414: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i742 nextGOPending_yes_reqresp_rule_6_1)
done
show goal415: "nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (smt (verit) aux2_r84 reqresps_empty_noGOPendingIs1)
done
show goal416: "nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (smt (verit) aux2_r84 reqresps_empty_noGOPendingIs1)
done
show goal417: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_HSTATE IMADGO'_nextHTDDataPending MESI_State.distinct(361) MESI_State.distinct(407) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i182 nextGOPending_yes_reqresp_rule_6_1)
done
show goal418: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis CSTATE_disj1 IMADGO'_CSTATE_otherside IMADGO'_HSTATE IMADGO'_nextHTDDataPending MESI_State.distinct(349) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i183 i581 i909 nextGOPending_yes_reqresp_rule_6_1)
done
show goal419: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(397) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> htddatas1_general_rule_5_0)
done
show goal420: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i742 nextGOPending_yes_reqresp_rule_6_1)
done
show goal421: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(397) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextSnoopIs_general_rule_6_0)
done
show goal422: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i742 nextGOPending_yes_reqresp_rule_6_1)
done
show goal423: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_nextSnoopIs MESI_State.distinct(397) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal424: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_nextSnoopIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i742 nextGOPending_yes_reqresp_rule_6_1)
done
show goal425: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_HSTATE IMADGO'_nextGOPendingIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux2_r84 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i1x i2x i313 i656 i666 nextGOPendingIs_XYADGO_agnostic1 reqresps_empty_noGOPendingIs1)
done
show goal426: "CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPendingIs GO_WritePullDrop ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (smt (verit) aux2_r84 reqresps_empty_noGOPendingIs1)
done
show goal427: "CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPendingIs GO_WritePullDrop ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant MESI_State.distinct(401))
done
show goal428: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms dthdatas1_general_rule_3_0 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i666)
done
show goal429: "CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant IMADGO'_nextSnoopIs MESI_State.distinct(151) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextSnoopIs_general_rule_6_0)
done
show goal430: "CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_nextSnoopIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i593 nextGOPending_yes_reqresp_rule_6_1)
done
show goal431: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(19) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal432: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(397) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal433: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis HOST_State.distinct(149) HOST_State.distinct(17) HOST_State.distinct(249) HOST_State.distinct(271) HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) nextGOPending_yes_reqresp_rule_6_1)
done
show goal434: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r84 empty_no_snoop_variant2)
done
show goal435: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal436: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i909 nextGOPending_yes_reqresp_rule_6_1)
done
show goal437: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis HOST_State.distinct(249) HSTATE_invariant3 IMADGO'_CSTATE_otherside IMADGO'_HSTATE IMADGO'_nextHTDDataPending IMADGO'_nextSnoopIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i465 i600 i697 i909 nextGOPending_yes_reqresp_rule_6_1)
done
show goal438: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (smt (verit) aux2_r84 empty_no_snoop_variant2)
done
show goal439: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant HSTATE_XYADGO1 IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(191) MESI_State.distinct(229) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal440: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> \<not> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i609 i666 nextGOPending_yes_reqresp_rule_6_1)
done
show goal441: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis HSTATE_XYADGO1 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i609 i666)
done
show goal442: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i609 i666 nextGOPending_yes_reqresp_rule_6_1)
done
show goal443: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis HSTATE_XYADGO1 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i609 i666)
done
show goal444: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i609 i666 nextGOPending_yes_reqresp_rule_6_1)
done
show goal445: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> (CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> (nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0))"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant HSTATE_XYADGO1 IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(265) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal446: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> (nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0))"
apply  (insert assms)
apply (metis HSTATE_XYADGO1 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i609 i666)
done
show goal447: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> (CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> (nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0))"
apply  (insert assms)
apply (metis CSTATE_disj1 IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(405) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal448: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> (CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> (nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1))"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i609 i666 nextGOPending_yes_reqresp_rule_6_1)
done
show goal449: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> (nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1))"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i609 i666 nextGOPending_yes_reqresp_rule_6_1)
done
show goal450: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<or> HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> (CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> (nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1))"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i574 i609 nextGOPending_yes_reqresp_rule_6_1)
done
show goal451: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant IMADGO'_nextSnoopIs MESI_State.distinct(191) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal452: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r84 empty_no_snoop2)
done
show goal453: "CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_disj1 IMADGO'_nextSnoopIs MESI_State.distinct(229) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal454: "CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r84 empty_no_snoop2)
done
show goal455: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_disj1 IMADGO'_nextSnoopIs MESI_State.distinct(265) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal456: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r84 empty_no_snoop2)
done
show goal457: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant IMADGO'_nextSnoopIs MESI_State.distinct(331) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal458: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r84 empty_no_snoop_variant2)
done
show goal459: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis HTDDataPending_htddatas_invariant2 IMADGO'_CSTATE_otherside IMADGO'_nextHTDDataPending IMADGO'_nextSnoopIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms empty_no_snoop_variant2 i341 i465 i620 nextGOPending_yes_reqresp_rule_6_1)
done
show goal460: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r84 empty_no_snoop_variant2)
done
show goal461: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant IMADGO'_nextSnoopIs MESI_State.distinct(361) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal462: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r84 empty_no_snoop_variant2)
done
show goal463: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal464: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r84 empty_no_snoop2)
done
show goal465: "CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant IMADGO'_nextSnoopIs MESI_State.distinct(409) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal466: "CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r84 empty_no_snoop_variant2)
done
show goal467: "CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant IMADGO'_nextSnoopIs MESI_State.distinct(407) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal468: "CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r84 empty_no_snoop_variant2)
done
show goal469: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant HSTATE_XYADGO1 IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(191) MESI_State.distinct(229) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal470: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i633 i748 nextGOPending_yes_reqresp_rule_6_1)
done
show goal471: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> (nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<longrightarrow> \<not> HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis HOST_State.distinct(151) HOST_State.distinct(19) HOST_State.distinct(251) HOST_State.distinct(271) HSTATE_XYADGO1 HSTATE_invariant3 IMADGO'_HSTATE IMADGO'_nextHTDDataPending \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i182)
done
show goal472: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> (nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<longrightarrow> \<not> HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis CSTATE_otherside_rule_6 IMADGO'_HSTATE IMADGO'_nextHTDDataPending \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i635 nextGOPending_yes_reqresp_rule_6_1)
done
show goal473: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis HOST_State.distinct(149) HOST_State.distinct(17) HOST_State.distinct(249) HOST_State.distinct(271) HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 nextGOPending_yes_reqresp_rule_6_1)
done
show goal474: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis HOST_State.distinct(149) HOST_State.distinct(17) HOST_State.distinct(249) HOST_State.distinct(271) HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 nextGOPending_yes_reqresp_rule_6_1)
done
show goal475: "CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis HOST_State.distinct(149) HOST_State.distinct(17) HOST_State.distinct(249) HOST_State.distinct(271) HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 nextGOPending_yes_reqresp_rule_6_1)
done
show goal476: "CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis HOST_State.distinct(149) HOST_State.distinct(17) HOST_State.distinct(249) HOST_State.distinct(271) HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 nextGOPending_yes_reqresp_rule_6_1)
done
show goal477: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> (CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1)"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_otherside_rule_6 empty_no_snoop_variant2 i106 i119 i1x i2x i341 i465 i640 i760 i846 i909 nextGOPending_yes_reqresp_rule_6_1 reqresps_empty_noGOPending1 xyad_go_invariant2)
done
show goal478: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> (CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0)"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal479: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_otherside_rule_6 empty_no_snoop_variant2 i119 i1x i2x i341 i465 i569 i642 i643 i760 i831 i846 i909 reqresps_empty_noGOPending1 xyad_go_invariant2)
done
show goal480: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_nextHTDDataPending MESI_State.distinct(229) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i643 nextGOPending_yes_reqresp_rule_6_1)
done
show goal481: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant CSTATE_otherside_rule_6 HOST_State.distinct(249) HSTATE_invariant4 MESI_State.distinct(101) MESI_State.distinct(261) aux_r77 i106 i107 i148 i160 i161 i1x i2x i385 i465 i558 i641 i644 i74 i760 i909 reqresps_empty_noGOPending1 xyad_go_invariant2)
done
show goal482: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(109) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal483: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant MESI_State.distinct(191))
done
show goal484: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i401 i465 nextGOPending_yes_reqresp_rule_6_1)
done
show goal485: "CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(229) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextSnoopIs_general_rule_6_0)
done
show goal486: "CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i465 i647 nextGOPending_yes_reqresp_rule_6_1)
done
show goal487: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal488: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i148 i465 nextGOPending_DeviceIMADGO nextGOPending_yes_reqresp_rule_6_1)
done
show goal489: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(265) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextSnoopIs_general_rule_6_0)
done
show goal490: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_HSTATE IMADGO'_nextHTDDataPending \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i148 i465 nextGOPending_yes_reqresp_rule_6_1)
done
show goal491: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis HSTATE_XYADGO1 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i656)
done
show goal492: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i656 nextGOPending_yes_reqresp_rule_6_1)
done
show goal493: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis HSTATE_XYADGO1 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i656)
done
show goal494: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> \<not> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i656 nextGOPending_yes_reqresp_rule_6_1)
done
show goal495: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> (nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0))"
apply  (insert assms)
apply (metis HOST_State.distinct(19) HOST_State.distinct(3) HOST_State.distinct(77) HOST_State.distinct(85) HSTATE_XYADGO1 HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms aux_r77 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i656)
done
show goal496: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> (nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1))"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i656 nextGOPending_yes_reqresp_rule_6_1)
done
show goal497: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> (CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> (nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0))"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant HSTATE_XYADGO1 IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(405) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal498: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> (CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> (nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1))"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i656 nextGOPending_yes_reqresp_rule_6_1)
done
show goal499: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis HOST_State.distinct(3) HOST_State.distinct(77) HOST_State.distinct(85) HOST_State.distinct(89) HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) nextGOPending_yes_reqresp_rule_6_1)
done
show goal500: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i666 nextGOPending_yes_reqresp_rule_6_1)
done
show goal501: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis HSTATE_XYADGO1 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i666)
done
show goal502: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> \<not> CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> \<not> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i666 nextGOPending_yes_reqresp_rule_6_1)
done
show goal503: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> (CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0)"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal504: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> (CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1)"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i666 nextGOPending_yes_reqresp_rule_6_1)
done
show goal505: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0)"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal506: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1)"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i666 nextGOPending_yes_reqresp_rule_6_1)
done
show goal507: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> (CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0)"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal508: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> (CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1)"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i666 nextGOPending_yes_reqresp_rule_6_1)
done
show goal509: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant HSTATE_XYADGO1 IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(229) MESI_State.distinct(361) MESI_State.distinct(407) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal510: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i666 nextGOPending_yes_reqresp_rule_6_1)
done
show goal511: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis HSTATE_XYADGO1 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i666)
done
show goal512: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i666 nextGOPending_yes_reqresp_rule_6_1)
done
show goal513: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis HSTATE_XYADGO1 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i666)
done
show goal514: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i666 nextGOPending_yes_reqresp_rule_6_1)
done
show goal515: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis HSTATE_XYADGO1 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i666)
done
show goal516: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i666 nextGOPending_yes_reqresp_rule_6_1)
done
show goal517: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r84)
done
show goal518: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_sameside IMADGO'_nextHTDDataPending \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms empty_no_snoop2 i341 i465 nextGOPending_yes_reqresp_rule_6_1)
done
show goal519: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal520: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_sameside IMADGO'_nextHTDDataPending \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms empty_no_snoop_variant2 i341 i465 nextGOPending_yes_reqresp_rule_6_1)
done
show goal521: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_nextSnoopIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i685 nextGOPending_yes_reqresp_rule_6_1)
done
show goal522: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_nextSnoopIs SnoopType.distinct(1) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i465 i51 nextGOPending_yes_reqresp_rule_6_1 nextSnoopIs_invariant_variant1)
done
show goal523: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_nextSnoopIs MESI_State.distinct(361) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal524: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_nextSnoopIs SnoopType.distinct(1) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i465 i51 nextGOPending_yes_reqresp_rule_6_1 nextSnoopIs_invariant_variant1)
done
show goal525: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_nextSnoopIs MESI_State.distinct(331) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal526: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_otherside IMADGO'_nextSnoopIs MESI_State.distinct(261) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i686 nextGOPending_yes_reqresp_rule_6_1)
done
show goal527: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis IMADGO'_HSTATE IMADGO'_nextSnoopIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i691 nextSnoopIs_general_rule_6_0)
done
show goal528: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_HSTATE IMADGO'_nextSnoopIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i688 nextGOPending_yes_reqresp_rule_6_1)
done
show goal529: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(361) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextSnoopIs_general_rule_6_0)
done
show goal530: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_HSTATE IMADGO'_nextSnoopIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i690 nextGOPending_yes_reqresp_rule_6_1)
done
show goal531: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(331) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextSnoopIs_general_rule_6_0)
done
show goal532: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_HSTATE IMADGO'_nextSnoopIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i698 nextGOPending_yes_reqresp_rule_6_1)
done
show goal533: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis HOST_State.distinct(169) HOST_State.distinct(269) HOST_State.distinct(307) HOST_State.distinct(37) HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) nextGOPending_yes_reqresp_rule_6_1)
done
show goal534: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis HOST_State.distinct(169) HOST_State.distinct(227) HOST_State.distinct(269) HOST_State.distinct(307) HOST_State.distinct(37) HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) nextReqIs_general_rule_6_0)
done
show goal535: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_HSTATE IMADGO'_nextReqIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i393 i909 nextGOPending_yes_reqresp_rule_6_1)
done
show goal536: "HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis HOST_State.distinct(167) HOST_State.distinct(267) HOST_State.distinct(305) HOST_State.distinct(35) HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) nextGOPending_yes_reqresp_rule_6_1)
done
show goal537: "HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> length (dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])) \<le> 1 \<and> length (dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])) \<le> 1"
apply  (insert assms)
apply (metis HOST_State.distinct(167) HOST_State.distinct(267) HOST_State.distinct(305) HOST_State.distinct(35) HOST_State.distinct(75) HSTATE_general_rule_4_0 HSTATE_invariant3 aux_r77)
done
show goal538: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> length (dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])) \<le> 1 \<and> length (dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])) \<le> 1"
apply  (insert assms)
apply (metis HOST_State.distinct(169) HOST_State.distinct(269) HOST_State.distinct(307) HOST_State.distinct(37) HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 i1x i2x i609 nextGOPending_yes_reqresp_rule_6_1)
done
show goal539: "HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis HOST_State.distinct(167) HOST_State.distinct(267) HOST_State.distinct(305) HOST_State.distinct(35) HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 nextDTHDataFrom2_XYADGO1)
done
show goal540: "HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis HOST_State.distinct(167) HOST_State.distinct(267) HOST_State.distinct(305) HOST_State.distinct(35) HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 nextDTHDataFrom2_XYADGO1)
done
show goal541: "HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> length (dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])) \<le> 1 \<and> length (dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])) \<le> 1"
apply  (insert assms)
apply (metis HOST_State.distinct(135) HOST_State.distinct(165) HOST_State.distinct(265) HOST_State.distinct(303) HOST_State.distinct(33) HOST_State.distinct(375) HSTATE_general_rule_4_0 HSTATE_invariant3 aux_r77)
done
show goal542: "HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i717 nextDTHDataFrom1_XYADGO1 nextDTHDataFrom_IXADGO_invariant1 reqresps_empty_noGOPending1)
done
show goal543: "HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms dthdatas1_general_rule_3_0 i435 nextDTHDataFrom2_XYADGO1)
done
show goal544: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis HOST_State.distinct(115) HOST_State.distinct(169) HOST_State.distinct(269) HOST_State.distinct(289) HOST_State.distinct(307) HOST_State.distinct(37) HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) nextDTHDataFrom1_XYADGO1)
done
show goal545: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis HOST_State.distinct(169) HOST_State.distinct(269) HOST_State.distinct(307) HOST_State.distinct(37) HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) nextDTHDataFrom2_XYADGO1)
done
show goal546: "HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i719 nextDTHDataFrom1_XYADGO1 nextDTHDataFrom_IXADGO_invariant1 reqresps_empty_noGOPending1)
done
show goal547: "HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis HOST_State.distinct(165) HOST_State.distinct(265) HOST_State.distinct(303) HOST_State.distinct(33) HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) nextDTHDataFrom2_XYADGO1)
done
show goal548: "HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux2_r84 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i714 snps1_general_rule_6_0)
done
show goal549: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux2_r84 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i715 snps1_general_rule_6_0)
done
show goal550: "HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux2_r84 i716 snps1_general_rule_6_0)
done
show goal551: "HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i717 nextDTHDataFrom1_XYADGO1 nextDTHDataFrom_IXADGO_invariant1 reqresps_empty_noGOPending1)
done
show goal552: "HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis HOST_State.distinct(105) HOST_State.distinct(167) HOST_State.distinct(267) HOST_State.distinct(305) HOST_State.distinct(35) HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) nextDTHDataFrom2_XYADGO1)
done
show goal553: "HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r84)
done
show goal554: "HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant HOST_State.distinct(151) HOST_State.distinct(165) HOST_State.distinct(19) HOST_State.distinct(251) HOST_State.distinct(265) HOST_State.distinct(271) HOST_State.distinct(33) HSTATE_invariant3 HTDDataPending_htddatas_invariant1 IMADGO'_HSTATE MESI_State.distinct(329) MESI_State.distinct(349) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms aux_r77 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i182 i24 i782 i801 nextDTHDataFrom2_XYADGO1 nextDTHDataFrom_IXADGO_invariant1)
done
show goal555: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r84)
done
show goal556: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis HOST_State.distinct(139) HOST_State.distinct(169) HOST_State.distinct(269) HOST_State.distinct(307) HOST_State.distinct(37) HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i1x i2x i609 nextDTHDataFrom2_XYADGO1)
done
show goal557: "HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis HOST_State.distinct(167) HOST_State.distinct(267) HOST_State.distinct(305) HOST_State.distinct(35) HSTATE_XYADGO1 HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24))
done
show goal558: "HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> \<not> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis HOST_State.distinct(167) HOST_State.distinct(267) HOST_State.distinct(305) HOST_State.distinct(35) HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 nextGOPending_yes_reqresp_rule_6_1)
done
show goal559: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis HOST_State.distinct(169) HOST_State.distinct(269) HOST_State.distinct(307) HOST_State.distinct(37) HSTATE_XYADGO1 HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24))
done
show goal560: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> \<not> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis HOST_State.distinct(169) HOST_State.distinct(269) HOST_State.distinct(307) HOST_State.distinct(37) HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) nextGOPending_yes_reqresp_rule_6_1)
done
show goal561: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> lastSharer ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i656 nextGOPending_yes_reqresp_rule_6_1)
done
show goal562: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> lastSharer ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i656 nextGOPending_yes_reqresp_rule_6_1)
done
show goal563: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> lastSharer ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> (CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1)"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i656 nextGOPending_yes_reqresp_rule_6_1)
done
show goal564: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> lastSharer ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> (CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0)"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal565: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(265) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal566: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r84)
done
show goal567: "HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r84)
done
show goal568: "HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_HSTATE MESI_State.distinct(261) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i161 nextDTHDataFrom2_XYADGO1 nextDTHDataFrom_IXADGO_invariant1)
done
show goal569: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis HOST_State.distinct(149) HOST_State.distinct(17) HOST_State.distinct(249) HOST_State.distinct(271) HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 nextGOPending_yes_reqresp_rule_6_1)
done
show goal570: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis HOST_State.distinct(149) HOST_State.distinct(17) HOST_State.distinct(249) HOST_State.distinct(271) HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) nextGOPending_yes_reqresp_rule_6_1)
done
show goal571: "HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> (\<not> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> nextGOPendingIs GO_WritePullDrop ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> (\<not> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> nextGOPendingIs GO_WritePullDrop ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1)"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_disj1 HSTATE_general_rule_4_0 IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_HSTATE IMADGO'_nextGOPendingIs MESI_State.distinct(413) i737 nextGOPendingIs_XYADGO_agnostic1)
done
show goal572: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<longrightarrow> \<not> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant HOST_State.distinct(17) HOST_State.distinct(249) HOST_State.distinct(271) HSTATE_invariant3 IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(261) MESI_State.distinct(289) MESI_State.distinct(413) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms aux_r77 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i106 nextGOPending_yes_reqresp_rule_6_1)
done
show goal573: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<longrightarrow> \<not> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (smt (verit) aux2_r84)
done
show goal574: "HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(413) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i740 nextGOPending_yes_reqresp_rule_6_1)
done
show goal575: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1)"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(397) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal576: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0)"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal577: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> (CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1)"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i909 nextGOPending_yes_reqresp_rule_6_1)
done
show goal578: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> (CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0)"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal579: "HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i2x i487 i760 i94 nextReqIs_general_rule_6_0 reqresps_empty_noGOPending1 reqs1_empty_not_nextReqIs_general_invariant)
done
show goal580: "HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_HSTATE IMADGO'_nextReqIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i393 i909 nextGOPending_yes_reqresp_rule_6_1)
done
show goal581: "HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(229) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i747 nextGOPending_yes_reqresp_rule_6_1)
done
show goal582: "HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(229) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i748 nextGOPending_yes_reqresp_rule_6_1)
done
show goal583: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<longrightarrow> \<not> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant HOST_State.distinct(17) HOST_State.distinct(249) HOST_State.distinct(271) HSTATE_invariant3 IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(221) MESI_State.distinct(229) MESI_State.distinct(261) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms aux_r77 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i106 nextGOPending_yes_reqresp_rule_6_1)
done
show goal584: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<longrightarrow> \<not> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (smt (verit) aux2_r84)
done
show goal585: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> \<not> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(397) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal586: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(407) MESI_State.distinct(409) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal587: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> \<not> CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(397) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal588: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i742 nextGOPending_yes_reqresp_rule_6_1)
done
show goal589: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> (nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1))"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(397) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal590: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> (nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0))"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(331) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal591: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(397) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal592: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(405) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal593: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms empty_no_snoop2 i341 i465 nextGOPending_yes_reqresp_rule_6_1)
done
show goal594: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r84)
done
show goal595: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_HSTATE IMADGO'_nextGOPendingIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i761 nextDTHDataFrom2_XYADGO1 nextDTHDataFrom_IXADGO_invariant1)
done
show goal596: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (smt (verit) aux2_r84 reqresps_empty_noGOPendingIs1)
done
show goal597: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis HOST_State.distinct(169) HOST_State.distinct(269) HOST_State.distinct(307) HOST_State.distinct(37) HSTATE_XYADGO1 HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24))
done
show goal598: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> \<not> CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis HOST_State.distinct(169) HOST_State.distinct(269) HOST_State.distinct(307) HOST_State.distinct(37) HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) nextGOPending_yes_reqresp_rule_6_1)
done
show goal599: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis HOST_State.distinct(169) HOST_State.distinct(269) HOST_State.distinct(307) HOST_State.distinct(37) HSTATE_XYADGO1 HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24))
done
show goal600: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> \<not> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i766 nextGOPending_yes_reqresp_rule_6_1)
done
show goal601: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis HOST_State.distinct(139) HOST_State.distinct(169) HOST_State.distinct(247) HOST_State.distinct(269) HOST_State.distinct(307) HOST_State.distinct(37) HSTATE_XYADGO1 HSTATE_invariant3 aux_r77 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24))
done
show goal602: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> \<not> CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis HOST_State.distinct(169) HOST_State.distinct(269) HOST_State.distinct(307) HOST_State.distinct(37) HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) nextGOPending_yes_reqresp_rule_6_1)
done
show goal603: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis HOST_State.distinct(169) HOST_State.distinct(269) HOST_State.distinct(307) HOST_State.distinct(37) HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) nextGOPending_yes_reqresp_rule_6_1)
done
show goal604: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis HOST_State.distinct(169) HOST_State.distinct(269) HOST_State.distinct(307) HOST_State.distinct(37) HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) nextGOPending_yes_reqresp_rule_6_1)
done
show goal605: "HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i609 nextDTHDataFrom2_XYADGO1)
done
show goal606: "HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i609 nextDTHDataFrom2_XYADGO1)
done
show goal607: "HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r84)
done
show goal608: "HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i609 nextDTHDataFrom2_XYADGO1)
done
show goal609: "HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis HOST_State.distinct(13) HOST_State.distinct(145) HOST_State.distinct(225) HOST_State.distinct(229) HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) nextDTHDataFrom2_XYADGO1)
done
show goal610: "HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis HOST_State.distinct(13) HOST_State.distinct(145) HOST_State.distinct(225) HOST_State.distinct(229) HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) nextDTHDataFrom2_XYADGO1)
done
show goal611: "HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextReqIs RdShared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis C_msg_not_def IMADGO'_HSTATE IMADGO'_nextReqIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i25 nextGOPending_yes_reqresp_rule_6_1)
done
show goal612: "HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextReqIs RdShared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant MESI_State.distinct(299))
done
show goal613: "HSTATE SD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant IMADGO'_CSTATE_otherside IMADGO'_HSTATE MESI_State.distinct(397) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i742 nextGOPending_yes_reqresp_rule_6_1)
done
show goal614: "HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(397) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i742 nextGOPending_yes_reqresp_rule_6_1)
done
show goal615: "HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(397) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i742 nextGOPending_yes_reqresp_rule_6_1)
done
show goal616: "HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(397) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i742 nextGOPending_yes_reqresp_rule_6_1)
done
show goal617: "snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<and> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(397) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i742 nextGOPending_yes_reqresp_rule_6_1)
done
show goal618: "snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<and> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (smt (verit) aux2_r84)
done
show goal619: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (cases "dthdatas1 T")
apply  (auto)
apply (smt (verit) HSTATE_def i408)
apply (smt (verit) HSTATE_def i1x i2x i785 i891)
apply (smt (verit) HSTATE_def i1x i2x i785 i891)
apply (smt (verit) i1x i2x i435 i574 i99 list.discI)
apply (smt (verit) i56 list.distinct(1))
apply (smt (verit) i1x i2x i435 i574 i95 list.discI)
done
show goal620: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r84)
done
show goal621: "nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis HSTATE_XYADGO1 i2x i422 i786 i892 nextDTHDataFrom1_XYADGO1 reqresps_empty_noGOPending1)
done
show goal622: "nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_HSTATE IMADGO'_nextReqIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i393 i909 nextDTHDataFrom2_XYADGO1)
done
show goal623: "HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextSnpRespIs RspSFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis C_not_C_msg_def IMADGO'_CSTATE_otherside IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i337 nextGOPending_yes_reqresp_rule_6_1)
done
show goal624: "HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextSnpRespIs RspSFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(19) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal625: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal626: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(109) MESI_State.distinct(19) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal627: "HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i719 nextDTHDataFrom1_XYADGO1 nextDTHDataFrom_IXADGO_invariant1 reqresps_empty_noGOPending1)
done
show goal628: "HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis HOST_State.distinct(165) HOST_State.distinct(265) HOST_State.distinct(303) HOST_State.distinct(33) HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) nextDTHDataFrom2_XYADGO1)
done
show goal629: "HSTATE SA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis HSTATE_XYADGO1 IMADGO'_HSTATE IMADGO'_nextGOPendingIs aux2_r84 i795 nextGOPendingIs_XYADGO_agnostic1 reqresps_empty_noGOPendingIs1)
done
show goal630: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i656 nextGOPendingIs_XYADGO_agnostic1)
done
show goal631: "CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> HSTATE SA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(401) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal632: "CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> HSTATE SA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis HOST_State.distinct(11) HOST_State.distinct(143) HOST_State.distinct(201) HOST_State.distinct(205) HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 nextGOPending_yes_reqresp_rule_6_1)
done
show goal633: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<longrightarrow> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<or> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis IMADGO'_HSTATE SARspSFwdM_invariant1 \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> htddatas1_general_rule_5_0 i2x i343 nextSnpRespIs_general_rule_6_0 nextSnpRespIs_property1 reqresps_empty_noGOPending1)
done
show goal634: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<longrightarrow> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<or> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (smt (verit) aux2_r84)
done
show goal635: "HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis HOST_State.distinct(165) HOST_State.distinct(265) HOST_State.distinct(303) HOST_State.distinct(33) HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) nextGOPending_yes_reqresp_rule_6_1)
done
show goal636: "HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis HOST_State.distinct(165) HOST_State.distinct(265) HOST_State.distinct(303) HOST_State.distinct(33) HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) nextDTHDataFrom1_XYADGO1)
done
show goal637: "HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis HOST_State.distinct(165) HOST_State.distinct(265) HOST_State.distinct(303) HOST_State.distinct(33) HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 nextDTHDataFrom2_XYADGO1)
done
show goal638: "HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis HOST_State.distinct(165) HOST_State.distinct(265) HOST_State.distinct(303) HOST_State.distinct(33) HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) nextGOPending_yes_reqresp_rule_6_1)
done
show goal639: "HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis HOST_State.distinct(165) HOST_State.distinct(265) HOST_State.distinct(303) HOST_State.distinct(33) HSTATE_XYADGO1 HSTATE_invariant3 aux_r77 hstate_invariants(2))
done
show goal640: "HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis HOST_State.distinct(165) HOST_State.distinct(225) HOST_State.distinct(265) HOST_State.distinct(303) HOST_State.distinct(33) HSTATE_XYADGO1 HSTATE_invariant3 aux_r77)
done
show goal641: "HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis HOST_State.distinct(165) HOST_State.distinct(229) HOST_State.distinct(265) HOST_State.distinct(285) HSTATE_XYADGO1 HSTATE_invariant3 IMADGO'_HSTATE IMADGO'_nextGOPendingIs aux2_r84 aux_r77 i313 i421 nextDTHDataFrom2_XYADGO1 reqresps_empty_noGOPendingIs1)
done
show goal642: "HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis HOST_State.distinct(165) HOST_State.distinct(265) HOST_State.distinct(303) HOST_State.distinct(33) HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) nextGOPending_yes_reqresp_rule_6_1)
done
show goal643: "HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_HSTATE IMADGO'_nextReqIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i810 nextDTHDataFrom2_XYADGO1 nextDTHDataFrom_IXADGO_invariant1)
done
show goal644: "HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis IMADGO'_HSTATE IMADGO'_nextReqIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i811 nextDTHDataFrom2_XYADGO1 nextDTHDataFrom_IXADGO_invariant1)
done
show goal645: "HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(229) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i812 nextGOPending_yes_reqresp_rule_6_1)
done
show goal646: "CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (smt (verit) aux2_r84 reqresps_empty_noGOPendingIs1)
done
show goal647: "CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(401))
done
show goal648: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_HSTATE IMADGO'_nextReqIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i815 nextDTHDataFrom2_XYADGO1 nextDTHDataFrom_IXADGO_invariant1)
done
show goal649: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_HSTATE IMADGO'_nextReqIs MESI_State.distinct(343) MESI_State.distinct(355) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i453 i769 nextDTHDataFrom2_XYADGO1)
done
show goal650: "HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis HSTATE_XYADGO1 i2x i717 nextDTHDataFrom1_XYADGO1 reqresps_empty_noGOPending1)
done
show goal651: "HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis HSTATE_XYADGO1 IMADGO'_HSTATE IMADGO'_nextGOPendingIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux2_r84 i818 nextDTHDataFrom2_XYADGO1 reqresps_empty_noGOPendingIs1)
done
show goal652: "HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis HOST_State.distinct(167) HOST_State.distinct(267) HOST_State.distinct(305) HOST_State.distinct(35) HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) nextDTHDataFrom2_XYADGO1)
done
show goal653: "HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis HOST_State.distinct(167) HOST_State.distinct(267) HOST_State.distinct(305) HOST_State.distinct(35) HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) nextDTHDataFrom2_XYADGO1)
done
show goal654: "HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i609 nextDTHDataFrom2_XYADGO1)
done
show goal655: "HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i609 nextDTHDataFrom2_XYADGO1)
done
show goal656: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant IMADGO'_nextReqIs MESI_State.distinct(19) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextReqIs_general_rule_6_0)
done
show goal657: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis C_not_C_msg_def IMADGO'_CSTATE_otherside IMADGO'_nextReqIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i337 nextGOPending_yes_reqresp_rule_6_1)
done
show goal658: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal659: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(191) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal660: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> (CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1)"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal661: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> (CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0)"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal662: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1)"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal663: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0)"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal664: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> (CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1)"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal665: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> (CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0)"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal666: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1)"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_nextHTDDataPending MESI_State.distinct(109) MESI_State.distinct(229) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i833 nextGOPending_DeviceIMADGO nextGOPending_yes_reqresp_rule_6_1)
done
show goal667: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0)"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal668: "HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r84)
done
show goal669: "HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i836 nextDTHDataFrom2_XYADGO1 nextDTHDataFrom_IXADGO_invariant1 snps1_general_rule_6_0)
done
show goal670: "HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(397) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextDTHDataFrom1_XYADGO1)
done
show goal671: "HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i742 nextDTHDataFrom2_XYADGO1)
done
show goal672: "HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(413) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i839 nextDTHDataFrom2_XYADGO1 nextDTHDataFrom_IXADGO_invariant1)
done
show goal673: "HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> \<not> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(413) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i840 nextDTHDataFrom2_XYADGO1 nextDTHDataFrom_IXADGO_invariant1)
done
show goal674: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> (htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<or> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1)"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(19) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal675: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> (htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<or> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0)"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms empty_no_snoop2 i341 i465 nextGOPending_yes_reqresp_rule_6_1)
done
show goal676: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(19) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal677: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(405) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal678: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(19) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal679: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r84)
done
show goal680: "CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> (CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1)"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal681: "CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> (CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0)"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal682: "CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal683: "CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(109) MESI_State.distinct(229) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal684: "CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal685: "CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms empty_no_snoop_variant2 i341 i465 nextGOPending_yes_reqresp_rule_6_1)
done
show goal686: "CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal687: "CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(361) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal688: "CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(151) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> snps1_general_rule_6_0)
done
show goal689: "CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r84)
done
show goal690: "HSTATE SD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis HOST_State.distinct(141) HOST_State.distinct(175) HOST_State.distinct(179) HOST_State.distinct(9) HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 nextDTHDataFrom2_XYADGO1)
done
show goal691: "HSTATE SD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis HOST_State.distinct(141) HOST_State.distinct(175) HOST_State.distinct(179) HOST_State.distinct(9) HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) nextDTHDataFrom2_XYADGO1)
done
show goal692: "HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis HSTATE_XYADGO1 IMADGO'_HSTATE IMADGO'_nextGOPendingIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux2_r84 i859 nextGOPendingIs_XYADGO_agnostic1 reqresps_empty_noGOPendingIs1)
done
show goal693: "HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(397) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i742 nextDTHDataFrom2_XYADGO1)
done
show goal694: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal695: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i909 nextGOPending_yes_reqresp_rule_6_1)
done
show goal696: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal697: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_nextReqIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i909 nextGOPending_yes_reqresp_rule_6_1)
done
show goal698: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal699: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_sameside IMADGO'_nextHTDDataPending \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms empty_no_snoop_variant2 i341 i465 nextGOPending_yes_reqresp_rule_6_1)
done
show goal700: "CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (smt (verit) aux2_r84 reqresps_empty_noGOPendingIs1)
done
show goal701: "CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_HSTATE IMADGO'_nextGOPendingIs IMADGO'_nextReqIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i868 nextGOPendingIs_XYADGO_agnostic1)
done
show goal702: "CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i742 nextGOPendingIs_XYADGO_agnostic1)
done
show goal703: "CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(397) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPendingIs_XYADGO_agnostic1)
done
show goal704: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i666 nextReqIs_general_rule_6_0)
done
show goal705: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i574 nextGOPending_yes_reqresp_rule_6_1)
done
show goal706: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> (\<not> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> nextGOPendingIs GO_WritePullDrop ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> (\<not> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> nextGOPendingIs GO_WritePullDrop ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1)"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i666 nextGOPendingIs_XYADGO_agnostic1)
done
show goal707: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextSnpRespIs RspIFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (smt (verit) aux1162)
done
show goal708: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextSnpRespIs RspIFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis HOST_State.distinct(149) HOST_State.distinct(17) HOST_State.distinct(249) HOST_State.distinct(271) HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 nextGOPending_yes_reqresp_rule_6_1)
done
show goal709: "length (dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])) \<le> 1"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_sameside \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms bot_nat_0.extremum dthdatas1_general_rule_3_0 i435 list.size(3) nextGOPending_yes_reqresp_rule_6_1)
done
show goal710: "length (dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])) \<le> 1"
apply  (cases "dthdatas1 T")
apply  (auto)
apply (smt (verit) One_nat_def i884)
apply (smt (verit) One_nat_def i884)
done
show goal711: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (smt (verit) aux2_r84 reqresps_empty_noGOPendingIs1)
done
show goal712: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_HSTATE IMADGO'_nextGOPendingIs IMADGO'_nextReqIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i886 nextGOPendingIs_XYADGO_agnostic1)
done
show goal713: "HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(109) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i887 nextDTHDataFrom2_XYADGO1 nextDTHDataFrom_IXADGO_invariant1)
done
show goal714: "HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(109) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i888 nextDTHDataFrom2_XYADGO1 nextDTHDataFrom_IXADGO_invariant1)
done
show goal715: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<longrightarrow> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant HOST_State.distinct(17) HOST_State.distinct(249) HOST_State.distinct(271) HSTATE_invariant3 IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(101) MESI_State.distinct(109) MESI_State.distinct(261) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms aux_r77 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i106 nextGOPending_yes_reqresp_rule_6_1)
done
show goal716: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [] \<longrightarrow> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (smt (verit) aux2_r84)
done
show goal717: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal718: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r84)
done
show goal719: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> (htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<or> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1)"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal720: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> (htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<or> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0)"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms empty_no_snoop2 i341 i465 nextGOPending_yes_reqresp_rule_6_1)
done
show goal721: "CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> (htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<or> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1)"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal722: "CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> (htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<or> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0)"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms empty_no_snoop2 i341 i465 nextGOPending_yes_reqresp_rule_6_1)
done
show goal723: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_sameside IXADGO_dthdatas1_invariant \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms dthdatas1_general_rule_3_0 i435)
done
show goal724: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms empty_no_snoop2 i341 i465 nextGOPending_yes_reqresp_rule_6_1)
done
show goal725: "nextSnpRespIs RspIHitSE ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant IMADGO'_nextSnpRespIs MESI_State.distinct(361) MESI_State.distinct(407) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextSnpRespIs_general_rule_6_0)
done
show goal726: "nextSnpRespIs RspIHitSE ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_nextSnpRespIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i900 nextGOPending_yes_reqresp_rule_6_1)
done
show goal727: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i909 nextGOPending_yes_reqresp_rule_6_1)
done
show goal728: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(405) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal729: "CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(409) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal730: "CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(405) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal731: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal732: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(405) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal733: "CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal734: "CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(405) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal735: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal736: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(405) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal737: "HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant IMADGO'_HSTATE MESI_State.distinct(405) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextDTHDataFrom1_XYADGO1)
done
show goal738: "HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i909 nextDTHDataFrom2_XYADGO1)
done
show goal739: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal740: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(405) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal741: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> \<not> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i666 nextGOPending_yes_reqresp_rule_6_1)
done
show goal742: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> \<not> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis HOST_State.distinct(169) HOST_State.distinct(269) HOST_State.distinct(307) HOST_State.distinct(37) HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) nextGOPending_yes_reqresp_rule_6_1)
done
show goal743: "HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> \<not> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i609 nextGOPending_yes_reqresp_rule_6_1)
done
show goal744: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextSnpRespIs RspIHitSE ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis IMADGO'_HSTATE IMADGO'_nextReqIs IMADGO'_nextSnpRespIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i918 nextSnpRespIs_general_rule_6_0)
done
show goal745: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextSnpRespIs RspIHitSE ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_HSTATE IMADGO'_nextReqIs IMADGO'_nextSnpRespIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i919 nextGOPending_yes_reqresp_rule_6_1)
done
show goal746: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(19) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal747: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms empty_no_snoop_variant2 i341 i465 nextGOPending_yes_reqresp_rule_6_1)
done
show goal748: "HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux2_r84 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i922 snps1_general_rule_6_0)
done
show goal749: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_nextSnoopIs MESI_State.distinct(405) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal750: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r84 empty_no_snoop2)
done
show goal751: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextSnpRespIs RspIFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (smt (verit) aux1162)
done
show goal752: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextSnpRespIs RspIFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant IMADGO'_HSTATE MESI_State.distinct(405) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal753: "CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> HSTATE SA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis C_not_C_msg_def IMADGO'_CSTATE_otherside IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i337 nextGOPending_yes_reqresp_rule_6_1)
done
show goal754: "CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> HSTATE SA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_sameside IMADGO'_HSTATE MESI_State.distinct(19) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> nextGOPending_yes_reqresp_rule_6_1)
done
show goal755: "CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_assign_rule_4 CSTATE_inequality_invariant IMADGO'_CSTATE_sameside MESI_State.distinct(417) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal756: "CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_nextHTDDataPending \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i930 nextGOPending_yes_reqresp_rule_6_1)
done
show goal757: "CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPendingState Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal758: "CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPendingState Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = [] \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (cases "dthdatas1 T")
apply  (auto)
apply (smt (verit) i56 nextReqRespStateIs.simps(1))
apply (smt (verit) i118 nextReqRespStateIs.simps(1))
apply (smt (verit) CSTATE_various_forms6 i930 nextHTDDataPending_various_forms2)
apply (smt (verit) i56 nextReqRespStateIs.simps(1))
apply (smt (verit) i118 nextReqRespStateIs.simps(1))
apply (smt (verit) i101 i1x i2x i435 list.discI)
done
show goal759: "(CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPendingState Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> (CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal760: "(CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPendingState Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> (CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_HSTATE IMADGO'_nextHTDDataPending MESI_State.distinct(15) MESI_State.distinct(329) MESI_State.distinct(339) MESI_State.distinct(349) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i934 nextGOPending_DeviceIMADGO nextGOPending_overlooked_reqresp_rule_6_0)
done
show goal761: "(CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPendingState Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> []"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal762: "(CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPendingState Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> []"
apply  (insert assms)
apply (metis IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i891 nextGOPending_DeviceIMADGO nextGOPending_overlooked_reqresp_rule_6_0 reqresps_empty_noGOPending2)
done
show goal763: "(CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPendingState Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal764: "(CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPendingState Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_otherside_rule_4_0 HOST_State.distinct(149) HOST_State.distinct(17) HOST_State.distinct(249) HOST_State.distinct(271) HSTATE_invariant4 aux_r77 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i147 i1x i2x i909 i937 nextGOPending_overlooked_reqresp_rule_6_0 nextGOPending_yes_reqresp_rule_6_1 xyad_go_invariant2)
done
show goal765: "CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPendingState Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal766: "CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPendingState Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) aux2_r84)
done
show goal767: "CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPendingState Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> reqs1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (smt (verit) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
done
show goal768: "CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPendingState Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> reqs2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []"
apply  (insert assms)
apply (metis \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i95 nextGOPending_DeviceIMADGO nextGOPending_overlooked_reqresp_rule_6_0 reqresps_empty_noGOPending2 reqs2_IMADGO)
done
show goal769: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextSnpRespIs RspIFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (smt (verit) aux1162)
done
show goal770: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextSnpRespIs RspIFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis HOST_State.distinct(149) HOST_State.distinct(17) HOST_State.distinct(249) HOST_State.distinct(271) HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) nextGOPending_yes_reqresp_rule_6_1)
done
show goal771: "HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis HOST_State.distinct(167) HOST_State.distinct(267) HOST_State.distinct(305) HOST_State.distinct(35) HSTATE_invariant3 IMADGO'_HSTATE \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> aux_r77 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) nextGOPending_yes_reqresp_rule_6_1)
done
show goal772: "nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (metis CSTATE_inequality_invariant IMADGO'_nextReqIs MESI_State.distinct(359) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> assms i946 nextReqIs_general_rule_6_0)
done
show goal773: "nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_CSTATE_otherside IMADGO'_nextReqIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i947 nextGOPending_yes_reqresp_rule_6_1)
done
show goal774: "nextSnpRespIs RspIHitSE ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis IMADGO'_nextSnpRespIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i948 nextDTHDataFrom_IXADGO_invariant1 nextSnpRespIs_general_rule_6_0)
done
show goal775: "nextSnpRespIs RspIHitSE ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
apply  (insert assms)
apply (metis IMADGO'_nextSnpRespIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i949 nextDTHDataFrom2_XYADGO1 nextDTHDataFrom_IXADGO_invariant1)
done
show goal776: "nextSnpRespIs RspIFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply  (insert assms)
apply (smt (verit) aux1162)
done
show goal777: "nextSnpRespIs RspIFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  (insert assms)
apply (metis IMADGO'_nextReqIs IMADGO'_nextSnpRespIs \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close> i951 nextGOPending_yes_reqresp_rule_6_1)
done
show goal778: "(CSTATE SMA ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextSnoopIs SnpData ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> HSTATE SAD ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])) "
by (smt (verit) \<open>\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0\<close>)
show goal779: "(CSTATE SMA ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextSnoopIs SnpData ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> HSTATE SAD ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])) "
by (metis IMADGO'_CSTATE_otherside IMADGO'_HSTATE IMADGO'_nextSnoopIs i953 nextGOPending_DeviceIMADGO)
show goal780: "((CSTATE SIA ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPendingIs GO_WritePullDrop ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> HSTATE ModifiedM ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> CSTATE Modified ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE MIA ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> (CSTATE IMAD ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMAD ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> nextHTDDataPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or>(CSTATE IMA ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMA ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> nextGOPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> (CSTATE IMD ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMD ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> nextHTDDataPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) "
by (metis CSTATE_assign_rule_4 CSTATE_different1 MESI_State.distinct(413))
show goal781: "((CSTATE SIA ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPendingIs GO_WritePullDrop ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> HSTATE ModifiedM ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> CSTATE Modified ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE MIA ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> (CSTATE IMAD ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMAD ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> nextHTDDataPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or>(CSTATE IMA ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMA ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> nextGOPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> (CSTATE IMD ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMD ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> nextHTDDataPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0)   "
by (metis CSTATE_different1 IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_HSTATE IMADGO'_nextGOPendingIs MESI_State.distinct(329) MESI_State.distinct(339) MESI_State.simps(16) MESI_State.simps(350) i1x i955 xyad_go_invariant2)
show goal782: "((CSTATE SIAC ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPendingIs GO ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPendingState Invalid ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE IIA ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> GTS ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> HSTATE ModifiedM ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> CSTATE Modified ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE MIA ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> (CSTATE IMAD ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMAD ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> nextHTDDataPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or>(CSTATE IMA ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMA ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> nextGOPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> (CSTATE IMD ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMD ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> nextHTDDataPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) "
by (smt (verit) aux2_r84 reqresps_empty_noGOPendingIs1)
show goal783: "((CSTATE SIAC ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPendingIs GO ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPendingState Invalid ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> \<not> CSTATE IIA ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> GTS ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> HSTATE ModifiedM ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> CSTATE Modified ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE MIA ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> (CSTATE IMAD ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMAD ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> nextHTDDataPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or>(CSTATE IMA ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMA ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> nextGOPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> (CSTATE IMD ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMD ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> nextHTDDataPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0)   "
apply simp
by (metis CSTATE_disj4' CSTATE_various_forms1 CSTATE_various_forms5 HSTATE_various_forms2 HTDDataPending_htddatas_invariant1 MESI_State.distinct(107) MESI_State.distinct(27) MESI_State.distinct(329) MESI_State.distinct(339) MESI_State.distinct(349) One_nat_def i1x i2x i489 i934 nat.simps(3) nextGOPendingState_def nextGOPending_various_forms4 reqresps_empty_noGOPending1)
show goal784: "((CSTATE SIAC ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPendingIs GO ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPendingState Invalid ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE IIA ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> GTS ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> HSTATE MD ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> dthdatas1 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> []) "
by (smt (verit) aux2_r84 reqresps_empty_noGOPendingIs1)
show goal785: "((CSTATE SIAC ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPendingIs GO ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPendingState Invalid ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> \<not> CSTATE IIA ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> GTS ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> HSTATE MD ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> dthdatas2 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<noteq> [])  "
apply simp
by (metis HSTATE_various_forms2 i1x i2x i891 nextReqRespStateIs.simps(1))
show goal786: "((CSTATE SIAC ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPendingIs GO ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPendingState Invalid ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE IIA ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> GTS ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> HSTATE MA ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> ((CSTATE IMAD ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMAD ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) \<and> nextHTDDataPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE IMA ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> CSTATE SMA ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1)) "
by simp
show goal787: "((CSTATE SIAC ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPendingIs GO ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPendingState Invalid ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> \<not> CSTATE IIA ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> GTS ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> HSTATE MA ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> ((CSTATE IMAD ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMAD ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) \<and> nextHTDDataPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE IMA ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> CSTATE SMA ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0)) "
apply simp
by (smt (verit) HOST_State.distinct(149) HOST_State.distinct(17) HOST_State.distinct(249) HOST_State.distinct(271) HSTATE_def aux_r77)
show goal788: "(HSTATE SD ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 0 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> snps2 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []) "
by (smt (verit) aux2_r84)
show goal789: "(HSTATE SD ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 1 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> snps1 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []) "
by (metis IMADGO'_HSTATE i963 nextDTHDataFrom2_XYADGO1 snps1_general_rule_6_0)
show goal790: "(HSTATE SD ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 0 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> reqresps1 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []) "
by (smt (verit) aux2_r84)
show goal791: "(HSTATE SD ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 1 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> reqresps2 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) = []) "
apply simp
by (smt (verit) HSTATE_various_forms2 i1x i2x i436 i965 nextDTHDataFrom_def)
show goal792: "(HSTATE ID ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 0 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> (\<not> CSTATE SIA ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> nextGOPendingIs GO_WritePullDrop ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) ) "
by (metis IMADGO'_CSTATE_sameside goal443)
show goal793: "(HSTATE ID ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 1 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> (\<not> CSTATE SIA ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> nextGOPendingIs GO_WritePullDrop ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0) ) "
by (metis IMADGO'_CSTATE_sameside IMADGO'_HSTATE goal180 goal443)
show goal794: "(CSTATE MIA ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> nextGOPendingIs GO_WritePull ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> HSTATE ID ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> (\<not> CSTATE SIA ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<or> nextGOPendingIs GO_WritePullDrop ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1)) "
by (metis IMADGO'_CSTATE_sameside IMADGO'_HSTATE goal174 goal443)
show goal795: "(CSTATE MIA ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> nextGOPendingIs GO_WritePull ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<and> HSTATE ID ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> (\<not> CSTATE SIA ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<or> nextGOPendingIs GO_WritePullDrop ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0))  "
by (metis IMADGO'_CSTATE_sameside IMADGO'_HSTATE goal174 goal443)
show goal796: "(HSTATE SAD ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextDTHDataFrom 1 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<longrightarrow> \<not> CSTATE MIA ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<and> \<not> CSTATE MIA ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1) "
by (metis CSTATE_disj1 IMADGO'_CSTATE_otherside IMADGO'_CSTATE_sameside IMADGO'_HSTATE assms goal150 hstate_invariants(2) i106 i742 i970 nextDTHDataFrom_IXADGO_invariant1)
qed
qed
lemma IMADGO_SWMR_shape: "P T \<Longrightarrow>
 (\<And>T m. P T \<and> CSTATE IMAD T 0 \<and> nextGOPending T 0 \<Longrightarrow>
   P ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])) \<Longrightarrow>
 Lall
  (if CSTATE IMAD T 0 \<and> nextGOPending T 0
   then [let m = nextGO T 0; devid = nat_to_id 0
   in if 0 = 0 then  T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ] else  T\<lparr>buffer2 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]]
   else [])
  P"
by simp
lemma IMADGO_coherent: shows "
SWMR_state_machine T \<Longrightarrow> Lall (IMADGO' T 0) SWMR_state_machine
"
unfolding IMADGO'_def consumeGO_def
apply(insert IMADGO'_coherent_aux_simpler)
by (metis IMADGO'_CSTATE_sameside IMADGO_SWMR_shape Lall.simps(1) Lall.simps(2) consumeGO_def hstate_invariants(2))
end