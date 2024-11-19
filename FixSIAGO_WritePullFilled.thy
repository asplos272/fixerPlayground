
theory FixSIAGO_WritePullFilled imports  BaseProof.BasicInvariants  begin
sledgehammer_params[timeout=10, dont_minimize, "try0" = false]
lemma snps2_SIAGO_WritePull: shows "snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = snps2 T"
apply(case_tac "program1 T")
by simp+
lemma snps1_SIAGO_WritePull: shows "snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = snps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqs2_SIAGO_WritePull: shows "reqs2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = reqs2 T"
apply(case_tac "program1 T")
by simp+
lemma reqs1_SIAGO_WritePull: shows "reqs1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = reqs1 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps2_SIAGO_WritePull: shows "snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = snpresps2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps1_SIAGO_WritePull: shows "snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = snpresps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps2_SIAGO_WritePull: shows "reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = reqresps2 T"
apply(case_tac "program1 T")
by simp+
lemma dthdatas2_SIAGO_WritePull: shows "dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = dthdatas2 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas1_SIAGO_WritePull: shows "htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = htddatas1 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas2_SIAGO_WritePull: shows "htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = htddatas2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_SIAGO_WritePull_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma reqresps1_SIAGO_WritePull_aux1: shows "reqresps1 T = reqresps1 (T [ Dev1 +=d2hd dthd] [ -=i 0])"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_SIAGO_WritePull: assumes "length (reqresps1 T) \<le> 1" shows "reqresps1  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
proof -
have half_same: " (reqresps1  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid])) = reqresps1 T"
by simp
have quarter_reduce: "reqresps1 (T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ]) = []"
proof -
have half_l1: "length (reqresps1  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] )) \<le> 1"
using assms half_same
by presburger
show ?thesis
using half_l1 reqresps1_SIAGO_WritePull_aux
by presburger
qed
have quarter_same: "reqresps1  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ]) = reqresps1  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
using reqresps1_SIAGO_WritePull_aux1
by blast
show ?thesis
using quarter_reduce quarter_same
by presburger
qed
lemma nextEvict_SIAGO_WritePull_CSTATE_invariant: shows "nextEvict T 0 \<Longrightarrow> CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])  0"
apply(case_tac "program1 T") apply simp+ done
lemma nextEvict_SIAGO_WritePull_invariant: shows"nextEvict T 0 = nextEvict ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] ) 0"
by simp
lemma HSTATE_SIAGO_WritePull_invariant: shows "HSTATE X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = 
  HSTATE X T"
apply(case_tac "program1 T")
by simp+
lemma CSTATE_SIAGO_WritePull_IMAD_invariant: shows "  CSTATE Invalid (T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd]) 0"
by simp
lemma CSTATE_SIAGO_WritePull_Invalid: shows " CSTATE Invalid (T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd]) 0"
using nextEvict_SIAGO_WritePull_CSTATE_invariant nextEvict_SIAGO_WritePull_invariant
using CSTATE_SIAGO_WritePull_IMAD_invariant
by presburger
lemma nextReqIs_SIAGO_WritePull_IMAD_invariant2: shows 
  "nextReqIs X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 = nextReqIs X T 1"
apply(case_tac "program1 T")
by simp+
lemma nextReqIs_SIAGO_WritePull_IMAD_invariant1: shows 
  "nextReqIs X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 = nextReqIs X T 0"
apply(case_tac "program1 T")
by simp+
lemma CSTATE_SIAGO_WritePull_otherside_invariant2: shows
" CSTATE X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 = CSTATE X T 1"
apply(case_tac "program1 T")
by simp+
lemma SIAGO_WritePull_nextGOPendingIs_otherside: shows 
"nextGOPendingIs X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 = nextGOPendingIs X T 1"
apply(case_tac "program1 T")
by simp+
lemma SIAGO_WritePull_nextEvict_otherside: shows 
"nextEvict  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 = nextEvict T 1"
apply(case_tac "program1 T")
by simp+
lemma SIAGO_WritePull_nextHTDDataPending_otherside: shows 
"nextDTHDataPending  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 = nextDTHDataPending T 1"
apply(case_tac "program1 T") apply  simp+ done
lemma SIAGO_WritePull_nextHTDDataPending_real: shows 
"nextHTDDataPending  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) i = nextHTDDataPending T i"
apply(case_tac "program1 T") apply  simp+ done
lemma SIAGO_WritePull_nextSnpRespIs_otherside: shows 
"nextSnpRespIs X  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 = nextSnpRespIs X T 1"
apply(case_tac "program1 T")
by simp+
lemma SIAGO_WritePull_nextHTDDataPending_sameside: shows 
"nextDTHDataPending  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 = nextDTHDataPending T 1"
apply(case_tac "program1 T")
by simp+
lemma SIAGO_WritePull_nextSnpRespIs_sameside: shows 
"nextSnpRespIs X  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 = nextSnpRespIs X T 0"
apply(case_tac "program1 T") apply  simp+ done
lemma SIAGO_WritePull_HSTATE: shows "HSTATE X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = 
  HSTATE X T"
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
lemma reqresps1_HostModifiedRdShared_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma reqresps1_HostModifiedRdShared_aux1: shows "reqresps1 T = reqresps1 (T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid])"
by simp
lemma SIAGO_WritePull_reqresps1_empty: shows 
  "length (reqresps1 T ) \<le> 1 \<Longrightarrow> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
using reqresps1_SIAGO_WritePull
by presburger
lemma SIAGO_WritePull_CSTATE_aux: shows "CSTATE X T 0 = CSTATE X ( T [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply(case_tac "program1 T")
by simp+
lemma dthdatas1_perform_instr: shows "dthdatas1 T = dthdatas1 (T [ -=i m])"
apply(case_tac m)
apply(case_tac "program1 T")
apply simp
apply simp
apply(case_tac "program2 T") apply simp+ done

  
\<comment>\<open>_params[minimize=true,preplay_timeout=50,timeout=200]
\<close>
lemma nextGOPending_DeviceSIAGO_WritePull: "nextGOPending (  T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0] ) 1 = nextGOPending T 1"
by (metis nextGOPending_def option.inject reqresps2_SIAGO_WritePull reqresps2_remove_op zero_neq_one)
lemma nextLoad_DeviceSIAGO_WritePull: "nextLoad (  T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0] ) 1 = nextLoad T 1"
apply(case_tac "program1 T") apply simp+ done
lemma SIAGO_WritePull'_coherent_aux_simpler: assumes "SWMR_state_machine T \<and> CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePull T 0"
  shows "SWMR_state_machine  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
proof -
have i0: "SWMR T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i1x: "CSTATE SIA T 0"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i2x: "nextGOPendingIs GO_WritePull T 0"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i3: "C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i4: "H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i5: "H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i6: "C_msg_P_oppo ISAD nextGOPending (\<lambda>T i. \<not> CSTATE Modified T i) T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i10: "H_msg_P_same SharedM (nextReqIs RdShared) (\<lambda>T i. \<not> CSTATE Modified T i) T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i11: "H_msg_P_oppo SharedM (nextReqIs RdShared) (\<lambda>T i. \<not> CSTATE Modified T i) T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i12: "H_msg_P_same ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> CSTATE Modified T i) T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i13: "H_msg_P_oppo ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> nextDTHDataPending T i) T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i14: "H_msg_P_oppo ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> nextSnpRespIs RspIFwdM T i) T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i15: "H_msg_P_same ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> nextSnpRespIs RspIFwdM T i) T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i16: "C_H_state IMAD (nextReqIs RdOwn) Modified SD T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i17: "C_H_state IMAD (nextReqIs RdOwn) Modified SAD T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i18: "C_H_state IMAD (nextReqIs RdOwn) Modified SA T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i19: "C_H_state Invalid nextStore Modified SAD T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i20: "C_H_state Invalid nextStore Modified SA T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i21: "C_H_state Invalid nextStore Modified SD T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i22: "HSTATE SharedM T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i23: "HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i24: "HSTATE MD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i25: "C_msg_not RdShared IMAD T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i26: "C_msg_not RdShared Invalid T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i27: "H_msg_P_same ModifiedM (nextReqIs DirtyEvict) (\<lambda>T i. CSTATE MIA T i \<or> CSTATE IIA T i) T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i28: "C_msg_P_host MIA (nextGOPendingIs GO_WritePull) (\<lambda>T. \<not> HSTATE ModifiedM T) T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i29: "C_msg_P_same MIA (nextGOPendingIs GO_WritePull) nextEvict T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i30: "C_msg_P_host MIA (nextGOPendingIs GO_WritePull) (HSTATE ID) T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i31: "C_state_not MIA RdShared T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i32: "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) nextEvict T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i34: "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextReqIs RdShared T i) T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i35: "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextDTHDataPending T i) T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i36: "H_C_state_msg_same ModifiedM Modified (\<lambda>T i. \<not> nextReqIs RdShared T i) T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i37: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) nextEvict T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i39: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextReqIs RdShared T i) T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i40: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextDTHDataPending T i) T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i41: "H_C_state_msg_oppo ModifiedM IIA (\<lambda>T i. \<not> nextReqIs RdShared T i) T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i46: "C_msg_P_host Shared (nextSnoopIs SnpInv) (HSTATE MA) T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i47: "C_msg_state RdShared ISAD T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i49: "C_not_C_msg Modified ISAD nextGOPending T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i50: "C_msg_P_same Invalid nextStore (\<lambda>T i. \<not> nextHTDDataPending T i) T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i51: "C_msg_P_same Invalid nextStore (\<lambda>T i. \<not> nextSnoopIs SnpInv T i) T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i52: "C_msg_P_same ISAD nextGOPending (\<lambda>T i. \<not> nextReqIs RdShared T i) T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i55: "snps2 T \<noteq> [] \<longrightarrow> reqs1 T = [] \<and> snpresps2 T = [] \<and> dthdatas2 T = [] \<and> reqresps1 T = []"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i56: "snps1 T \<noteq> [] \<longrightarrow> reqs2 T = [] \<and> snpresps1 T = [] \<and> dthdatas1 T = [] \<and> reqresps2 T = []"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i57: "length (reqs1 T) \<le> 1"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i58: "length (reqs2 T) \<le> 1"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i59: "C_msg_P_same Shared (nextSnoopIs SnpInv) (\<lambda>T i. \<not> nextHTDDataPending T i) T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i60: "length (snps2 T) \<le> 1"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i61: "length (snps1 T) \<le> 1"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i611old: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) (\<lambda> T i. \<not>nextSnoopPending T i) T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i612old: "C_msg_P_oppo Invalid nextStore (\<lambda>T i. \<not> nextSnoopPending T i) T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i613old: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i614old: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i615old: "(CSTATE Shared T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i616old: "(CSTATE Shared T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i617old: "(CSTATE IIA T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> htddatas1 T = [])"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i618old: "(CSTATE IIA T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> htddatas2 T = [])"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i68: "CSTATE Invalid T 0 \<longrightarrow> reqs1 T = []"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i69: "CSTATE Invalid T 1 \<longrightarrow> reqs2 T = []"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i70: "CSTATE Shared T 0 \<longrightarrow> reqs1 T = []"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i71: "CSTATE Shared T 1 \<longrightarrow> reqs2 T = []"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i72: "CSTATE Modified T 0 \<longrightarrow> \<not>CSTATE Modified T 1"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i73: "CSTATE Modified T 1 \<longrightarrow> \<not>CSTATE Modified T 0"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i74: "CSTATE ISD T 0 \<longrightarrow> \<not>HSTATE ModifiedM T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i75: "CSTATE ISD T 1 \<longrightarrow> \<not>HSTATE ModifiedM T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i76: "C_msg_P_host ISD (nextSnoopIs SnpInv) (HSTATE MA) T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i77: "length (htddatas1 T) \<le> 1"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i78: "length (htddatas2 T) \<le> 1"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i79: "CSTATE ISD T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = []"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i80: "CSTATE ISD T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = []"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i81: "CSTATE ISD T 0 \<longrightarrow> reqs1 T = []"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i82: "CSTATE ISD T 1 \<longrightarrow> reqs2 T = []"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i83: "(CSTATE IMAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> reqs1 T = [])"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i84: "(CSTATE IMAD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> reqs2 T = [])"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i85: "(length (reqresps1 T) \<le> 1)"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i86: "(length (reqresps2 T) \<le> 1)"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i87: "(CSTATE MIA T 0 \<and> (nextGOPendingIs GO_WritePull T 0)  \<longrightarrow> snps1 T = [] )"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i88: "(CSTATE MIA T 1 \<and> (nextGOPendingIs GO_WritePull T 1)  \<longrightarrow> snps2 T = [] )"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i89: "(CSTATE MIA T 0 \<and> (nextGOPendingIs GO_WritePull T 0) \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> htddatas1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i90: "(CSTATE MIA T 1 \<and> (nextGOPendingIs GO_WritePull T 1) \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> htddatas2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i91: "(CSTATE ISAD T 0 \<longrightarrow> \<not> nextReqIs DirtyEvict T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i92: "(CSTATE ISAD T 1 \<longrightarrow> \<not> nextReqIs DirtyEvict T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i93: "(C_msg_P_same MIA  (nextReqIs DirtyEvict) (nextEvict) T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i94: "(reqs1 T \<noteq> [] \<longrightarrow> reqresps1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i95: "(reqs2 T \<noteq> [] \<longrightarrow> reqresps2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i98: "(reqs1 T \<noteq> [] \<longrightarrow> snpresps2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i99: "(reqs2 T \<noteq> [] \<longrightarrow> snpresps1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i100: "(reqs1 T \<noteq> [] \<longrightarrow> htddatas1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i101: "(reqs2 T \<noteq> [] \<longrightarrow> htddatas2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i751old: " (CSTATE ISD T 0 \<longrightarrow> nextLoad T 0)"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)+
have i752old: " (CSTATE ISD T 1 \<longrightarrow> nextLoad T 1)"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)+
have i104: "(reqs1 T \<noteq> [] \<longrightarrow> reqresps1 T = [] ) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i105: "(reqs2 T \<noteq> [] \<longrightarrow> reqresps2 T = [] ) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i106: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i107: "(HSTATE ModifiedM T \<longrightarrow> \<not>CSTATE Shared T 0 \<and> \<not>CSTATE Shared T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i108: "(HSTATE SD T \<and> dthdatas1 T \<noteq> [] \<longrightarrow> htddatas2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i109: "(HSTATE SD T \<and> dthdatas2 T \<noteq> [] \<longrightarrow> htddatas1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i110: "(length (dthdatas1 T ) \<le> 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i111: "(length (dthdatas2 T ) \<le> 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i112: "(HSTATE SD T \<and> nextDTHDataFrom 0 T \<longrightarrow> (CSTATE ISAD T 1 \<or> CSTATE ISD T 1)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i113: "(HSTATE SD T \<and> nextDTHDataFrom 1 T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISD T 0)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i114: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i115: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i118: "(snpresps1 T \<noteq> [] \<longrightarrow> reqresps2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i119: "(snpresps2 T \<noteq> [] \<longrightarrow> reqresps1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i120: "(length (snpresps1 T) \<le> 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i121: "(length (snpresps2 T) \<le> 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i126: "(HSTATE SAD T \<and> snpresps1 T \<noteq> [] \<longrightarrow> htddatas2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i127: "(HSTATE SAD T \<and> snpresps2 T \<noteq> [] \<longrightarrow> htddatas1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i128: "(HSTATE MD T \<and> reqs1 T \<noteq> [] \<longrightarrow> dthdatas1 T \<noteq> []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i129: "(HSTATE MD T \<and> reqs2 T \<noteq> [] \<longrightarrow> dthdatas2 T \<noteq> []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i130: "(HSTATE ID T \<and> dthdatas1 T \<noteq> [] \<longrightarrow> CSTATE Invalid T 0 \<or> CSTATE ISAD T 0 \<or> CSTATE IMAD T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i131: "(HSTATE ID T \<and> dthdatas2 T \<noteq> [] \<longrightarrow> CSTATE Invalid T 1 \<or> CSTATE ISAD T 1 \<or> CSTATE IMAD T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i132: "(HSTATE ID T \<and> dthdatas1 T \<noteq> [] \<longrightarrow> \<not>CSTATE MIA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i133: "(HSTATE ID T \<and> dthdatas2 T \<noteq> [] \<longrightarrow> \<not>CSTATE MIA T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i136: "(dthdatas1 T \<noteq> [] \<and> HSTATE SD T \<longrightarrow> snpresps2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i137: "(dthdatas2 T \<noteq> [] \<and> HSTATE SD T \<longrightarrow> snpresps1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i138: "(CSTATE ISD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> nextLoad T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i139: "(CSTATE ISD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> nextLoad T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i142: "(C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) (\<lambda> T i. \<not>nextSnoopPending T i) T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i143: "(CSTATE ISAD T 0 \<and> nextGOPending T 0 \<longrightarrow> HSTATE SD T \<or> HSTATE SharedM T \<or> HSTATE MAD T \<or> HSTATE SB T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i144: "(CSTATE ISAD T 1 \<and> nextGOPending T 1 \<longrightarrow> HSTATE SD T \<or> HSTATE SharedM T \<or> HSTATE MAD T \<or> HSTATE SB T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i145: "(CSTATE ISAD T 0 \<longrightarrow> nextLoad T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i146: "(CSTATE ISAD T 1 \<longrightarrow> nextLoad T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i147: "(CSTATE ISAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i148: "(CSTATE ISAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i149: "(CSTATE ISAD T 0 \<and> nextGOPending T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] ) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i150: "(CSTATE ISAD T 1 \<and> nextGOPending T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] ) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i153: "((CSTATE Invalid T 0 \<or> CSTATE ISDI T 0) \<and> HSTATE MD T \<longrightarrow> dthdatas1 T \<noteq> []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i154: "((CSTATE Invalid T 1 \<or> CSTATE ISDI T 1) \<and> HSTATE MD T \<longrightarrow> dthdatas2 T \<noteq> []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i159: "(HSTATE ModifiedM T \<longrightarrow> snpresps2 T = [] \<and> snpresps1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i160: "(HSTATE SAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> CSTATE ISAD T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i161: "(HSTATE SAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> CSTATE ISAD T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i164: "(HSTATE SAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> htddatas2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i165: "(HSTATE SAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> htddatas1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i166: "(HSTATE SAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqs2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i167: "(HSTATE SAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqs1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i168: "(HSTATE SD T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqs2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i169: "(HSTATE SD T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqs1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i170: "(HSTATE SharedM T \<and> nextReqIs RdOwn T 0 \<longrightarrow> dthdatas2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i171: "(HSTATE SharedM T \<and> nextReqIs RdOwn T 1 \<longrightarrow> dthdatas1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i172: "(HSTATE SharedM T \<and> nextReqIs RdShared T 0 \<longrightarrow> dthdatas2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i173: "(HSTATE SharedM T \<and> nextReqIs RdShared T 1 \<longrightarrow> dthdatas1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i178: "(CSTATE IIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> HSTATE IB T \<or> HSTATE SB T \<or> HSTATE MB T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i179: "(CSTATE IIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> HSTATE IB T \<or> HSTATE SB T \<or> HSTATE MB T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i180: "(CSTATE IIA T 0 \<and> nextGOPendingIs GO_WritePullDrop T 0 \<longrightarrow> HSTATE SharedM T \<or> HSTATE InvalidM T \<or> HSTATE ModifiedM T \<or> HSTATE SB T \<or> HSTATE ID T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i181: "(CSTATE IIA T 1 \<and> nextGOPendingIs GO_WritePullDrop T 1 \<longrightarrow> HSTATE SharedM T \<or> HSTATE InvalidM T \<or> HSTATE ModifiedM T \<or> HSTATE SB T \<or> HSTATE ID T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i182: "(CSTATE IMAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MA T \<or> HSTATE MAD T \<or> HSTATE SAD T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i183: "(CSTATE IMAD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MA T \<or> HSTATE MAD T \<or> HSTATE SAD T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i186: "(HSTATE SharedM T \<longrightarrow> dthdatas1 T = [] \<and> dthdatas2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i187: "(CSTATE MIA T 1 \<longrightarrow> \<not>CSTATE MIA T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i188: "(CSTATE MIA T 0 \<longrightarrow> \<not>CSTATE MIA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i189: "(HSTATE ModifiedM T \<longrightarrow> dthdatas2 T = [] \<and> dthdatas1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i190: "(nextDTHDataFrom  0 T \<longrightarrow> \<not> nextHTDDataPending T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i191: "(nextDTHDataFrom  1 T \<longrightarrow> \<not> nextHTDDataPending T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i192: "(nextDTHDataFrom 0 T \<longrightarrow> \<not> nextDTHDataFrom 1 T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i193: "(nextDTHDataFrom 1 T \<longrightarrow> \<not> nextDTHDataFrom 0 T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i194: "(HSTATE SA T \<longrightarrow> dthdatas2 T = [] \<and> dthdatas1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i195: "(HSTATE SD T \<longrightarrow> \<not> CSTATE IIA T 0 \<or> \<not> CSTATE IIA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i196: "(HSTATE SAD T \<longrightarrow> (\<not> CSTATE IIA T 0 \<or> nextSnpRespIs RspIFwdM T 0) \<and> (\<not> CSTATE IIA T 1 \<or> nextSnpRespIs RspIFwdM T 1)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i197: "(CSTATE IIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> \<not> nextDTHDataFrom 1 T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i198: "(CSTATE IIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> \<not> nextDTHDataFrom 0 T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i199: "(CSTATE IIA T 0 \<longrightarrow> \<not> CSTATE IIA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i200: "(CSTATE IIA T 1 \<longrightarrow> \<not> CSTATE IIA T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i301: "(CSTATE MIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> \<not> nextDTHDataFrom 1 T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i302: "(CSTATE MIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> \<not> nextDTHDataFrom 0 T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i305: "(snpresps1 T \<noteq> [] \<longrightarrow> reqresps1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i306: "(snpresps2 T \<noteq> [] \<longrightarrow> reqresps2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i307: "(HSTATE SharedM T \<and> nextReqIs RdShared T 1 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i308: "(HSTATE SharedM T \<and> nextReqIs RdShared T 0 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i309: "(HSTATE SD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i310: "(HSTATE SD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i313: "(HSTATE ModifiedM T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i314: "(C_msg_P_same SIA (nextGOPendingIs GO_WritePull) nextEvict T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i315: "(C_msg_P_same SIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextReqIs RdShared T i) T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i316: "(CSTATE SIA T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> htddatas1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i317: "(CSTATE SIA T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> htddatas2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i318: "(C_msg_P_same SIA (nextGOPendingIs GO_WritePull) (\<lambda> T i. \<not>nextSnoopPending T i) T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i319: "(CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> HSTATE IB T \<or> HSTATE SB T \<or> HSTATE MB T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i320: "(CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> HSTATE IB T \<or> HSTATE SB T \<or> HSTATE MB T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i321: "(C_msg_P_same SIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextDTHDataPending T i) T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i322: "(CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> \<not> nextDTHDataFrom 1 T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i323: "(CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> \<not> nextDTHDataFrom 0 T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i324: "(C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) nextEvict T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i325: "(C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextReqIs RdShared T i) T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i326: "(C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) (\<lambda> T i. \<not>nextSnoopPending T i) T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i327: "(CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePullDrop T 0 \<longrightarrow> HSTATE InvalidM T \<or> HSTATE SharedM T \<or> HSTATE SB T \<or> HSTATE IB T \<or> HSTATE ModifiedM T \<or> HSTATE ID T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i328: "(CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePullDrop T 1 \<longrightarrow> HSTATE InvalidM T \<or> HSTATE SharedM T \<or> HSTATE SB T \<or> HSTATE IB T \<or> HSTATE ModifiedM T \<or> HSTATE ID T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i329: "(C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextDTHDataPending T i) T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i332: "(CSTATE SMAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MA T \<or> HSTATE MAD T \<or> HSTATE SAD T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i333: "(CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow>  HSTATE SharedM T \<or> HSTATE SA T \<or> HSTATE MA T \<or> HSTATE SB T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i334: "(CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow>  HSTATE SharedM T \<or> HSTATE SA T \<or> HSTATE MA T \<or> HSTATE SB T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i335: "(CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> (CSTATE IMAD T 1 \<and> nextHTDDataPending T 1)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i336: "(CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> (CSTATE IMAD T 0 \<and> nextHTDDataPending T 0)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i337: "(C_not_C_msg Modified IMAD nextGOPending T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i338: "(CSTATE IMAD T 0 \<and> nextGOPending T 0 \<longrightarrow> HSTATE MD T \<or> HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i339: "(CSTATE IMAD T 0 \<longrightarrow> nextStore T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i340: "(CSTATE IMAD T 1 \<longrightarrow> nextStore T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i341: "(CSTATE IMAD T 0 \<and> nextGOPending T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] ) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i342: "(CSTATE IMAD T 1 \<and> nextGOPending T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] ) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i343: "(snpresps1 T \<noteq> [] \<longrightarrow> reqresps1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i344: "(snpresps2 T \<noteq> [] \<longrightarrow> reqresps2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i345: "(CSTATE SMAD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MA T \<or> HSTATE MAD T \<or> HSTATE SAD T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i346: "(CSTATE IMAD T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE MD T \<or> HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i347: "(CSTATE SMAD T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE MD T \<or> HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i348: "(CSTATE SMAD T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE MD T \<or> HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i349: "(CSTATE SMAD T 0 \<longrightarrow> nextStore T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i350: "(CSTATE SMAD T 1 \<longrightarrow> nextStore T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i351: "(C_msg_P_same IMA (nextGOPending) nextStore T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i352: "(CSTATE IMA T 0 \<or> CSTATE SMA T 0 \<or> CSTATE ISA T 0 \<longrightarrow> \<not> nextHTDDataPending T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i353: "(CSTATE IMA T 1 \<or> CSTATE SMA T 1 \<or> CSTATE ISA T 1 \<longrightarrow> \<not> nextHTDDataPending T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i354: "(C_msg_P_oppo IMA (nextGOPending) (\<lambda> T i. \<not>nextSnoopPending T i) T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i355: "(C_msg_P_oppo SMA (nextGOPending) (\<lambda> T i. \<not>nextSnoopPending T i) T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i356: "(C_msg_P_oppo ISA (nextGOPending) (\<lambda> T i. \<not>nextSnoopPending T i) T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i357: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i358: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i365: "(C_msg_P_same SMA (nextGOPending) nextStore T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i366: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i367: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i368: "(CSTATE ISD T 0 \<or> CSTATE ISAD T 0 \<or> CSTATE ISA T 0 \<or> CSTATE ISDI T 0 \<longrightarrow> nextLoad T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i369: "(CSTATE ISD T 1 \<or> CSTATE ISAD T 1 \<or> CSTATE ISA T 1 \<or> CSTATE ISDI T 1 \<longrightarrow> nextLoad T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i370: "(CSTATE IMD T 0 \<or> CSTATE IMAD T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMD T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE SMA T 0  \<longrightarrow> nextStore T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i371: "(CSTATE IMD T 1 \<or> CSTATE IMAD T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMD T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE SMA T 1  \<longrightarrow> nextStore T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i374: "(CSTATE ISA T 0 \<and> nextGOPending T 0 \<longrightarrow> HSTATE SharedM T \<or> HSTATE MAD T \<or> HSTATE MA T \<or> HSTATE SB T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i375: "(CSTATE ISA T 1 \<and> nextGOPending T 1 \<longrightarrow> HSTATE SharedM T \<or> HSTATE MAD T \<or> HSTATE MA T \<or> HSTATE SB T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i376: "(CSTATE ISDI T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> HSTATE ModifiedM T \<or> HSTATE MAD T  \<or> HSTATE MA T \<or> HSTATE MD T\<or> HSTATE ID T \<or> HSTATE InvalidM T \<or> HSTATE SharedM T \<or> HSTATE SB T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i377: "(CSTATE ISDI T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> snps1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i378: "(CSTATE ISDI T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> snps2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i379: "(CSTATE ISDI T 0 \<longrightarrow> \<not>nextReqIs RdOwn T 1 \<or> \<not>HSTATE ModifiedM T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i380: "(CSTATE ISDI T 1 \<longrightarrow> \<not>nextReqIs RdOwn T 0 \<or> \<not>HSTATE ModifiedM T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i381: "(CSTATE Invalid T 0 \<longrightarrow> reqresps1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i382: "(CSTATE Invalid T 1 \<longrightarrow> reqresps2 T = [])"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i383: "(CSTATE ISDI T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> HSTATE ModifiedM T \<or> HSTATE MAD T  \<or> HSTATE MA T \<or> HSTATE MD T\<or> HSTATE ID T \<or> HSTATE InvalidM T \<or> HSTATE SharedM T \<or> HSTATE SB T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i384: "(CSTATE Shared T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i385: "(CSTATE Shared T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i388: "(CSTATE SMAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i389: "(CSTATE SMAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i390: "(CSTATE SMAD T 0 \<and> reqresps1 T = [] \<and> htddatas1 T = [] \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i391: "(CSTATE SMAD T 1 \<and> reqresps2 T = [] \<and> htddatas2 T = [] \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T)"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i392: "(nextReqIs RdOwn T 0 \<longrightarrow> CSTATE SMAD T 0 \<or> CSTATE IMAD T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i393: "(nextReqIs RdOwn T 1 \<longrightarrow> CSTATE SMAD T 1 \<or> CSTATE IMAD T 1)"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i396: "(CSTATE SMAD T 0 \<and> nextSnoopIs SnpInv T 0 \<and> CXL_SPG_used T 0 \<longrightarrow> nextReqIs RdOwn T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i397: "(CSTATE SMAD T 1 \<and> nextSnoopIs SnpInv T 1 \<and> CXL_SPG_used T 1 \<longrightarrow> nextReqIs RdOwn T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i400: "(CSTATE ISD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i401: "(CSTATE ISD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i406: "(CSTATE IMA T 0 \<or> CSTATE SMA T 0 \<or> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0)  \<longrightarrow> dthdatas1 T = [] \<and> (dthdatas2 T = [] \<or> HSTATE MB T \<or> HSTATE ModifiedM T)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i407: "(CSTATE IMA T 1 \<or> CSTATE SMA T 1 \<or> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1)  \<longrightarrow> dthdatas2 T = [] \<and> (dthdatas1 T = [] \<or> HSTATE MB T \<or> HSTATE ModifiedM T)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i408: "(HSTATE MD T \<longrightarrow> snpresps1 T = [] \<and> snpresps2 T = [])"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i415: "(HSTATE ModifiedM T  \<and> nextReqIs RdOwn T 0 \<longrightarrow> (CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i416: "(HSTATE ModifiedM T  \<and> nextReqIs RdOwn T 1 \<longrightarrow> (CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i417: "((CSTATE Invalid T 0 \<or> CSTATE ISDI T 0) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i418: "((CSTATE Invalid T 1 \<or> CSTATE ISDI T 1) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i419: "(CSTATE IIA T 0 \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i420: "(CSTATE IIA T 1 \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i421: "(HSTATE MD T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i422: "(HSTATE MD T \<and> nextDTHDataFrom 0 T \<longrightarrow> CSTATE IMAD T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i423: "(HSTATE MD T \<and> nextDTHDataFrom 1 T \<longrightarrow> CSTATE IMAD T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i424: "(HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> CSTATE IMAD T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i425: "(HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> CSTATE IMAD T 0)"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i426: "(HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> snpresps2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i427: "(HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> snpresps1 T = [])"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i430: "(HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> reqs2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i431: "(HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE Modified T 1 \<and> reqs1 T = [])"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i432: "(HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqresps2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i433: "(HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqresps1 T = [])"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i437: "(CSTATE IMD T 0 \<or> CSTATE SMD T 0 \<or> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextGOPending T 0) \<longrightarrow> dthdatas1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i438: "(CSTATE IMD T 1 \<or> CSTATE SMD T 1 \<or> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextGOPending T 1) \<longrightarrow> dthdatas2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i441: "(HSTATE SAD T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 ) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i442: "(HSTATE SAD T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 ) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i445: "(nextSnpRespIs RspSFwdM T 0 \<longrightarrow> CSTATE Shared T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE SIA T 0 \<or> CSTATE SIAC T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i446: "(nextSnpRespIs RspSFwdM T 1 \<longrightarrow> CSTATE Shared T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE SIA T 1 \<or> CSTATE SIAC T 1)"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i447: "((HSTATE SAD T \<or> HSTATE MAD T \<or> HSTATE SA T \<or> HSTATE MA T) \<and> snpresps1 T \<noteq> [] \<longrightarrow> htddatas1 T = [] \<or> CSTATE ISDI T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i448: "((HSTATE SAD T \<or> HSTATE MAD T \<or> HSTATE SA T \<or> HSTATE MA T) \<and> snpresps2 T \<noteq> [] \<longrightarrow> htddatas2 T = [] \<or> CSTATE ISDI T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i449: "(HSTATE SAD T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i450: "(HSTATE SAD T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i453: "(HSTATE MAD T \<and> nextSnpRespIs RspIFwdM T 0 \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> dthdatas1 T \<noteq> [] \<and> htddatas2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i454: "(HSTATE MAD T \<and> nextSnpRespIs RspIFwdM T 1 \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> dthdatas2 T \<noteq> [] \<and> htddatas1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i455: "(HSTATE MA T \<and> snpresps1 T \<noteq> [] \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> htddatas2 T \<noteq> [] \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> htddatas2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i456: "(HSTATE MA T \<and> snpresps2 T \<noteq> [] \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> htddatas1 T \<noteq> [] \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> htddatas1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i457: "(nextReqIs DirtyEvict T 0 \<longrightarrow> CSTATE MIA T 0 \<or>  CSTATE SIA T 0 \<or> CSTATE IIA T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i458: "(nextReqIs DirtyEvict T 1 \<longrightarrow> CSTATE MIA T 1 \<or>  CSTATE SIA T 1 \<or> CSTATE IIA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i459: "(HSTATE MA T \<longrightarrow> dthdatas2 T = [] \<and> dthdatas1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i460: "((nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspIHitSE T 0) \<longrightarrow> CSTATE Invalid T 0 \<or> CSTATE ISDI T 0 \<or> CSTATE ISAD T 0 \<or> CSTATE IMAD T 0 \<or> CSTATE IIA T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i461: "((nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspIHitSE T 1) \<longrightarrow> CSTATE Invalid T 1 \<or> CSTATE ISDI T 1 \<or> CSTATE ISAD T 1 \<or> CSTATE IMAD T 1 \<or> CSTATE IIA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i464: "((CSTATE Invalid T 0  \<or> CSTATE ISDI T 0 \<or> nextReqIs RdOwn T 0) \<and> HSTATE MA T \<longrightarrow> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i465: "((CSTATE Invalid T 1  \<or> CSTATE ISDI T 1 \<or> nextReqIs RdOwn T 1) \<and> HSTATE MA T \<longrightarrow> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0))"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i466: "((CSTATE ISAD T 0 \<and> nextGOPending T 0) \<or> CSTATE ISA T 0 \<or> ( nextHTDDataPending T 0) \<or> CSTATE Shared T 0 \<longrightarrow> \<not> CSTATE Modified T 1 \<and> (dthdatas1 T = [] \<or> nextSnpRespIs RspSFwdM T 0 \<or> HSTATE SD T)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i467: "((CSTATE ISAD T 1 \<and> nextGOPending T 1) \<or> CSTATE ISA T 1 \<or> ( nextHTDDataPending T 1) \<or> CSTATE Shared T 1 \<longrightarrow> \<not> CSTATE Modified T 0 \<and> (dthdatas2 T = [] \<or> nextSnpRespIs RspSFwdM T 1 \<or> HSTATE SD T)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i469: "(CSTATE IMD T 0 \<or> CSTATE SMD T 0 \<or> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextGOPending T 0) \<longrightarrow> ((\<not> CSTATE ISD T 1) \<and> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE SMD T 1 \<and> \<not>( (CSTATE ISAD T 1 \<or> CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextGOPending T 1) \<and> \<not>CSTATE ISA T 1 \<and> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> \<not> (  nextHTDDataPending T 1) \<and>  \<not> CSTATE Shared T 1 \<and> \<not> CSTATE Modified T 1) \<or> nextSnoopIs SnpInv T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i470: "(CSTATE IMD T 1 \<or> CSTATE SMD T 1 \<or> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextGOPending T 1) \<longrightarrow> ((\<not> CSTATE ISD T 0) \<and> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE SMD T 0 \<and> \<not>( (CSTATE ISAD T 0 \<or> CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextGOPending T 0) \<and> \<not>CSTATE ISA T 0 \<and> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0 \<and> \<not> (  nextHTDDataPending T 0) \<and>  \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Modified T 0) \<or> nextSnoopIs SnpInv T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i471: "(CSTATE Shared T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE SMA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i472: "(CSTATE Shared T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE SMA T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i473: "(CSTATE ISD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE SMA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i474: "(CSTATE ISD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE SMA T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i475: "(HSTATE MD T \<and> nextDTHDataFrom 0 T \<longrightarrow>  \<not> nextReqIs CleanEvict T 0 \<and> \<not> nextReqIs CleanEvictNoData T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i476: "(HSTATE MD T \<and> nextDTHDataFrom 1 T \<longrightarrow>  \<not> nextReqIs CleanEvict T 1 \<and> \<not> nextReqIs CleanEvictNoData T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i477: "(HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow>  \<not> nextReqIs CleanEvict T 0 \<and> \<not> nextReqIs CleanEvictNoData T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i478: "(HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow>  \<not> nextReqIs CleanEvict T 1 \<and> \<not> nextReqIs CleanEvictNoData T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i479: "(CSTATE Modified T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MAD T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i480: "(CSTATE Modified T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MAD T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i481: "(CSTATE Modified T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 ) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i482: "(CSTATE Modified T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 ) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i483: "(CSTATE MIA T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i484: "(CSTATE MIA T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i485: "(CSTATE MIA T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> CSTATE ISAD T 1 ) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i486: "(CSTATE MIA T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> CSTATE ISAD T 0 ) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i487: "(CSTATE Modified T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i488: "(CSTATE Modified T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i489: "(CSTATE Modified T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> CSTATE ISAD T 1 ) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i490: "(CSTATE Modified T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> CSTATE ISAD T 0 ) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i491: "(CSTATE Modified T 0 \<longrightarrow> reqs1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i492: "(CSTATE Modified T 1 \<longrightarrow> reqs2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i493: "(CSTATE Modified T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i494: "(CSTATE Modified T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i495: "(HSTATE InvalidM T \<and> nextReqIs RdShared T 0 \<longrightarrow> dthdatas2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i496: "(HSTATE InvalidM T \<and> nextReqIs RdShared T 1 \<longrightarrow> dthdatas1 T = [])"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i497: "(HSTATE InvalidM T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1 \<and> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1)"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i498: "(nextReqIs RdOwn T 0 \<longrightarrow> \<not> CSTATE ISAD T 0 \<and> \<not> CSTATE Invalid T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i499: "(nextReqIs RdOwn T 1 \<longrightarrow> \<not> CSTATE ISAD T 1 \<and> \<not> CSTATE Invalid T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i500: "(HSTATE InvalidM T \<and> nextReqIs RdOwn T 0 \<longrightarrow> CSTATE IMAD T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i501: "(HSTATE InvalidM T \<and> nextReqIs RdOwn T 1 \<longrightarrow> CSTATE IMAD T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i502: "(HSTATE InvalidM T \<and> nextReqIs RdOwn T 0 \<longrightarrow> dthdatas2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i503: "(HSTATE InvalidM T \<and> nextReqIs RdOwn T 1 \<longrightarrow> dthdatas1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i504: "(CSTATE SIA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i505: "(CSTATE SIA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i506: "(CSTATE SIA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i507: "(CSTATE SIA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i508: "(CSTATE SIA T 0 \<and> nextSnoopIs SnpInv T 0 \<and> CXL_SPG_used T 0 \<longrightarrow> (nextReqIs CleanEvict T 0 \<or> nextReqIs CleanEvictNoData T 0 )) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i509: "(CSTATE SIA T 1 \<and> nextSnoopIs SnpInv T 1 \<and> CXL_SPG_used T 1 \<longrightarrow> (nextReqIs CleanEvict T 1 \<or> nextReqIs CleanEvictNoData T 1 )) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i510: "(CSTATE SIA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE SMA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i511: "(CSTATE SIA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE SMA T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i512: "(CSTATE SMAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE SMA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i513: "(CSTATE SMAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE SMA T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i514: "(HSTATE ID T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1 \<and> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i515: "(HSTATE ModifiedM T \<and> nextReqIs DirtyEvict T 0 \<longrightarrow> (\<not> CSTATE Modified T 0 \<or> \<not> CSTATE Modified T 1) \<and> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i516: "(HSTATE ModifiedM T \<and> nextReqIs DirtyEvict T 1 \<longrightarrow> (\<not> CSTATE Modified T 0 \<or> \<not> CSTATE Modified T 1) \<and> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1)"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i517: "(HSTATE ID T \<and> nextReqIs RdOwn T 0 \<longrightarrow> CSTATE IMAD T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i518: "(HSTATE ID T \<and> nextReqIs RdOwn T 1 \<longrightarrow> CSTATE IMAD T 1)"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i519: "(CSTATE SMAD T 0 \<and> nextGOPending T 0\<longrightarrow> nextHTDDataPending T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i520: "(CSTATE SMAD T 1 \<and> nextGOPending T 1\<longrightarrow> nextHTDDataPending T 1)"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i521: "(C_msg_P_oppo SMAD nextGOPending (\<lambda>T i. \<not> nextSnoopPending T i) T)"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i522: "(HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 0 \<longrightarrow> CSTATE SIAC T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i523: "(HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 1 \<longrightarrow> CSTATE SIAC T 1)"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i526: "(nextGOPendingIs GO_WritePull T 0 \<and> HSTATE InvalidM T \<longrightarrow> reqresps2 T = [] \<or> nextReqRespStateIs Invalid (reqresps2 T)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i527: "(nextGOPendingIs GO_WritePull T 1 \<and> HSTATE InvalidM T \<longrightarrow> reqresps1 T = [] \<or> nextReqRespStateIs Invalid (reqresps1 T)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i528: "(HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 0 \<longrightarrow> nextEvict T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i529: "(HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 1 \<longrightarrow> nextEvict T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i530: "(HSTATE SharedM T \<and> nextReqIs CleanEvict T 0 \<longrightarrow> nextEvict T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i531: "(HSTATE SharedM T \<and> nextReqIs CleanEvict T 1 \<longrightarrow> nextEvict T 1)"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i532: "(HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 0 \<longrightarrow> \<not> CSTATE ISDI T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i533: "(HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 1 \<longrightarrow> \<not> CSTATE ISDI T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i534: "(HSTATE SharedM T \<and> nextReqIs CleanEvict T 0 \<longrightarrow> \<not> CSTATE ISDI T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i535: "(HSTATE SharedM T \<and> nextReqIs CleanEvict T 1 \<longrightarrow> \<not> CSTATE ISDI T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i536: "(HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 0 \<longrightarrow> \<not> CSTATE MIA T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i537: "(HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 1 \<longrightarrow> \<not> CSTATE MIA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i538: "(HSTATE SharedM T \<and> nextReqIs CleanEvict T 0 \<longrightarrow> \<not> CSTATE MIA T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i539: "(HSTATE SharedM T \<and> nextReqIs CleanEvict T 1 \<longrightarrow> \<not> CSTATE MIA T 1)"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i540: "(CSTATE Shared T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> htddatas2 T \<noteq> [] \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> htddatas2 T = [])) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i541: "(CSTATE Shared T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> htddatas1 T \<noteq> [] \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> htddatas1 T = []))"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i542: "(nextReqIs DirtyEvict T 0 \<longrightarrow> nextEvict T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i543: "(nextReqIs DirtyEvict T 1 \<longrightarrow> nextEvict T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i544: "(nextReqIs DirtyEvict T 0 \<and> HSTATE InvalidM T \<longrightarrow> \<not> nextDTHDataFrom 1 T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i545: "(nextReqIs DirtyEvict T 1 \<and> HSTATE InvalidM T \<longrightarrow> \<not> nextDTHDataFrom 0 T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i546: "(nextReqIs DirtyEvict T 0 \<and> HSTATE InvalidM T \<longrightarrow> \<not> CSTATE ISDI T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i547: "(nextReqIs DirtyEvict T 1 \<and> HSTATE InvalidM T \<longrightarrow> \<not> CSTATE ISDI T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i548: "(nextReqIs DirtyEvict T 0 \<and> HSTATE InvalidM T \<longrightarrow> (reqresps2 T = [] \<or> nextReqRespStateIs Invalid (reqresps2 T))) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i549: "(nextReqIs DirtyEvict T 1 \<and> HSTATE InvalidM T \<longrightarrow> (reqresps1 T = [] \<or> nextReqRespStateIs Invalid (reqresps1 T)))"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i550: "(CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not>(CSTATE ISA T 1 \<or> nextHTDDataPending T 1)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i551: "(CSTATE SMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not>(CSTATE ISA T 0 \<or> nextHTDDataPending T 0)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i552: "(CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MAD T \<and> CSTATE IMAD T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i553: "(CSTATE SMD T 1 \<and> nextHTDDataPending T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MAD T \<and> CSTATE IMAD T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i554: "(CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T \<and> CSTATE ISAD T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i555: "(CSTATE SMD T 1 \<and> nextHTDDataPending T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T \<and> CSTATE ISAD T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i556: "(CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i557: "(CSTATE SMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i558: "(CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> nextReqIs DirtyEvict T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i559: "(CSTATE SMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> nextReqIs DirtyEvict T 0)"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i560: "((nextReqIs CleanEvictNoData T 0 \<or> nextReqIs CleanEvict T 0) \<longrightarrow> (CSTATE SIA T 0 \<or> CSTATE IIA T 0 \<or> CSTATE SIAC T 0)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i561: "((nextReqIs CleanEvictNoData T 1 \<or> nextReqIs CleanEvict T 1) \<longrightarrow> (CSTATE SIA T 1 \<or> CSTATE IIA T 1 \<or> CSTATE SIAC T 1)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i562: "((CSTATE Shared T 0 \<or> CSTATE Shared T 1) \<longrightarrow> \<not> HSTATE MD T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i563: "(CSTATE Shared T 0 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i564: "(CSTATE Shared T 1 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i565: "((nextReqIs CleanEvictNoData T 0 \<or> nextReqIs CleanEvict T 0) \<longrightarrow> nextEvict T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i566: "((nextReqIs CleanEvictNoData T 1 \<or> nextReqIs CleanEvict T 1) \<longrightarrow> nextEvict T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i567: "((nextReqIs CleanEvictNoData T 0 \<or> nextReqIs CleanEvict T 0) \<longrightarrow> \<not> CSTATE ISDI T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i568: "((nextReqIs CleanEvictNoData T 1 \<or> nextReqIs CleanEvict T 1) \<longrightarrow> \<not> CSTATE ISDI T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i569: "((nextReqIs CleanEvictNoData T 0 \<or> nextReqIs CleanEvict T 0) \<longrightarrow> \<not> CSTATE MIA T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i570: "((nextReqIs CleanEvictNoData T 1 \<or> nextReqIs CleanEvict T 1) \<longrightarrow> \<not> CSTATE MIA T 1)"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i571: "(CSTATE IIA T 0 \<and> HSTATE SharedM T \<longrightarrow> reqs2 T = [] \<or> nextReqIs CleanEvict T 1 \<or> nextReqIs CleanEvictNoData T 1 \<or> nextReqIs RdOwn T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i572: "(CSTATE IIA T 1 \<and> HSTATE SharedM T \<longrightarrow> reqs1 T = [] \<or> nextReqIs CleanEvict T 0 \<or> nextReqIs CleanEvictNoData T 0 \<or> nextReqIs RdOwn T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i573: "(CSTATE IIA T 0 \<and> HSTATE SharedM T \<longrightarrow> CSTATE Shared T 1 \<or> CSTATE SIA T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE ISAD T 1 \<and> nextGOPending T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1 \<and> nextGOPending T 1 \<or> CSTATE ISD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SIAC T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i574: "(CSTATE IIA T 1 \<and> HSTATE SharedM T \<longrightarrow> CSTATE Shared T 0 \<or> CSTATE SIA T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE ISAD T 0 \<and> nextGOPending T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0 \<and> nextGOPending T 0 \<or> CSTATE ISD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SIAC T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i575: "(CSTATE IIA T 1 \<and> HSTATE InvalidM T \<and> nextReqIs RdShared T 0 \<longrightarrow> CSTATE ISAD T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i576: "(CSTATE IIA T 0 \<and> HSTATE InvalidM T \<and> nextReqIs RdShared T 1 \<longrightarrow> CSTATE ISAD T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i577: "(HSTATE InvalidM T \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0 \<and> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE SMD T 0 \<and>  \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE SMD T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i578: "(HSTATE InvalidM T \<longrightarrow> \<not> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0)) \<and> \<not> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i579: "(nextGOPendingIs GO_WritePull T 0 \<or> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> \<not> HSTATE InvalidM T)"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i580: "(CSTATE MIA T 0 \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> \<not> nextHTDDataPending T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i581: "(CSTATE MIA T 1 \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0 \<and> \<not> nextHTDDataPending T 0)"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i582: "(nextGOPendingIs GO_WritePull T 0 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i583: "(nextGOPendingIs GO_WritePull T 1 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0)"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i584: "((CSTATE IMA T 0 \<or> CSTATE SMA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0) \<longrightarrow> (HSTATE MA T \<or> HSTATE ModifiedM T \<or> HSTATE MB T \<or> HSTATE MAD T \<or> HSTATE SAD T)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i585: "((CSTATE IMA T 1 \<or> CSTATE SMA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1) \<longrightarrow> (HSTATE MA T \<or> HSTATE ModifiedM T \<or> HSTATE MB T \<or> HSTATE MAD T \<or> HSTATE SAD T))"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i586: "(CSTATE MIA T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> htddatas1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i587: "(CSTATE MIA T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> htddatas2 T = [])"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i588: "(CSTATE MIA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MAD T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i589: "(CSTATE MIA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MAD T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i590: "(CSTATE MIA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i591: "(CSTATE MIA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0)"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i592: "((HSTATE InvalidM T \<or> HSTATE SharedM T \<or> HSTATE ModifiedM T) \<longrightarrow> (\<not> nextGOPendingIs GO_WritePull T 0) \<and> (\<not> nextGOPendingIs GO_WritePull T 1))"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i593: "(CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePullDrop T 0 \<and> CSTATE IIA T 1 \<longrightarrow> HSTATE InvalidM T \<or> HSTATE IB T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i594: "(CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePullDrop T 1 \<and> CSTATE IIA T 0 \<longrightarrow> HSTATE InvalidM T \<or> HSTATE IB T)"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i595: "(HSTATE InvalidM T \<longrightarrow> dthdatas1 T = [] \<and> dthdatas2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i596: "(CSTATE Invalid T 0 \<longrightarrow> \<not> nextSnoopIs SnpInv T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i597: "(CSTATE Invalid T 1 \<longrightarrow> \<not> nextSnoopIs SnpInv T 1)"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i598: "(CSTATE Modified T 0 \<longrightarrow> \<not> CSTATE MIA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i599: "(CSTATE Modified T 1 \<longrightarrow> \<not> CSTATE MIA T 0)"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i600: "(HSTATE MA T \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> htddatas2 T \<noteq> [] \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> htddatas2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i601: "(HSTATE MA T \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> htddatas1 T \<noteq> [] \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> htddatas1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i602: "(CSTATE SMAD T 0 \<and> nextGOPending T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i603: "(CSTATE SMAD T 1 \<and> nextGOPending T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i604: "(HSTATE MA T \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i605: "(HSTATE MA T \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0)"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i606: "(HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> CSTATE ISD T 0 \<and> \<not> CSTATE ISA T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i607: "(HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> CSTATE ISD T 1 \<and> \<not> CSTATE ISA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i608: "(HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> CSTATE SMD T 0 \<and> \<not> CSTATE SMA T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i609: "(HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> CSTATE SMD T 1 \<and> \<not> CSTATE SMA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i610: "(HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE IMA T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i611: "(HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE IMA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i612: "(HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> (CSTATE ISAD T 0 \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0))) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i613: "(HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> (CSTATE IMAD T 0 \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0))) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i614: "(HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> (CSTATE SMAD T 0 \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0))) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i615: "(HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> (CSTATE ISAD T 1 \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i616: "(HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> (CSTATE IMAD T 1 \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i617: "(HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> (CSTATE SMAD T 1 \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i618: "(CSTATE ISD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> htddatas2 T \<noteq> []) \<or> ((CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> htddatas2 T = [])) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i619: "(CSTATE ISD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> htddatas1 T \<noteq> []) \<or> ((CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> htddatas1 T = [])) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i620: "(CSTATE ISA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> htddatas2 T \<noteq> []) \<or> ((CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> htddatas2 T = [])) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i621: "(CSTATE ISA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> htddatas1 T \<noteq> []) \<or> ((CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> htddatas1 T = [])) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i622: "(CSTATE ISAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> htddatas2 T \<noteq> []) \<or> ((CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> htddatas2 T = [])) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i623: "(CSTATE ISAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> htddatas1 T \<noteq> []) \<or> ((CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> htddatas1 T = [])) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i624: "(CSTATE IMAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i625: "(CSTATE IMAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i626: "(CSTATE IMD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i627: "(CSTATE IMD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i628: "(CSTATE IMA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i629: "(CSTATE IMA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i630: "(CSTATE SMAD T 0 \<and> nextGOPending T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i631: "(CSTATE SMAD T 1 \<and> nextGOPending T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i632: "(CSTATE SMD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i633: "(CSTATE SMD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i634: "(CSTATE SMA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i635: "(CSTATE SMA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i636: "(CSTATE ISD T 0 \<or> CSTATE ISA T 0 \<longrightarrow> \<not> HSTATE MD T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i637: "(CSTATE ISD T 1 \<or> CSTATE ISA T 1 \<longrightarrow> \<not> HSTATE MD T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i638: "(CSTATE ISAD T 0 \<and> (nextHTDDataPending T 0 \<or> nextGOPending T 0) \<longrightarrow> \<not> HSTATE MD T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i639: "(CSTATE ISAD T 1 \<and> (nextHTDDataPending T 1 \<or> nextGOPending T 1) \<longrightarrow> \<not> HSTATE MD T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i640: "(CSTATE ISD T 0 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i641: "(CSTATE ISD T 1 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i642: "(CSTATE ISA T 0 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i643: "(CSTATE ISA T 1 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0)"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i644: "(CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> (CSTATE ISAD T 1 \<and> nextGOPending T 1)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i645: "(CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> (CSTATE ISAD T 0 \<and> nextGOPending T 0)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i646: "(CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> CSTATE ISA T 1 \<and> \<not> nextHTDDataPending T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i647: "(CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> nextHTDDataPending T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i648: "(CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> CSTATE Shared T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i649: "(CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> CSTATE Shared T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i650: "(CSTATE ISA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i651: "(CSTATE ISA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i652: "(CSTATE ISAD T 0 \<and> nextGOPending T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i653: "(CSTATE ISAD T 1 \<and> nextGOPending T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i654: "(CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i655: "(CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T)"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i656: "(HSTATE SharedM T \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i657: "(HSTATE SharedM T \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i658: "(HSTATE SharedM T \<longrightarrow> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE SMD T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i659: "(HSTATE SharedM T \<longrightarrow> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE SMD T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i660: "(HSTATE SharedM T \<longrightarrow> \<not> (CSTATE IMAD T 0 \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0))) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i661: "(HSTATE SharedM T \<longrightarrow> \<not> (CSTATE IMAD T 1 \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i662: "(HSTATE SharedM T \<longrightarrow> \<not> (CSTATE SMAD T 0 \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0))) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i663: "(HSTATE SharedM T \<longrightarrow> \<not> (CSTATE SMAD T 1 \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i664: "(HSTATE SharedM T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i665: "(HSTATE InvalidM T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i666: "(HSTATE InvalidM T \<longrightarrow> \<not> CSTATE ISD T 0 \<and> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE SMD T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i667: "(HSTATE InvalidM T \<longrightarrow> \<not> CSTATE ISD T 1 \<and> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE SMD T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i668: "(HSTATE InvalidM T \<longrightarrow> \<not> (CSTATE ISAD T 0 \<and> nextGOPending T 0)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i669: "(HSTATE InvalidM T \<longrightarrow> \<not> (CSTATE ISAD T 1 \<and> nextGOPending T 1)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i670: "(HSTATE InvalidM T \<longrightarrow> \<not> (CSTATE IMAD T 0 \<and> nextGOPending T 0)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i671: "(HSTATE InvalidM T \<longrightarrow> \<not> (CSTATE IMAD T 1 \<and> nextGOPending T 1)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i672: "(HSTATE InvalidM T \<longrightarrow> \<not> (CSTATE SMAD T 0 \<and> nextGOPending T 0)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i673: "(HSTATE InvalidM T \<longrightarrow> \<not> (CSTATE SMAD T 1 \<and> nextGOPending T 1)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i674: "(HSTATE InvalidM T \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i675: "(HSTATE InvalidM T \<longrightarrow> \<not> CSTATE ISA T 1 \<and> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i676: "(HSTATE InvalidM T \<longrightarrow> \<not> nextHTDDataPending T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i677: "(HSTATE InvalidM T \<longrightarrow> \<not> nextHTDDataPending T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i678: "(HSTATE InvalidM T \<longrightarrow> \<not> CSTATE Shared T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i679: "(HSTATE InvalidM T \<longrightarrow> \<not> CSTATE Shared T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i680: "(HSTATE InvalidM T \<longrightarrow> \<not> CSTATE Modified T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i681: "(CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> snpresps2 T = [] \<and> reqresps1 T = [] \<and> snps2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i682: "(CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> snpresps1 T = [] \<and> reqresps2 T = [] \<and> snps1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i683: "(CSTATE IMAD T 0 \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<longrightarrow> snpresps2 T = [] \<and> snps2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i684: "(CSTATE IMAD T 1 \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<longrightarrow> snpresps1 T = [] \<and> snps1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i685: "(CSTATE IMD T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> CSTATE ISAD T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i686: "(CSTATE IMD T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> CSTATE ISAD T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i687: "(CSTATE IMA T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> CSTATE ISAD T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i688: "(CSTATE IMA T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> CSTATE ISAD T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i689: "(CSTATE IMAD T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> CSTATE ISAD T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i690: "(CSTATE IMAD T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> CSTATE ISAD T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i691: "(CSTATE IMD T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i692: "(CSTATE IMD T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i693: "(CSTATE IMA T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i694: "(CSTATE IMA T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i695: "(CSTATE IMAD T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i696: "(CSTATE IMD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MAD T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i697: "(CSTATE IMD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MAD T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i698: "(CSTATE IMAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MAD T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i699: "(CSTATE IMAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MAD T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i700: "(CSTATE IMA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MAD T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i701: "(CSTATE IMA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MAD T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i702: "(CSTATE IMAD T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i703: "(HSTATE IB T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1 \<and> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i704: "(HSTATE IB T \<and> nextReqIs RdOwn T 0 \<longrightarrow> CSTATE IMAD T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i705: "(HSTATE IB T \<and> nextReqIs RdOwn T 1 \<longrightarrow> CSTATE IMAD T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i706: "(HSTATE SB T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i707: "(HSTATE SB T \<longrightarrow> length (dthdatas1 T) \<le> 1 \<and> length (dthdatas2 T) \<le> 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i708: "(HSTATE IB T \<longrightarrow> length (dthdatas1 T) \<le> 1 \<and> length (dthdatas2 T) \<le> 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i709: "(HSTATE SB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE IIA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i710: "(HSTATE SB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE IIA T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i711: "(HSTATE MB T \<longrightarrow> length (dthdatas1 T) \<le> 1 \<and> length (dthdatas2 T) \<le> 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i712: "(HSTATE SB T \<and> nextDTHDataFrom 0 T \<longrightarrow> dthdatas2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i713: "(HSTATE SB T \<and> nextDTHDataFrom 1 T \<longrightarrow> dthdatas1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i714: "(HSTATE IB T \<and> nextDTHDataFrom 0 T \<longrightarrow> dthdatas2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i715: "(HSTATE IB T \<and> nextDTHDataFrom 1 T \<longrightarrow> dthdatas1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i716: "(HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> dthdatas2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i717: "(HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> dthdatas1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i718: "(HSTATE SB T \<longrightarrow> snps2 T = [] \<and> snps1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i719: "(HSTATE IB T \<longrightarrow> snps2 T = [] \<and> snps1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i720: "(HSTATE MB T \<longrightarrow> snps2 T = [] \<and> snps1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i721: "(HSTATE SB T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqresps1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i722: "(HSTATE SB T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqresps2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i723: "(HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqresps1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i724: "(HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqresps2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i725: "(HSTATE IB T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqresps1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i726: "(HSTATE IB T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqresps2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i727: "(HSTATE SB T \<longrightarrow> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE SMD T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i728: "(HSTATE SB T \<longrightarrow> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE SMD T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i729: "(HSTATE IB T \<longrightarrow> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE SMD T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i730: "(HSTATE IB T \<longrightarrow> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE SMD T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i731: "(HSTATE SharedM T \<and> lastSharer T \<and> nextReqIs CleanEvictNoData T 0 \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i732: "(HSTATE SharedM T \<and> lastSharer T \<and> nextReqIs CleanEvictNoData T 1 \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i733: "(HSTATE SharedM T \<and> lastSharer T \<and> nextReqIs CleanEvictNoData T 0 \<longrightarrow> \<not> (CSTATE ISAD T 1 \<and> nextGOPending T 1)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i734: "(HSTATE SharedM T \<and> lastSharer T \<and> nextReqIs CleanEvictNoData T 1 \<longrightarrow> \<not> (CSTATE ISAD T 0 \<and> nextGOPending T 0))"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i735: "(CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> snpresps1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i736: "(CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> snpresps2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i737: "(HSTATE SAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> snpresps2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i738: "(HSTATE SAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> snpresps1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i739: "(CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i740: "(CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0)"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i741: "(HSTATE ModifiedM T \<longrightarrow> (\<not> CSTATE SIA T 0 \<or> nextGOPendingIs GO_WritePullDrop T 0) \<and> (\<not> CSTATE SIA T 1 \<or> nextGOPendingIs GO_WritePullDrop T 1)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i742: "(HSTATE MA T \<and> snpresps1 T \<noteq> [] \<longrightarrow> \<not> CSTATE SIA T 0 \<and> \<not> CSTATE SIA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i743: "(HSTATE MA T \<and> snpresps2 T \<noteq> [] \<longrightarrow> \<not> CSTATE SIA T 0 \<and> \<not> CSTATE SIA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i744: "(HSTATE MD T \<longrightarrow> \<not> CSTATE SIA T 0 \<and> \<not> CSTATE SIA T 1)"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i745: "(CSTATE MIA T 0 \<longrightarrow> \<not> (CSTATE IMAD T 1 \<and> nextGOPending T 1)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i746: "(CSTATE MIA T 1 \<longrightarrow> \<not> (CSTATE IMAD T 0 \<and> nextGOPending T 0)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i747: "(CSTATE MIA T 0 \<longrightarrow> \<not> (CSTATE SMAD T 1 \<and> nextGOPending T 1)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i748: "(CSTATE MIA T 1 \<longrightarrow> \<not> (CSTATE SMAD T 0 \<and> nextGOPending T 0)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i749: "(HSTATE ModifiedM T \<and> nextReqIs RdOwn T 0 \<longrightarrow> CSTATE IMAD T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i750: "(HSTATE ModifiedM T \<and> nextReqIs RdOwn T 1 \<longrightarrow> CSTATE IMAD T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i751: "(HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE ISA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i752: "(HSTATE MD T \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE ISA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i753: "(HSTATE MA T \<and> snpresps1 T \<noteq> [] \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE ISA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i754: "(HSTATE MA T \<and> snpresps2 T \<noteq> [] \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE ISA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i755: "(CSTATE MIA T 0 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE SMA T 1 \<and> \<not> CSTATE SMD T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i756: "(CSTATE MIA T 1 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE SMA T 0 \<and> \<not> CSTATE SMD T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i757: "(CSTATE MIA T 0 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE IMD T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i758: "(CSTATE MIA T 1 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE IMD T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i759: "(CSTATE MIA T 0 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> (CSTATE IMAD T 1 \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i760: "(CSTATE MIA T 1 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> (CSTATE IMAD T 0 \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0))) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i761: "(CSTATE MIA T 0 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE SMAD T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i762: "(CSTATE MIA T 1 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE SMAD T 0)"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i763: "(CSTATE IMD T 1 \<longrightarrow> reqresps2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i764: "(CSTATE IMD T 0 \<longrightarrow> reqresps1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i765: "(HSTATE IB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i766: "(HSTATE IB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i767: "(HSTATE IB T \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE ISD T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i768: "(HSTATE IB T \<longrightarrow> \<not> CSTATE ISA T 1 \<and> \<not> CSTATE ISD T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i769: "(HSTATE IB T \<longrightarrow> \<not> CSTATE SMA T 0 \<and> \<not> CSTATE SMD T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i770: "(HSTATE IB T \<longrightarrow> \<not> CSTATE SMA T 1 \<and> \<not> CSTATE SMD T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i771: "(HSTATE IB T \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE IMD T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i772: "(HSTATE IB T \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE IMD T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i773: "(HSTATE IB T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i774: "(HSTATE IB T \<longrightarrow> \<not> nextHTDDataPending T 0 \<and> \<not> nextHTDDataPending T 1)"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i775: "(HSTATE ID T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i776: "(HSTATE ID T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i777: "(HSTATE ID T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqresps1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i778: "(HSTATE ID T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqresps2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i779: "(HSTATE ID T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextHTDDataPending T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i780: "(HSTATE ID T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextHTDDataPending T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i781: "(HSTATE ModifiedM T \<and> nextReqIs RdShared T 0 \<longrightarrow> \<not> CSTATE ISDI T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i782: "(HSTATE ModifiedM T \<and> nextReqIs RdShared T 1 \<longrightarrow> \<not> CSTATE ISDI T 0)"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i783: "(HSTATE SD T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i784: "(HSTATE SAD T \<and> snpresps1 T \<noteq> [] \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i785: "(HSTATE SAD T \<and> snpresps2 T \<noteq> [] \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1)"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i786: "(HSTATE MD T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i787: "(snpresps1 T \<noteq> [] \<and> HSTATE MAD T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i788: "(snpresps2 T \<noteq> [] \<and> HSTATE MAD T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i789: "(CSTATE IMD T 0 \<and> HSTATE MD T \<longrightarrow> snpresps1 T = [] \<and> snps1 T = [] \<and> reqresps2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i790: "(CSTATE IMD T 1 \<and> HSTATE MD T \<longrightarrow> snpresps2 T = [] \<and> snps2 T = [] \<and> reqresps1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i791: "(nextDTHDataFrom 0 T \<and> HSTATE MD T \<and> nextReqIs RdOwn T 0 \<longrightarrow> CSTATE IMAD T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i792: "(nextDTHDataFrom 1 T \<and> HSTATE MD T \<and> nextReqIs RdOwn T 1 \<longrightarrow> CSTATE IMAD T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i793: "(HSTATE SAD T \<and> nextSnpRespIs RspSFwdM T 0 \<longrightarrow> \<not> CSTATE Modified T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i794: "(HSTATE SAD T \<and> nextSnpRespIs RspSFwdM T 1 \<longrightarrow> \<not> CSTATE Modified T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i795: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE Modified T 1 \<and> \<not> CSTATE Shared T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i796: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Shared T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i797: "(HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> dthdatas2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i798: "(HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> dthdatas1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i799: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i800: "(HSTATE SharedM T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i801: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i802: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i803: "(HSTATE MA T \<and> snpresps1 T \<noteq> [] \<longrightarrow> htddatas1 T = [] \<or> CSTATE ISDI T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i804: "(HSTATE MA T \<and> snpresps2 T \<noteq> [] \<longrightarrow> htddatas2 T = [] \<or> CSTATE ISDI T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i805: "(HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> (CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i806: "(HSTATE MB T \<longrightarrow> \<not> CSTATE ISD T 0 \<and> \<not> CSTATE ISD T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i807: "(HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> CSTATE Invalid T 0 \<or> CSTATE ISAD T 0 \<or> CSTATE IMAD T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i808: "(HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> CSTATE Invalid T 1 \<or> CSTATE ISAD T 1 \<or> CSTATE IMAD T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i809: "(HSTATE MB T \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i810: "(HSTATE MB T \<longrightarrow> snpresps1 T = [] \<and> snpresps2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i811: "(HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i812: "(HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i813: "(HSTATE MB T \<longrightarrow> \<not> CSTATE SIA T 0 \<and> \<not> CSTATE SIA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i814: "(HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextReqIs RdOwn T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i815: "(HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextReqIs RdOwn T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i816: "(HSTATE MB T \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE ISA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i817: "(CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<and> HSTATE SB T \<longrightarrow> \<not> CSTATE IIA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i818: "(CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<and> HSTATE SB T \<longrightarrow> \<not> CSTATE IIA T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i819: "(HSTATE IB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextReqIs DirtyEvict T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i820: "(HSTATE IB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextReqIs DirtyEvict T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i821: "(HSTATE SB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i822: "(HSTATE SB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i823: "(HSTATE SB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i824: "(HSTATE SB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1)"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i825: "(HSTATE ID T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i826: "(HSTATE ID T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i827: "(CSTATE Modified T 0 \<longrightarrow> \<not> nextReqIs RdOwn T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i828: "(CSTATE Modified T 1 \<longrightarrow> \<not> nextReqIs RdOwn T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i829: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE ISD T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i830: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE ISD T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i831: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> (CSTATE ISAD T 1 \<and> nextGOPending T 1)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i832: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> (CSTATE ISAD T 0 \<and> nextGOPending T 0)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i833: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> (CSTATE IMA T 1 \<and> nextGOPending T 1)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i834: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> (CSTATE IMA T 0 \<and> nextGOPending T 0)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i835: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> (CSTATE ISA T 1 \<and> nextGOPending T 1)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i836: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> (CSTATE ISA T 0 \<and> nextGOPending T 0)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i837: "((CSTATE ISAD T 0 \<and> nextGOPending T 0) \<or> CSTATE ISA T 0 \<or> ( nextHTDDataPending T 0) \<or> CSTATE Shared T 0 \<longrightarrow> \<not> (CSTATE IMA T 1 \<and> nextGOPending T 1)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i838: "((CSTATE ISAD T 1 \<and> nextGOPending T 1) \<or> CSTATE ISA T 1 \<or> ( nextHTDDataPending T 1) \<or> CSTATE Shared T 1 \<longrightarrow> \<not> (CSTATE IMA T 0 \<and> nextGOPending T 0)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i839: "(HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> snps2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i840: "(HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> snps1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i841: "(HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE MIA T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i842: "(HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE MIA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i843: "(HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE SIA T 0 \<and> \<not> CSTATE SIA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i844: "(HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE SIA T 1 \<and> \<not> CSTATE SIA T 0)  "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i845: "(CSTATE Modified T 0 \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> (htddatas2 T = [] \<or> CSTATE ISDI T 1)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i846: "(CSTATE Modified T 1 \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0 \<and> (htddatas1 T = [] \<or> CSTATE ISDI T 0)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i847: "(CSTATE Modified T 0 \<longrightarrow> \<not> CSTATE SMAD T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i848: "(CSTATE Modified T 1 \<longrightarrow> \<not> CSTATE SMAD T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i849: "(CSTATE Modified T 0 \<longrightarrow> snpresps1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i850: "(CSTATE Modified T 1 \<longrightarrow> snpresps2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i851: "(CSTATE SMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> (CSTATE ISAD T 1 \<and> nextGOPending T 1)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i852: "(CSTATE SMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> (CSTATE ISAD T 0 \<and> nextGOPending T 0)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i853: "(CSTATE SMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE ISA T 1 \<and> \<not> CSTATE Shared T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i854: "(CSTATE SMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE Shared T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i855: "(CSTATE SMA T 0 \<and> nextGOPending T 0 \<longrightarrow> htddatas2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i856: "(CSTATE SMA T 1 \<and> nextGOPending T 1 \<longrightarrow> htddatas1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i857: "(CSTATE SMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE IMA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i858: "(CSTATE SMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE IMA T 0)  "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i859: "(CSTATE Invalid T 0 \<longrightarrow> snps1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i860: "(CSTATE Invalid T 1 \<longrightarrow> snps2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i861: "(HSTATE SD T \<and> nextDTHDataFrom 0 T \<longrightarrow> CSTATE ISD T 1 \<or> CSTATE ISAD T 1 \<and> nextGOPending T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i862: "(HSTATE SD T \<and> nextDTHDataFrom 1 T \<longrightarrow> CSTATE ISD T 0 \<or> CSTATE ISAD T 0 \<and> nextGOPending T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i863: "(HSTATE SAD T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i864: "(HSTATE SAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i865: "(CSTATE SMAD T 0 \<and> nextGOPending T 0 \<and> nextHTDDataPending T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T \<and> CSTATE ISAD T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i866: "(CSTATE SMAD T 1 \<and> nextGOPending T 1 \<and> nextHTDDataPending T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T \<and> CSTATE ISAD T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i867: "(CSTATE SMAD T 0 \<and> nextGOPending T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> nextReqIs DirtyEvict T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i868: "(CSTATE SMAD T 1 \<and> nextGOPending T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> nextReqIs DirtyEvict T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i869: "(CSTATE SMAD T 0 \<and> nextGOPending T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i870: "(CSTATE SMAD T 1 \<and> nextGOPending T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i871: "(CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<and> HSTATE IB T \<longrightarrow> \<not> nextReqIs DirtyEvict T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i872: "(CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<and> HSTATE IB T \<longrightarrow> \<not> nextReqIs DirtyEvict T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i873: "(CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<and> HSTATE SB T \<longrightarrow> \<not> CSTATE MIA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i874: "(CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<and> HSTATE SB T \<longrightarrow> \<not> CSTATE MIA T 0)"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i875: "(HSTATE InvalidM T \<and> nextReqIs DirtyEvict T 0 \<longrightarrow> CSTATE IIA T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i876: "(HSTATE InvalidM T \<and> nextReqIs DirtyEvict T 1 \<longrightarrow> CSTATE IIA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i877: "(HSTATE InvalidM T \<longrightarrow> (\<not> CSTATE SIA T 0 \<or> nextGOPendingIs GO_WritePullDrop T 0) \<and> (\<not> CSTATE SIA T 1 \<or> nextGOPendingIs GO_WritePullDrop T 1)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i878: "(HSTATE MA T  \<and> nextSnpRespIs RspIFwdM T 0 \<longrightarrow> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i879: "(HSTATE MA T  \<and> nextSnpRespIs RspIFwdM T 1 \<longrightarrow> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0))  "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i880: "(HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> (CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i881: "(HSTATE MB T \<and> CSTATE IIA T 0 \<longrightarrow> (CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i882: "(HSTATE MB T \<and> CSTATE IIA T 1 \<longrightarrow> (CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i883: "length (dthdatas1 T) \<le> 1"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i884: "length (dthdatas2 T) \<le> 1"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i885: "(HSTATE IB T \<and> CSTATE IIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> \<not> nextReqIs DirtyEvict T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i886: "(HSTATE IB T \<and> CSTATE IIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> \<not> nextReqIs DirtyEvict T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i887: "(HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i888: "(HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i889: "(HSTATE MA T \<and> snpresps1 T \<noteq> [] \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i890: "(HSTATE MA T \<and> snpresps2 T \<noteq> [] \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1)  "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i891: "(CSTATE IMAD T 0 \<and> nextGOPending T 0 \<and> HSTATE MD T \<longrightarrow> snpresps1 T = [] \<and> snps1 T = [] \<and> reqresps2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i892: "(CSTATE IMAD T 1 \<and> nextGOPending T 1 \<and> HSTATE MD T \<longrightarrow> snpresps2 T = [] \<and> snps2 T = [] \<and> reqresps1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i893: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> (htddatas2 T = [] \<or> CSTATE ISDI T 1)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i894: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0 \<and> (htddatas1 T = [] \<or> CSTATE ISDI T 0)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i895: "(CSTATE SMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> (htddatas2 T = [] \<or> CSTATE ISDI T 1)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i896: "(CSTATE SMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0 \<and> (htddatas1 T = [] \<or> CSTATE ISDI T 0)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i897: "(CSTATE Modified T 0 \<longrightarrow> dthdatas1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i898: "(CSTATE Modified T 1 \<longrightarrow> dthdatas2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i899: "(nextSnpRespIs RspIHitSE T 0 \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i900: "(nextSnpRespIs RspIHitSE T 1 \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i901: "(CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> CSTATE SMAD T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i902: "(CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> CSTATE SMAD T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i903: "(CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> CSTATE SMAD T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i904: "(CSTATE SMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> CSTATE SMAD T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i905: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE SMAD T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i906: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE SMAD T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i907: "(CSTATE SMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE SMAD T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i908: "(CSTATE SMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE SMAD T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i909: "(CSTATE IMAD T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE SMAD T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i910: "(CSTATE IMAD T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE SMAD T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i911: "(HSTATE MD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE SMAD T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i912: "(HSTATE MD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE SMAD T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i913: "(CSTATE SMAD T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE SMAD T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i914: "(CSTATE SMAD T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE SMAD T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i915: "(HSTATE InvalidM T \<longrightarrow> \<not> CSTATE SMAD T 1 \<and> \<not> CSTATE SMAD T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i916: "(HSTATE IB T \<longrightarrow> \<not> CSTATE SMAD T 1 \<and> \<not> CSTATE SMAD T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i917: "(HSTATE ID T \<longrightarrow> \<not> CSTATE SMAD T 1 \<and> \<not> CSTATE SMAD T 0)  "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i918: "(HSTATE MA T \<and> nextSnpRespIs RspIHitSE T 0 \<longrightarrow> \<not> nextReqIs DirtyEvict T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i919: "(HSTATE MA T \<and> nextSnpRespIs RspIHitSE T 1 \<longrightarrow> \<not> nextReqIs DirtyEvict T 1)"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i920: "(CSTATE Modified T 0 \<longrightarrow> htddatas2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i921: "(CSTATE Modified T 1 \<longrightarrow> htddatas1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i922: "(HSTATE ModifiedM T \<longrightarrow> snps1 T = [] \<and> snps2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i923: "(CSTATE SMAD T 0 \<and> nextHTDDataPending T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i924: "(CSTATE SMAD T 1 \<and> nextHTDDataPending T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i925: "(CSTATE SMAD T 1 \<and> HSTATE MA T \<and> nextSnpRespIs RspIFwdM T 0 \<longrightarrow> \<not> nextReqIs DirtyEvict T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i926: "(CSTATE SMAD T 0 \<and> HSTATE MA T \<and> nextSnpRespIs RspIFwdM T 1 \<longrightarrow> \<not> nextReqIs DirtyEvict T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i927: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i928: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i929: "(CSTATE SIAC T 0 \<longrightarrow> \<not> nextHTDDataPending T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i930: "(CSTATE SIAC T 1 \<longrightarrow> \<not> nextHTDDataPending T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i931: "((CSTATE SIAC T 0 \<and> nextGOPending T 0 \<and> nextGOPendingState Invalid T 0) --> snps2 T = [] \<and> snpresps2 T = [] \<and> htddatas1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i932: "((CSTATE SIAC T 1 \<and> nextGOPending T 1 \<and> nextGOPendingState Invalid T 1) --> snps1 T = [] \<and> snpresps1 T = [] \<and> htddatas2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i933: "((CSTATE SIAC T 0 \<and> nextGOPending T 0 \<and> nextGOPendingState Invalid T 0) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i934: "((CSTATE SIAC T 1 \<and> nextGOPending T 1 \<and> nextGOPendingState Invalid T 1) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i935: "((CSTATE SIAC T 0 \<and> nextGOPending T 0 \<and> nextGOPendingState Invalid T 0) \<and> HSTATE MD T \<longrightarrow> dthdatas1 T \<noteq> []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i936: "((CSTATE SIAC T 1 \<and> nextGOPending T 1 \<and> nextGOPendingState Invalid T 1) \<and> HSTATE MD T \<longrightarrow> dthdatas2 T \<noteq> []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i937: "((CSTATE SIAC T 0 \<and> nextGOPending T 0 \<and> nextGOPendingState Invalid T 0) \<and> HSTATE MA T \<longrightarrow>(CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i938: "((CSTATE SIAC T 1 \<and> nextGOPending T 1 \<and> nextGOPendingState Invalid T 1) \<and> HSTATE MA T \<longrightarrow>(CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i939: "((CSTATE SIAC T 0 \<and> nextGOPending T 0 \<and> nextGOPendingState Invalid T 0) --> snps1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i940: "((CSTATE SIAC T 1 \<and> nextGOPending T 1 \<and> nextGOPendingState Invalid T 1) --> snps2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i941: "((CSTATE SIAC T 0 \<and> nextGOPending T 0 \<and> nextGOPendingState Invalid T 0) --> reqs1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i942: "((CSTATE SIAC T 1 \<and> nextGOPending T 1 \<and> nextGOPendingState Invalid T 1) --> reqs2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i943: "(HSTATE MA T \<and> nextSnpRespIs RspIFwdM T 0 \<longrightarrow> \<not> nextHTDDataPending T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i944: "(HSTATE MA T \<and> nextSnpRespIs RspIFwdM T 1 \<longrightarrow> \<not> nextHTDDataPending T 1)"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i945: "(HSTATE SB T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i946: "(nextReqIs CleanEvictNoData T 0 \<longrightarrow> CSTATE SIAC T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i947: "(nextReqIs CleanEvictNoData T 1 \<longrightarrow> CSTATE SIAC T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i948: "(nextSnpRespIs RspIHitSE T 0 \<longrightarrow> \<not> nextDTHDataFrom 0 T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i949: "(nextSnpRespIs RspIHitSE T 1 \<longrightarrow> \<not> nextDTHDataFrom 1 T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i950: "(nextSnpRespIs RspIFwdM T 0 \<longrightarrow> \<not> nextReqIs CleanEvictNoData T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i951: "(nextSnpRespIs RspIFwdM T 1 \<longrightarrow> \<not> nextReqIs CleanEvictNoData T 1)  "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i952: "(CSTATE SMA T 0 \<and> nextSnoopIs SnpData T 0 \<and> nextGOPending T 0 \<longrightarrow> HSTATE SAD T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i953: "(CSTATE SMA T 1 \<and> nextSnoopIs SnpData T 1 \<and> nextGOPending T 1 \<longrightarrow> HSTATE SAD T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i954: "((CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePullDrop T 0) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or>(CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i955: "((CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePullDrop T 1) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or>(CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0)   "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i956: "((CSTATE SIAC T 0 \<and> nextGOPendingIs GO T 0 \<and> nextGOPendingState Invalid T 0 \<and> \<not> CSTATE IIA T 1 \<and> GTS T 1) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or>(CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i957: "((CSTATE SIAC T 1 \<and> nextGOPendingIs GO T 1 \<and> nextGOPendingState Invalid T 1 \<and> \<not> CSTATE IIA T 0 \<and> GTS T 0) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or>(CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0)   "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i958: "((CSTATE SIAC T 0 \<and> nextGOPendingIs GO T 0 \<and> nextGOPendingState Invalid T 0 \<and> \<not> CSTATE IIA T 1 \<and> GTS T 1) \<and> HSTATE MD T \<longrightarrow> dthdatas1 T \<noteq> []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i959: "((CSTATE SIAC T 1 \<and> nextGOPendingIs GO T 1 \<and> nextGOPendingState Invalid T 1 \<and> \<not> CSTATE IIA T 0 \<and> GTS T 0) \<and> HSTATE MD T \<longrightarrow> dthdatas2 T \<noteq> [])  "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i960: "((CSTATE SIAC T 0 \<and> nextGOPendingIs GO T 0 \<and> nextGOPendingState Invalid T 0 \<and> \<not> CSTATE IIA T 1 \<and> GTS T 1) \<and> HSTATE MA T \<longrightarrow> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i961: "((CSTATE SIAC T 1 \<and> nextGOPendingIs GO T 1 \<and> nextGOPendingState Invalid T 1 \<and> \<not> CSTATE IIA T 0 \<and> GTS T 0) \<and> HSTATE MA T \<longrightarrow> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i962: "(HSTATE SD T \<and> nextDTHDataFrom 0 T \<longrightarrow> snps2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i963: "(HSTATE SD T \<and> nextDTHDataFrom 1 T \<longrightarrow> snps1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i964: "(HSTATE SD T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqresps1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i965: "(HSTATE SD T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqresps2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i966: "(HSTATE ID T \<and> nextDTHDataFrom 0 T \<longrightarrow> (\<not> CSTATE SIA T 1 \<or> nextGOPendingIs GO_WritePullDrop T 1) ) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i967: "(HSTATE ID T \<and> nextDTHDataFrom 1 T \<longrightarrow> (\<not> CSTATE SIA T 0 \<or> nextGOPendingIs GO_WritePullDrop T 0) ) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i968: "(CSTATE MIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<and> HSTATE ID T \<longrightarrow> (\<not> CSTATE SIA T 1 \<or> nextGOPendingIs GO_WritePullDrop T 1)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i969: "(CSTATE MIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<and> HSTATE ID T \<longrightarrow> (\<not> CSTATE SIA T 0 \<or> nextGOPendingIs GO_WritePullDrop T 0))  "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i970: "(HSTATE SAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i202: "nextEvict T 0"
using C_msg_P_same_def i1x i2x i314
by presburger
have i205: "\<not> nextReqIs RdShared T 0"
using C_msg_P_same_def i1x i2x  i315
by presburger
have i206: "\<not> nextReqIs RdOwn T 0"
by (metis i202 i339 i349 i392 i517 nextStore_nextEvict_exclusive)
have i207: "\<not> nextHTDDataPending  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
using htddatas1_SIAGO_WritePull
using i1x i316 nextHTDDataPending_def
by presburger
have i208: "snps1 T = [] \<and> snps2 T = []"
by (metis C_msg_P_same_def assms i318 i316 nextSnoopPending_def)
have i209: "\<not> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
using empty_no_snoop i208 snps1_SIAGO_WritePull
by presburger
have i210: "reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
using i85 reqresps1_SIAGO_WritePull
by blast
have i211: "\<not> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
using i210 nextGOPending_def nextReqRespIs.simps(1)
by presburger
have i212: "\<not> nextSnoopPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
using i208 nextSnoopPending_def snps1_SIAGO_WritePull
by presburger
have i213: " snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
by (metis i212 nextSnoopPending_def)
have i214: " snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
using i208 snps2_SIAGO_WritePull
by presburger
have i215: " reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
using i210
by blast
have i2160: "CSTATE Invalid (T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid]) 0"
using SharedSnpInv'_CSTATE_invariant5
by presburger
have i216: "CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
using SIAGO_WritePull_CSTATE_aux i2160
by blast
have i217: "\<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 "
using CSTATE_def MESI_State.simps(6) i216
by presburger
have i218: "HSTATE ModifiedM T \<longrightarrow> \<not> nextReqIs RdShared T 1"
using i2x i313
by fastforce
have i219: "HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow>\<not>nextReqIs RdShared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
using i218 nextReqIs_SIAGO_WritePull_IMAD_invariant2
using HSTATE_SIAGO_WritePull_invariant
by presburger
have i221: "HSTATE IB T \<or> HSTATE SB T \<or> HSTATE MB T"
using i1x i2x i319
by blast
have i2201: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> 
HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> 
HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) "
using HSTATE_SIAGO_WritePull_invariant i221
by presburger
have i220: "\<not>HSTATE SA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
using i2201
by force
have i222: "\<not>HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
using i2201
by force
have i223: "\<not>HSTATE SD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
using i2201
by force
have i224: "\<not>HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
using i2201
by force
have i225: "\<not>HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
using i2201
by force
have i249: "\<not> (HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and>
  nextReqIs RdShared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1)"
using HSTATE_SIAGO_WritePull_invariant H_C_state_msg_oppo_def SWMR_state_machine_def i41 nextReqIs_SIAGO_WritePull_IMAD_invariant2 i1x
using i219
by force
have i250: "(HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and>
  nextReqIs RdShared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow>
  \<not> nextDTHDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0)"
using i249
by blast
have i2520: "(HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and>
  nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow>
  CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) = (HSTATE ModifiedM T \<and> nextReqIs DirtyEvict T 1 \<longrightarrow>
   CSTATE MIA T 1)"
using CSTATE_SIAGO_WritePull_otherside_invariant2 HSTATE_SIAGO_WritePull_invariant nextReqIs_SIAGO_WritePull_IMAD_invariant2
by presburger
have i252: "(HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and>
  nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow>
  CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1)"
by (metis CSTATE_otherside_rule_3 HOST_State.distinct(35) HOST_State.distinct(37) HOST_State.distinct(83) HSTATE_SIAGO_WritePull_invariant HSTATE_invariant3 i1x i2160 i221 i2520 i813)
have i253: "reqs1 T = []"
using i2x i94
by fastforce
have i254: "reqs1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
using i253 reqs1_SIAGO_WritePull
by presburger
have i255: "\<not> nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
by (metis i254 nextReqIs_def startsWithProp.simps(1) startsWithReq_def)
have i256: " (CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow>
  \<not> nextReqIs RdShared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) = (CSTATE MIA T 1 \<longrightarrow> \<not> nextReqIs RdShared T 1)"
using CSTATE_SIAGO_WritePull_otherside_invariant2 nextReqIs_def reqs1_SIAGO_WritePull reqs2_SIAGO_WritePull
by presburger
have i257: "(CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and>
  nextGOPendingIs GO_WritePullDrop ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow>
  nextEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) = 
  (CSTATE IIA T 1 \<and> nextGOPendingIs GO_WritePullDrop T 1 \<longrightarrow> nextEvict T 1)"
using CSTATE_SIAGO_WritePull_otherside_invariant2 SIAGO_WritePull_nextEvict_otherside SIAGO_WritePull_nextGOPendingIs_otherside
by presburger
have i258: " (CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and>
  nextGOPendingIs GO_WritePullDrop ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow>
  \<not> nextReqIs RdShared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) = 
  (CSTATE IIA T 1 \<and> nextGOPendingIs GO_WritePullDrop T 1 \<longrightarrow> \<not> nextReqIs RdShared T 1)"
using CSTATE_SIAGO_WritePull_otherside_invariant2 SIAGO_WritePull_nextGOPendingIs_otherside nextReqIs_SIAGO_WritePull_IMAD_invariant2
by presburger
have "\<not> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
using i206 nextReqIs_SIAGO_WritePull_IMAD_invariant1
by blast
have i259: "nextLoad ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 = nextLoad T 1"
apply(case_tac "program1 T")
by simp+
have i260: "(reqs2 (T\<lparr>buffer1 := Some m\<rparr> [0 s= Invalid] [0 -=reqresp] [Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<longrightarrow>
   htddatas2 (T\<lparr>buffer1 := Some m\<rparr> [0 s= Invalid] [0 -=reqresp] [Dev1 +=d2hd dthd] [ -=i 0]) = []) = 
   (reqs2 T \<noteq> [] \<longrightarrow> htddatas2 T = []) "
using htddatas2_SIAGO_WritePull reqs2_SIAGO_WritePull
by presburger
have aux_r113: "dthdatas1 T = []"
by (metis C_msg_P_same_def assms i321 nextDTHDataPending_def)
have aux3_r113: "dthdatas1 (T\<lparr>buffer1 := Some m\<rparr> [0 s= Invalid] [0 -=reqresp]) = dthdatas1 T"
by simp
have aux2_r113: "dthdatas1 (T\<lparr>buffer1 := Some m\<rparr> [0 s= Invalid] [0 -=reqresp]) = []"
using aux3_r113 aux_r113
by presburger
have aux4_r113: "length (dthdatas1 (T\<lparr>buffer1 := Some m\<rparr> [0 s= Invalid] [0 -=reqresp] [Dev1 +=d2hd dthd])) \<le> 1"
using SharedSnpInv'_dthdatas1 aux2_r113
by presburger
have aux5_r113: "(dthdatas1 (T\<lparr>buffer1 := Some m\<rparr> [0 s= Invalid] [0 -=reqresp] [Dev1 +=d2hd dthd])) = (dthdatas1 (T\<lparr>buffer1 := Some m\<rparr> [0 s= Invalid] [0 -=reqresp] [Dev1 +=d2hd dthd] [ -=i 0]))"
using dthdatas1_perform_instr
by blast
have aux_103p: " \<not> (HSTATE ModifiedM T \<and> nextReqIs RdOwn T 1)"
using i2x i313
by linarith
have aux1_103p: "(HSTATE ModifiedM T \<and> nextReqIs RdOwn T 1) = 
((HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])  \<and> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1))"
using HSTATE_SIAGO_WritePull_invariant nextReqIs_def reqs2_SIAGO_WritePull
by presburger
have aux_r173: "\<not>(HSTATE SharedM T \<and> nextReqIs RdOwn T 1)"
apply simp
using HOST_State.distinct(103) HOST_State.distinct(105) HOST_State.distinct(107) HSTATE_def i221
by presburger
have aux_r175: "\<not>(HSTATE SharedM T \<and> nextReqIs RdShared T 1)"
using i2x i307
by blast
have aux192:  "\<not> nextDTHDataFrom 1 T "
using i1x i2x i322
by fastforce
have g302aux: "snpresps1 T = []"
by (metis assms i343 reqresps_empty_noGOPendingIs1)
have aux542: "dthdatas2 T = []"
by (smt (verit) aux192 nextDTHDataFrom_def zero_neq_one)
show ?thesis
unfolding SWMR_state_machine_def
proof (intro conjI)
show goal1: "SWMR ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (smt (verit) CSTATE_inequality_invariant CSTATE_various_forms2 MESI_State.distinct(95) i216 i217) done
show goal2: "C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (smt (verit) i207 i217) done
show goal3: "H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (smt (verit) i217 i223) done
show goal4: "H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (smt (verit) i217 i222) done
show goal5: "C_msg_P_oppo ISAD nextGOPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (smt (verit) i211 i217) done
show goal6: "H_msg_P_same SharedM (nextReqIs RdShared) (\<lambda>T i. \<not> CSTATE Modified T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i800 nextGOPendingIs_XIAGOWP_otherside1 remove_instr_HSTATE) done
show goal7: "H_msg_P_oppo SharedM (nextReqIs RdShared) (\<lambda>T i. \<not> CSTATE Modified T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (smt (verit) i217 i254 reqs1_empty_not_nextReqIs_general_invariant) done
show goal8: "H_msg_P_same ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> CSTATE Modified T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (smt (verit) i217 i219) done
show goal9: "H_msg_P_oppo ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> nextDTHDataPending T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (smt (verit) i250 i254 reqs1_empty_not_nextReqIs_general_invariant) done
show goal10: "H_msg_P_oppo ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> nextSnpRespIs RspIFwdM T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (smt (verit) i219 i254 reqs1_empty_not_nextReqIs_general_invariant) done
show goal11: "H_msg_P_same ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> nextSnpRespIs RspIFwdM T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (smt (verit) i219 i254 reqs1_empty_not_nextReqIs_general_invariant) done
show goal12: "C_H_state IMAD (nextReqIs RdOwn) Modified SD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (smt (verit) i217 i223) done
show goal13: "C_H_state IMAD (nextReqIs RdOwn) Modified SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (smt (verit) i217 i222) done
show goal14: "C_H_state IMAD (nextReqIs RdOwn) Modified SA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (smt (verit) \<open>\<not> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0\<close> i217) done
show goal15: "C_H_state Invalid nextStore Modified SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (smt (verit) i217 i222) done
show goal16: "C_H_state Invalid nextStore Modified SA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (smt (verit) i217 i220) done
show goal17: "C_H_state Invalid nextStore Modified SD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (smt (verit) i217 i223) done
show goal18: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i800 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal19: "HSTATE SD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i223) done
show goal20: "HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i225) done
show goal21: "C_msg_not RdShared IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (metis CSTATE_SIAGO_WritePull_IMAD_invariant CSTATE_inequality_invariant CSTATE_otherside_rule_4_0 CSTATE_remove_op C_msg_not_def MESI_State.distinct(147) SharedSnpInv'_MAD_CSTATE_invariant5 i216 i2160 i25 i254 nextGOPendingIs_general_rule_3_0 nextReqIs_SIAGO_WritePull_IMAD_invariant2 nextReqIs_not_various_forms1 reqs1_remove_op) done
show goal22: "C_msg_not RdShared Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (metis CSTATE_SIAGO_WritePull_IMAD_invariant CSTATE_otherside_rule_4_0 CSTATE_remove_op C_msg_not_def SharedSnpInv'_MAD_CSTATE_invariant5 i2160 i254 i26 nextGOPendingIs_general_rule_3_0 nextReqIs_SIAGO_WritePull_IMAD_invariant2 nextReqIs_not_various_forms1 reqs1_remove_op) done
show goal23: "H_msg_P_same ModifiedM (nextReqIs DirtyEvict) (\<lambda>T i. CSTATE MIA T i \<or> CSTATE IIA T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (smt (verit) i252 i255) done
show goal24: "C_msg_P_host MIA (nextGOPendingIs GO_WritePull) (\<lambda>T. \<not> HSTATE ModifiedM T) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i313 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal25: "C_msg_P_same MIA (nextGOPendingIs GO_WritePull) nextEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (metis CSTATE_inequality_invariant Invalid_not_eq_MIA SIAGO_WritePull_nextEvict_otherside SIAGO_WritePull_nextGOPendingIs_otherside assms i216 i2160 i582 nextGOPendingIs_general_rule_3_0) done
show goal26: "C_msg_P_host MIA (nextGOPendingIs GO_WritePull) (HSTATE ID) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (metis CSTATE_inequality_invariant CSTATE_otherside_rule_4_0 CSTATE_remove_op HSTATE_SIAGO_WritePull_invariant Invalid_not_eq_MIA SharedSnpInv'_MAD_CSTATE_invariant5 assms i216 i2160 i221 i773 i813 i945 nextGOPendingIs_general_rule_3_0) done
show goal27: "C_state_not MIA RdShared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (smt (verit) CSTATE_inequality_invariant C_state_not_def Invalid_not_eq_MIA i216 i256 i31) done
show goal28: "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) nextEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (smt (verit) CSTATE_inequality_invariant C_msg_P_same_def MESI_State.distinct(163) i216 i257 i32) done
show goal29: "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextReqIs RdShared T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (smt (verit) CSTATE_inequality_invariant C_msg_state_def MESI_State.distinct(163) MESI_State.distinct(277) i216 i258 i47) done
show goal30: "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextDTHDataPending T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (metis CSTATE_SIAGO_WritePull_IMAD_invariant SIAGO_WritePull_nextHTDDataPending_otherside assms aux542 i215 i2160 i582 nextDTHDataPending_def nextDTHDataPending_other_rule_7_0 reqresps1_SIAGO_WritePull_aux1 reqresps1_remove_op reqresps_empty_noGOPendingIs1) done
show goal31: "H_C_state_msg_same ModifiedM Modified (\<lambda>T i. \<not> nextReqIs RdShared T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (smt (verit) i217 i219) done
show goal32: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) nextEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (metis SIAGO_WritePull_nextEvict_otherside SIAGO_WritePull_nextGOPendingIs_otherside assms i215 i2160 i582 nextGOPendingIs_general_rule_3_0 reqresps1_SIAGO_WritePull_aux1 reqresps1_remove_op reqresps_empty_noGOPendingIs1) done
show goal33: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextReqIs RdShared T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (metis CSTATE_SIAGO_WritePull_IMAD_invariant CSTATE_inequality_invariant CSTATE_otherside_rule_4_0 CSTATE_remove_op C_msg_state_def MESI_State.distinct(277) SharedSnpInv'_MAD_CSTATE_invariant5 i215 i2160 i254 i47 nextGOPendingIs_general_rule_3_0 nextReqIs_SIAGO_WritePull_IMAD_invariant2 nextReqIs_not_various_forms1 reqresps1_SIAGO_WritePull_aux1 reqresps1_remove_op reqresps_empty_noGOPendingIs1 reqs1_remove_op) done
show goal34: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextDTHDataPending T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (metis CSTATE_SIAGO_WritePull_IMAD_invariant SIAGO_WritePull_nextHTDDataPending_otherside assms aux542 i215 i2160 i582 nextDTHDataPending_def nextDTHDataPending_other_rule_7_0 reqresps1_SIAGO_WritePull_aux1 reqresps1_remove_op reqresps_empty_noGOPendingIs1) done
show goal35: "H_C_state_msg_oppo ModifiedM IIA (\<lambda>T i. \<not> nextReqIs RdShared T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (smt (verit) i219 i254 reqs1_empty_not_nextReqIs_general_invariant) done
show goal36: "C_msg_P_host Shared (nextSnoopIs SnpInv) (HSTATE MA) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (smt (verit) empty_no_snoop2 i209 i214) done
show goal37: "C_msg_state RdShared ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (metis CSTATE_SIAGO_WritePull_IMAD_invariant CSTATE_otherside_rule_4_0 CSTATE_remove_op C_msg_state_def SharedSnpInv'_MAD_CSTATE_invariant5 i2160 i254 i47 nextGOPendingIs_general_rule_3_0 nextReqIs_SIAGO_WritePull_IMAD_invariant2 nextReqIs_not_various_forms1 reqs1_remove_op) done
show goal38: "C_not_C_msg Modified ISAD nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (smt (verit) i211 i217) done
show goal39: "C_msg_P_same Invalid nextStore (\<lambda>T i. \<not> nextHTDDataPending T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (metis CSTATE_SIAGO_WritePull_IMAD_invariant CSTATE_otherside_rule_4_0 CSTATE_remove_op HTDDataPending_htddatas_invariant2 SIAGO_WritePull_nextHTDDataPending_real SharedSnpInv'_MAD_CSTATE_invariant5 i207 i2160 i614old nextStore_otherside_rule_1_0) done
show goal40: "C_msg_P_same Invalid nextStore (\<lambda>T i. \<not> nextSnoopIs SnpInv T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (smt (verit) empty_no_snoop_variant2 i209 i214) done
show goal41: "C_msg_P_same ISAD nextGOPending (\<lambda>T i. \<not> nextReqIs RdShared T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
unfolding C_msg_P_same_def
proof (intro conjI)
show goal1: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> nextReqIs RdShared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply (smt (verit) i211)
done
show goal2: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> nextReqIs RdShared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply (metis CSTATE_otherside_rule_4_0 CSTATE_remove_op C_msg_P_same_def SharedSnpInv'_MAD_CSTATE_invariant5 goal31 i2160 i52 nextGOPending_DeviceSIAGO_WritePull nextGOPending_yes_reqresp_rule_3_1 nextReqIs_SIAGO_WritePull_IMAD_invariant2)
done
qed
show goal42: "snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<longrightarrow> reqs1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i214) done
show goal43: "snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<longrightarrow> reqs2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i213) done
show goal44: "length (reqs1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])) \<le> 1"
apply  (insert assms) apply (smt (verit) aux_r113 i254 i883) done
show goal45: "length (reqs2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])) \<le> 1"
apply  (insert assms) apply (metis i2160 i58 nextGOPendingIs_general_rule_3_0 reqs2_SIAGO_WritePull reqs2_remove_op) done
show goal46: "length (snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])) \<le> 1"
apply  (insert assms) apply (smt (verit) aux_r113 i214 i883) done
show goal47: "length (snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])) \<le> 1"
apply  (insert assms) apply (smt (verit) aux_r113 i213 i883) done
show goal48: "C_msg_P_same Shared (nextSnoopIs SnpInv) (\<lambda>T i. \<not> nextHTDDataPending T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (smt (verit) empty_no_snoop_variant2 i207 i214) done
show goal49: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextSnoopPending T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (smt (verit) i212 i213 i214 nextSnoopPending_def) done
show goal50: "C_msg_P_oppo Invalid nextStore (\<lambda>T i. \<not> nextSnoopPending T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (smt (verit) i212 i213 i214 nextSnoopPending_def) done
show goal51: "CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis HTDDataPending_htddatas_invariant1 assms htddatas1_general_rule_10_0 htddatas1_general_rule_12_0 i207 i214 i215 i2160 i316 snpresps2_SIAGO_WritePull snpresps2_remove_op snps2_SIAGO_WritePull) done
show goal52: "CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis CSTATE_otherside_rule_4_0 CSTATE_remove_op SharedSnpInv'_MAD_CSTATE_invariant5 g302aux htddatas2_SIAGO_WritePull htddatas2_remove_op i213 i2160 i382 i614old nextGOPendingIs_general_rule_3_0 reqresps2_SIAGO_WritePull reqresps2_remove_op snpresps1_SIAGO_WritePull snpresps1_remove_op snps1_SIAGO_WritePull) done
show goal53: "CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(95) i216) done
show goal54: "CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis CSTATE_otherside_rule_4_0 CSTATE_remove_op SharedSnpInv'_MAD_CSTATE_invariant5 g302aux htddatas2_SIAGO_WritePull htddatas2_remove_op i213 i2160 i616old nextGOPendingIs_general_rule_3_0 reqresps2_SIAGO_WritePull reqresps2_remove_op snpresps1_SIAGO_WritePull snpresps1_remove_op snps1_SIAGO_WritePull) done
show goal55: "CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(163) i216) done
show goal56: "CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis CSTATE_otherside_rule_4_0 CSTATE_remove_op SharedSnpInv'_MAD_CSTATE_invariant5 g302aux htddatas2_SIAGO_WritePull htddatas2_remove_op i213 i2160 i618old nextGOPendingIs_general_rule_3_0 snpresps1_SIAGO_WritePull snpresps1_remove_op snps1_SIAGO_WritePull) done
show goal57: "CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> reqs1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i254) done
show goal58: "CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> reqs2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis CSTATE_otherside_rule_4_0 CSTATE_remove_op SharedSnpInv'_MAD_CSTATE_invariant5 i2160 i69 nextGOPendingIs_general_rule_3_0 reqs2_SIAGO_WritePull reqs2_remove_op) done
show goal59: "CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> reqs1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i254) done
show goal60: "CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> reqs2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis CSTATE_otherside_rule_4_0 CSTATE_remove_op SharedSnpInv'_MAD_CSTATE_invariant5 i2160 i71 nextGOPendingIs_general_rule_3_0 reqs2_SIAGO_WritePull reqs2_remove_op) done
show goal61: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i217) done
show goal62: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i217) done
show goal63: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant HSTATE_rule_1 assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i313 remove_instr_HSTATE) done
show goal64: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i313 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal65: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> nextLoad ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(139) i216) done
show goal66: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> nextLoad ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis CSTATE_otherside_rule_4_0 CSTATE_remove_op SharedSnpInv'_MAD_CSTATE_invariant5 i2160 i259 i752old nextGOPendingIs_general_rule_3_0 nextLoad_DeviceSIAGO_WritePull) done
show goal67: "C_msg_P_host ISD (nextSnoopIs SnpInv) (HSTATE MA) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (smt (verit) empty_no_snoop2 i209 i214) done
show goal68: "length (htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])) \<le> 1"
apply  (insert assms) apply (smt (verit) aux2_r113 aux3_r113 i207 i253 i883 nextHTDDataPending_various_forms1) done
show goal69: "length (htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])) \<le> 1"
apply  (insert assms) apply (metis htddatas2_SIAGO_WritePull htddatas2_remove_op i2160 i78 nextGOPendingIs_general_rule_3_0) done
show goal70: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(139) i216) done
show goal71: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis CSTATE_otherside_rule_4_0 CSTATE_remove_op SharedSnpInv'_MAD_CSTATE_invariant5 g302aux i213 i2160 i80 nextGOPendingIs_general_rule_3_0 reqresps2_SIAGO_WritePull reqresps2_remove_op snpresps1_SIAGO_WritePull snpresps1_remove_op snps1_SIAGO_WritePull) done
show goal72: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> reqs1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i254) done
show goal73: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> reqs2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis CSTATE_otherside_rule_4_0 CSTATE_remove_op SharedSnpInv'_MAD_CSTATE_invariant5 i2160 i82 nextGOPendingIs_general_rule_3_0 reqs2_SIAGO_WritePull reqs2_remove_op) done
show goal74: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> reqs1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i207) done
show goal75: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> reqs2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) HTDDataPending_htddatas_invariant2 i101 i260) done
show goal76: "length (reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])) \<le> 1"
apply  (insert assms) apply (smt (verit) aux_r113 i215 i883) done
show goal77: "length (reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])) \<le> 1"
apply  (insert assms) apply (metis i2160 i86 nextGOPendingIs_general_rule_3_0 reqresps2_SIAGO_WritePull reqresps2_remove_op) done
show goal78: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i213) done
show goal79: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i214) done
show goal80: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i215 reqresps_empty_noGOPendingIs1) done
show goal81: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis CSTATE_otherside_rule_4_0 CSTATE_remove_op SharedSnpInv'_MAD_CSTATE_invariant5 g302aux htddatas2_SIAGO_WritePull htddatas2_remove_op i213 i2160 i587 nextGOPendingIs_general_rule_3_0 snpresps1_SIAGO_WritePull snpresps1_remove_op snps1_SIAGO_WritePull) done
show goal82: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i255) done
show goal83: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis CSTATE_SIAGO_WritePull_IMAD_invariant CSTATE_otherside_rule_4_0 CSTATE_remove_op SharedSnpInv'_MAD_CSTATE_invariant5 i2160 i92 nextGOPendingIs_general_rule_3_0 nextReqIs_SIAGO_WritePull_IMAD_invariant2) done
show goal84: "C_msg_P_same MIA (nextReqIs DirtyEvict) nextEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (metis CSTATE_otherside_rule_4_0 CSTATE_remove_op C_msg_P_same_def SIAGO_WritePull_nextEvict_otherside SharedSnpInv'_MAD_CSTATE_invariant5 i2160 i255 i93 nextGOPendingIs_general_rule_3_0 nextReqIs_SIAGO_WritePull_IMAD_invariant2) done
show goal85: "reqs1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<longrightarrow> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i215) done
show goal86: "reqs2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<longrightarrow> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis CSTATE_assign_rule_1 i2160 i95 reqresps2_SIAGO_WritePull reqresps2_remove_op reqs2_SIAGO_WritePull reqs2_remove_op) done
show goal87: "reqs1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<longrightarrow> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i254) done
show goal88: "reqs2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<longrightarrow> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis CSTATE_assign_rule_1 g302aux i2160 reqs2_SIAGO_WritePull snpresps1_SIAGO_WritePull snpresps1_remove_op) done
show goal89: "reqs1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<longrightarrow> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i254) done
show goal90: "reqs2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<longrightarrow> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i101 i260) done
show goal91: "HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> (CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) \<open>\<not> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0\<close>) done
show goal92: "HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> (CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) assms aux1_103p i313 i750) done
show goal93: "HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> (CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i813 nextDTHDataFrom_otherside_rule_3_0 remove_instr_HSTATE) done
show goal94: "HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> (CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i813 nextDTHDataFrom_otherside_rule_3_0 remove_instr_HSTATE) done
show goal95: "HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> (CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i813 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal96: "HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> (CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i813 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal97: "reqs1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<longrightarrow> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i215) done
show goal98: "reqs2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<longrightarrow> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis CSTATE_assign_rule_1 i2160 i95 reqresps2_SIAGO_WritePull reqresps2_remove_op reqs2_SIAGO_WritePull reqs2_remove_op) done
show goal99: "HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i222) done
show goal100: "HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i313 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal101: "HSTATE SD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<longrightarrow> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i223) done
show goal102: "HSTATE SD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<longrightarrow> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i223) done
show goal103: "length (dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])) \<le> 1"
apply  (insert assms) apply (smt (verit) aux4_r113 aux5_r113) done
show goal104: "length (dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])) \<le> 1"
apply  (insert assms) apply (metis aux542 dthdatas2_SIAGO_WritePull dthdatas2_remove_op i2160 le0 list.size(3) nextGOPendingIs_general_rule_3_0) done
show goal105: "HSTATE SD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i223) done
show goal106: "HSTATE SD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i223) done
show goal107: "HSTATE SA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> (nextSnpRespIs RspIFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> nextSnpRespIs RspSFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<longrightarrow> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i220) done
show goal108: "HSTATE SA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> (nextSnpRespIs RspIFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> nextSnpRespIs RspSFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<longrightarrow> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i220) done
show goal109: "nextSnpRespIs RspIFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> nextSnpRespIs RspIHitSE ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i216) done
show goal110: "nextSnpRespIs RspIFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> nextSnpRespIs RspIHitSE ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis CSTATE_SIAGO_WritePull_IMAD_invariant SIAGO_WritePull_nextSnpRespIs_otherside assms i2160 i316 nextGOPendingIs_general_rule_3_0 nextSnpRespIs_invariant2) done
show goal111: "nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i255) done
show goal112: "nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis CSTATE_SIAGO_WritePull_IMAD_invariant CSTATE_otherside_rule_4_0 CSTATE_remove_op SharedSnpInv'_MAD_CSTATE_invariant5 i2160 i458 nextGOPendingIs_general_rule_3_0 nextReqIs_SIAGO_WritePull_IMAD_invariant2) done
show goal113: "snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<longrightarrow> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis CSTATE_assign_rule_1 g302aux i2160 reqresps2_SIAGO_WritePull snpresps1_SIAGO_WritePull snpresps1_remove_op) done
show goal114: "snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<longrightarrow> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i215) done
show goal115: "length (snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])) \<le> 1"
apply  (insert assms) apply (metis CSTATE_assign_rule_1 CSTATE_otherside_rule_3 SharedSnpInv'_snpresps1_invariant6 assms aux542 aux_r113 g302aux i2160 i316 i381 i78 le0 le_antisym list.size(3) nat_le_linear nextGOPendingIs_general_rule_3_0 no2Datas_def reqresps_empty_noGOPendingIs1 snpresps1_SIAGO_WritePull snpresps1_remove_op) done
show goal116: "length (snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])) \<le> 1"
apply  (insert assms) apply (metis assms i2160 i316 le0 list.size(3) nextGOPendingIs_general_rule_3_0 snpresps2_SIAGO_WritePull snpresps2_remove_op) done
show goal117: "HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> (nextSnpRespIs RspIFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> nextSnpRespIs RspSFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<longrightarrow> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i222) done
show goal118: "HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> (nextSnpRespIs RspIFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> nextSnpRespIs RspSFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<longrightarrow> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i222) done
show goal119: "HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextSnpRespIs RspIFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis SIAGO_WritePull_nextSnpRespIs_sameside aux_r113 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) htddatas2_SIAGO_WritePull i2160 i453 nextGOPendingIs_XIAGOWP_otherside1 remove_instr_HSTATE) done
show goal120: "HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextSnpRespIs RspIFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis SIAGO_WritePull_nextSnpRespIs_otherside aux542 dthdatas2_SIAGO_WritePull hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i454 nextGOPendingIs_XIAGOWP_otherside1 remove_instr_HSTATE) done
show goal121: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis g302aux htddatas2_SIAGO_WritePull i2160 nextGOPendingIs_XIAGOWP_otherside1 snpresps1_SIAGO_WritePull snpresps1_remove_op) done
show goal122: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis assms htddatas1_SIAGO_WritePull htddatas1_general_rule_10_0 i2160 i316 snpresps2_SIAGO_WritePull snpresps2_remove_op) done
show goal123: "HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<longrightarrow> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i222) done
show goal124: "HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<longrightarrow> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i222) done
show goal125: "HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> reqs1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<longrightarrow> dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> []"
apply  (insert assms) apply (smt (verit) i225) done
show goal126: "HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> reqs2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<longrightarrow> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> []"
apply  (insert assms) apply (smt (verit) i225) done
show goal127: "HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<longrightarrow> CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i216) done
show goal128: "HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<longrightarrow> CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i224) done
show goal129: "HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i224) done
show goal130: "HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i224) done
show goal131: "dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<and> HSTATE SD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i223) done
show goal132: "dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<and> HSTATE SD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i223) done
show goal133: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> nextLoad ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i207) done
show goal134: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> nextLoad ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis CSTATE_otherside_rule_4_0 CSTATE_remove_op SharedSnpInv'_MAD_CSTATE_invariant5 i2160 i259 i752old nextGOPendingIs_general_rule_3_0 nextLoad_DeviceSIAGO_WritePull) done
show goal135: "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextSnoopPending T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (smt (verit) i212 i213 i214 nextSnoopPending_def) done
show goal136: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> HSTATE SD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) i211) done
show goal137: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> HSTATE SD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (metis CSTATE_otherside_rule_4_0 CSTATE_remove_op HSTATE_SIAGO_WritePull_invariant SharedSnpInv'_MAD_CSTATE_invariant5 assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i144 i2160 i223 i800 nextGOPendingIs_general_rule_3_0 nextGOPending_DeviceSIAGO_WritePull remove_instr_HSTATE) done
show goal138: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> nextLoad ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(143) i216) done
show goal139: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> nextLoad ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis CSTATE_otherside_rule_4_0 CSTATE_remove_op SharedSnpInv'_MAD_CSTATE_invariant5 i146 i2160 i259 nextGOPendingIs_general_rule_3_0 nextLoad_DeviceSIAGO_WritePull) done
show goal140: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) i209) done
show goal141: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) empty_no_snoop2 i214) done
show goal142: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i211) done
show goal143: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis g302aux i213 i2160 nextGOPendingIs_general_rule_3_0 snpresps1_SIAGO_WritePull snpresps1_remove_op snps1_SIAGO_WritePull) done
show goal144: "(CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> (CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i313 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal145: "(CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> (CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i313 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal146: "(CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> []"
apply  (insert assms) apply (smt (verit) i225) done
show goal147: "(CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> []"
apply  (insert assms) apply (smt (verit) i225) done
show goal148: "HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i313 remove_instr_HSTATE snpresps1_SIAGO_WritePull snps1_general_rule_3_0) done
show goal149: "HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i222) done
show goal150: "HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i222) done
show goal151: "HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i222) done
show goal152: "HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i222) done
show goal153: "HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> reqs2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i222) done
show goal154: "HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> reqs1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i222) done
show goal155: "HSTATE SD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> reqs2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i223) done
show goal156: "HSTATE SD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> reqs1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i223) done
show goal157: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) \<open>\<not> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0\<close>) done
show goal158: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i800 nextGOPendingIs_XIAGOWP_otherside1 remove_instr_HSTATE) done
show goal159: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextReqIs RdShared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i254 nextReqIs_not_various_forms1) done
show goal160: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextReqIs RdShared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i800 nextDTHDataPending_other_rule_7_0 remove_instr_HSTATE) done
show goal161: "CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> (CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i313 nextGOPendingIs_XIAGOWP_otherside1 remove_instr_HSTATE) done
show goal162: "CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> (CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i313 nextGOPendingIs_XIAGOWP_otherside1 remove_instr_HSTATE) done
show goal163: "CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> reqs2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<or> nextReqIs CleanEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i800 nextGOPendingIs_XIAGOWP_otherside1 remove_instr_HSTATE reqs2_SIAGO_WritePull) done
show goal164: "CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> reqs1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<or> nextReqIs CleanEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i254) done
show goal165: "CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) i2201) done
show goal166: "CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) i2201) done
show goal167: "CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPendingIs GO_WritePullDrop ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) i215 reqresps_empty_noGOPendingIs1) done
show goal168: "CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPendingIs GO_WritePullDrop ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (metis CSTATE_otherside_rule_4_0 CSTATE_remove_op HSTATE_SIAGO_WritePull_invariant SIAGO_WritePull_nextGOPendingIs_otherside SharedSnpInv'_MAD_CSTATE_invariant5 assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i181 i2160 i224 i313 i579 i800 i817 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal169: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) i207) done
show goal170: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (metis CSTATE_otherside_rule_4_0 CSTATE_remove_op HSTATE_SIAGO_WritePull_invariant SharedSnpInv'_MAD_CSTATE_invariant5 assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i183 i2160 i313 i863 nextGOPendingIs_general_rule_3_0 nextHTDDataPending_general_rule_3_0 remove_instr_HSTATE) done
show goal171: "CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i800 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal172: "CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i800 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal173: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis assms dthdatas2_SIAGO_WritePull hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i800 remove_instr_HSTATE snps1_general_rule_3_0) done
show goal174: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant Invalid_not_eq_MIA i216) done
show goal175: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant Invalid_not_eq_MIA i216) done
show goal176: "HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis assms dthdatas2_SIAGO_WritePull hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i313 remove_instr_HSTATE snps1_general_rule_3_0) done
show goal177: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) HOST_State.distinct(103) HOST_State.distinct(107) HOST_State.distinct(285) HOST_State.distinct(287) HOST_State.distinct(289) HOST_State.distinct(375) HSTATE_invariant4 i2201) done
show goal178: "nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i207) done
show goal179: "nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis CSTATE_SIAGO_WritePull_IMAD_invariant aux192 i2160 nextDTHDataFrom_otherside_rule_3_0) done
show goal180: "nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (metis CSTATE_SIAGO_WritePull_IMAD_invariant aux192 i2160 nextDTHDataFrom_otherside_rule_3_0) done
show goal181: "nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (metis CSTATE_SIAGO_WritePull_IMAD_invariant aux192 i2160 nextDTHDataFrom_otherside_rule_3_0) done
show goal182: "HSTATE SA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i220) done
show goal183: "HSTATE SD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> \<not> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i223) done
show goal184: "HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> (\<not> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> nextSnpRespIs RspIFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> (\<not> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> nextSnpRespIs RspIFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1)"
apply  (insert assms) apply (smt (verit) i222) done
show goal185: "CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(163) i216) done
show goal186: "CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (metis CSTATE_SIAGO_WritePull_IMAD_invariant SIAGO_WritePull_nextGOPendingIs_otherside assms i2160 i582 nextDTHDataFrom_otherside_rule_3_0) done
show goal187: "CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(163) i216) done
show goal188: "CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(163) i216) done
show goal189: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant Invalid_not_eq_MIA i216) done
show goal190: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (metis CSTATE_SIAGO_WritePull_IMAD_invariant SIAGO_WritePull_nextGOPendingIs_otherside assms i2160 i582 nextDTHDataFrom_otherside_rule_3_0) done
show goal191: "snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<longrightarrow> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i215) done
show goal192: "snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<longrightarrow> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis CSTATE_assign_rule_1 assms i2160 i316 reqresps2_SIAGO_WritePull snpresps2_SIAGO_WritePull snpresps2_remove_op) done
show goal193: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextReqIs RdShared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i215 reqresps_empty_noGOPendingIs1) done
show goal194: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextReqIs RdShared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i254 reqs1_empty_not_nextReqIs_general_invariant) done
show goal195: "HSTATE SD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i223) done
show goal196: "HSTATE SD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i223) done
show goal197: "HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> (nextSnpRespIs RspIFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> nextSnpRespIs RspSFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i222) done
show goal198: "HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> (nextSnpRespIs RspIFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> nextSnpRespIs RspSFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i222) done
show goal199: "HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i313 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal200: "C_msg_P_same SIA (nextGOPendingIs GO_WritePull) nextEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (metis CSTATE_inequality_invariant MESI_State.distinct(175) SIAGO_WritePull_nextEvict_otherside SIAGO_WritePull_nextGOPendingIs_otherside assms i216 i2160 i582 nextGOPendingIs_general_rule_3_0) done
show goal201: "C_msg_P_same SIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextReqIs RdShared T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (metis CSTATE_SIAGO_WritePull_IMAD_invariant CSTATE_inequality_invariant CSTATE_otherside_rule_4_0 CSTATE_remove_op C_msg_state_def MESI_State.distinct(289) SharedSnpInv'_MAD_CSTATE_invariant5 i215 i2160 i254 i47 nextGOPendingIs_general_rule_3_0 nextReqIs_SIAGO_WritePull_IMAD_invariant2 nextReqIs_not_various_forms1 reqresps1_SIAGO_WritePull_aux1 reqresps1_remove_op reqresps_empty_noGOPendingIs1 reqs1_remove_op) done
show goal202: "CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(175) i216) done
show goal203: "CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis CSTATE_otherside_rule_4_0 CSTATE_remove_op SharedSnpInv'_MAD_CSTATE_invariant5 g302aux htddatas2_SIAGO_WritePull htddatas2_remove_op i213 i2160 i317 nextGOPendingIs_general_rule_3_0 snpresps1_SIAGO_WritePull snpresps1_remove_op snps1_SIAGO_WritePull) done
show goal204: "C_msg_P_same SIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextSnoopPending T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (smt (verit) i212 i213 i214 nextSnoopPending_def) done
show goal205: "CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) i2201) done
show goal206: "CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) i2201) done
show goal207: "C_msg_P_same SIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextDTHDataPending T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (metis CSTATE_SIAGO_WritePull_IMAD_invariant SIAGO_WritePull_nextHTDDataPending_otherside assms aux542 i215 i2160 i582 nextDTHDataPending_def nextDTHDataPending_other_rule_7_0 reqresps1_SIAGO_WritePull_aux1 reqresps1_remove_op reqresps_empty_noGOPendingIs1) done
show goal208: "CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(175) i216) done
show goal209: "CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (metis CSTATE_SIAGO_WritePull_IMAD_invariant SIAGO_WritePull_nextGOPendingIs_otherside assms i2160 i582 nextDTHDataFrom_otherside_rule_3_0) done
show goal210: "C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) nextEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (metis CSTATE_inequality_invariant CSTATE_otherside_rule_4_0 CSTATE_remove_op C_msg_P_same_def MESI_State.distinct(175) SIAGO_WritePull_nextEvict_otherside SIAGO_WritePull_nextGOPendingIs_otherside SharedSnpInv'_MAD_CSTATE_invariant5 i215 i216 i2160 i324 nextGOPendingIs_general_rule_3_0 reqresps1_SIAGO_WritePull_aux1 reqresps1_remove_op reqresps_empty_noGOPendingIs1) done
show goal211: "C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextReqIs RdShared T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (metis CSTATE_SIAGO_WritePull_IMAD_invariant CSTATE_inequality_invariant CSTATE_otherside_rule_4_0 CSTATE_remove_op C_msg_state_def MESI_State.distinct(289) SharedSnpInv'_MAD_CSTATE_invariant5 i215 i2160 i254 i47 nextGOPendingIs_general_rule_3_0 nextReqIs_SIAGO_WritePull_IMAD_invariant2 nextReqIs_not_various_forms1 reqresps1_SIAGO_WritePull_aux1 reqresps1_remove_op reqresps_empty_noGOPendingIs1 reqs1_remove_op) done
show goal212: "C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextSnoopPending T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (smt (verit) i212 i213 i214 nextSnoopPending_def) done
show goal213:  "CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPendingIs GO_WritePullDrop ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) i215 reqresps_empty_noGOPendingIs1) done
show goal214:  "CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPendingIs GO_WritePullDrop ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i2201 i813 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal215: "C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextDTHDataPending T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (metis CSTATE_SIAGO_WritePull_IMAD_invariant SIAGO_WritePull_nextHTDDataPending_otherside assms aux542 i215 i2160 i582 nextDTHDataPending_def nextDTHDataPending_other_rule_7_0 reqresps1_SIAGO_WritePull_aux1 reqresps1_remove_op reqresps_empty_noGOPendingIs1) done
show goal216: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) i207) done
show goal217: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE SA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) i207) done
show goal218: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE SA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i221 i774 i813 nextGOPendingIs_general_rule_3_0 nextHTDDataPending_general_rule_3_0 remove_instr_HSTATE) done
show goal219: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1)"
apply  (insert assms) apply (smt (verit) i207) done
show goal220: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0)"
apply  (insert assms) apply (smt (verit) i207) done
show goal221: "C_not_C_msg Modified IMAD nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (smt (verit) i211 i217) done
show goal222: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) i211) done
show goal223: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> nextStore ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(147) i216) done
show goal224: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> nextStore ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis CSTATE_SIAGO_WritePull_IMAD_invariant CSTATE_otherside_rule_4_0 CSTATE_remove_op SharedSnpInv'_MAD_CSTATE_invariant5 i2160 i340 nextStore_XIAGO_WP1 nextStore_otherside_rule_1_0) done
show goal225: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i211) done
show goal226: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis g302aux i213 i2160 nextGOPendingIs_general_rule_3_0 snpresps1_SIAGO_WritePull snpresps1_remove_op snps1_SIAGO_WritePull) done
show goal227: "snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<longrightarrow> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i215) done
show goal228: "snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<longrightarrow> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis CSTATE_assign_rule_1 assms i2160 i316 reqresps2_SIAGO_WritePull snpresps2_SIAGO_WritePull snpresps2_remove_op) done
show goal229: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (metis CSTATE_otherside_rule_4_0 CSTATE_remove_op HSTATE_SIAGO_WritePull_invariant SIAGO_WritePull_nextHTDDataPending_real SharedSnpInv'_MAD_CSTATE_invariant5 assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i313 i345 i863 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal230: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (metis CSTATE_otherside_rule_4_0 CSTATE_remove_op HSTATE_SIAGO_WritePull_invariant SharedSnpInv'_MAD_CSTATE_invariant5 assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i313 i346 i744 i863 nextGOPendingIs_general_rule_3_0 nextGOPending_DeviceSIAGO_WritePull remove_instr_HSTATE) done
show goal231: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) i211) done
show goal232: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (metis CSTATE_otherside_rule_4_0 CSTATE_remove_op HSTATE_SIAGO_WritePull_invariant SharedSnpInv'_MAD_CSTATE_invariant5 assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i313 i348 i744 i863 nextGOPendingIs_general_rule_3_0 nextGOPending_DeviceSIAGO_WritePull remove_instr_HSTATE) done
show goal233: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> nextStore ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(167) i216) done
show goal234: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> nextStore ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis CSTATE_SIAGO_WritePull_IMAD_invariant CSTATE_otherside_rule_4_0 CSTATE_remove_op SharedSnpInv'_MAD_CSTATE_invariant5 i2160 i350 nextStore_XIAGO_WP1 nextStore_otherside_rule_1_0) done
show goal235: "C_msg_P_same IMA nextGOPending nextStore ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (metis CSTATE_otherside_rule_4_0 CSTATE_remove_op SharedSnpInv'_MAD_CSTATE_invariant5 i211 i2160 i371 nextGOPending_DeviceSIAGO_WritePull nextStore_XIAGO_WP1 nextStore_otherside_rule_1_0) done
show goal236: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i207) done
show goal237: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis CSTATE_SIAGO_WritePull_IMAD_invariant CSTATE_otherside_rule_4_0 CSTATE_remove_op HTDDataPending_htddatas_invariant2 SharedSnpInv'_MAD_CSTATE_invariant5 htddatas2_SIAGO_WritePull htddatas2_remove_op i2160 i353 nextGOPendingIs_general_rule_3_0 nextHTDDataPending_various_forms2) done
show goal238: "C_msg_P_oppo IMA nextGOPending (\<lambda>T i. \<not> nextSnoopPending T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (smt (verit) i211 i212) done
show goal239: "C_msg_P_oppo SMA nextGOPending (\<lambda>T i. \<not> nextSnoopPending T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (smt (verit) i211 i212) done
show goal240: "C_msg_P_oppo ISA nextGOPending (\<lambda>T i. \<not> nextSnoopPending T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (smt (verit) i211 i212) done
show goal241: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) i211) done
show goal242: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (metis CSTATE_otherside_rule_4_0 CSTATE_remove_op HSTATE_SIAGO_WritePull_invariant SharedSnpInv'_MAD_CSTATE_invariant5 assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i313 i358 i863 nextGOPendingIs_general_rule_3_0 nextGOPending_DeviceSIAGO_WritePull remove_instr_HSTATE) done
show goal243: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> ((CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> \<not> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(151) MESI_State.distinct(171) i211 i216) done
show goal244: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> ((CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> \<not> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(139) MESI_State.distinct(141) MESI_State.distinct(149) MESI_State.distinct(151) MESI_State.distinct(169) MESI_State.distinct(171) MESI_State.distinct(95) i207 i211 i216 i217) done
show goal245: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> (dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<or> HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]))"
apply  (insert assms) apply (smt (verit) CSTATE_different1 MESI_State.distinct(149) MESI_State.distinct(169) i207 i216) done
show goal246: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> (dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<or> HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]))"
apply  (insert assms)
using CSTATE_otherside_rule_3 HOST_State.distinct(267) HOST_State.distinct(287) HOST_State.distinct(379) HSTATE_invariant3 dthdatas2_SIAGO_WritePull hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i183 i1x i221 i224 i2x i313 i345 i585 i770 i772 i774 i813 i863 nextGOPendingIs_general_rule_3_0 nextHTDDataPending_general_rule_3_0 remove_instr_HSTATE goal237 i916
using CSTATE_SIAGO_WritePull_otherside_invariant2 HOST_State.distinct(269) HOST_State.distinct(289) HSTATE_SIAGO_WritePull_invariant HSTATE_XIAGOWP1 HSTATE_invariant4 SIAGO_WritePull_nextHTDDataPending_real assms goal170 goal176 goal229 i222 i319 i800
proof -
have f1: "\<not> HSTATE MB T"
by (metis i1x i813)
have "HSTATE SB T \<longrightarrow> (\<exists>h ha. SB \<noteq> h \<and> SB \<noteq> ha)"
by (metis HSTATE_XIAGOWP1 i224)
moreover
{
assume "\<exists>h ha. SB \<noteq> h \<and> SB \<noteq> ha"
moreover
{
assume "\<not> HSTATE MAD T"
moreover
{
assume "\<not> CSTATE IMA T 1 \<and> \<not> HSTATE MAD T"
moreover
{
assume "(\<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1) \<and> \<not> HSTATE MAD T"
moreover
{
assume "\<not> HSTATE MAD T \<and> nextHTDDataPending T 1"
then
have "(\<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> \<not> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
by (metis HSTATE_XIAGOWP1 goal237 nextHTDDataPending_general_rule_3_0)
then
have "(CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> (dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<or> HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]))) \<or> (\<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> \<not> nextHTDDataPending T 1 \<or> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
by (metis dthdatas2_SIAGO_WritePull goal170 goal176 goal229 i222 nextHTDDataPending_general_rule_3_0)
}
ultimately
have "(CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> (dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<or> HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]))) \<or> (\<not> CSTATE SMA T 1 \<and> \<not> CSTATE IMA T 1) \<and> \<not> nextHTDDataPending T 1 \<or> (\<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> \<not> nextHTDDataPending T 1 \<or> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
by metis
}
ultimately
have "HSTATE MA T \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> (dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<or> HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]))) \<or> (\<not> CSTATE SMA T 1 \<and> \<not> CSTATE IMA T 1) \<and> \<not> nextHTDDataPending T 1 \<or> (\<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> \<not> nextHTDDataPending T 1 \<or> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
using f1
by (metis i2x i313 i585 i863)
}
ultimately
have "(CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> (dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<or> HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]))) \<or> (\<not> CSTATE SMA T 1 \<and> \<not> CSTATE IMA T 1) \<and> \<not> nextHTDDataPending T 1 \<or> (\<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> \<not> nextHTDDataPending T 1"
using f1
by (metis HSTATE_XIAGOWP1 aux5_r113 dthdatas2_SIAGO_WritePull goal177 i2x i313 i585 i863)
}
ultimately
have "HSTATE IB T \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> (dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<or> HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]))) \<or> (\<not> CSTATE SMA T 1 \<and> \<not> CSTATE IMA T 1) \<and> \<not> nextHTDDataPending T 1 \<or> (\<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> \<not> nextHTDDataPending T 1"
using f1
by (metis HOST_State.distinct(267) HSTATE_invariant3 i1x i2x i319)
}
ultimately
have "(CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> (dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<or> HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]))) \<or> (\<not> CSTATE SMA T 1 \<and> \<not> CSTATE IMA T 1) \<and> \<not> nextHTDDataPending T 1 \<or> (\<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> \<not> nextHTDDataPending T 1"
using f1
by (metis i1x i2x i319 i770 i772 i774)
then
show ?thesis
by (metis CSTATE_otherside_rule_3 nextHTDDataPending_general_rule_3_0)
qed
show goal247: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(151) MESI_State.distinct(171) i211 i216) done
show goal248: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis aux542 dthdatas2_SIAGO_WritePull dthdatas2_remove_op i2160 nextGOPendingIs_general_rule_3_0) done
show goal249: "C_msg_P_same SMA nextGOPending nextStore ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (metis CSTATE_otherside_rule_4_0 CSTATE_remove_op SharedSnpInv'_MAD_CSTATE_invariant5 i211 i2160 i371 nextGOPending_DeviceSIAGO_WritePull nextStore_XIAGO_WP1 nextStore_otherside_rule_1_0) done
show goal250: "CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) i207 i211) done
show goal251: "CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (metis CSTATE_otherside_rule_4_0 CSTATE_remove_op HSTATE_SIAGO_WritePull_invariant SharedSnpInv'_MAD_CSTATE_invariant5 assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i221 i313 i367 i728 i770 i772 i813 i863 nextGOPendingIs_general_rule_3_0 nextGOPending_DeviceSIAGO_WritePull remove_instr_HSTATE) done
show goal252: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> nextLoad ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(139) MESI_State.distinct(141) MESI_State.distinct(143) MESI_State.distinct(145) i216) done
show goal253: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> nextLoad ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis CSTATE_SIAGO_WritePull_otherside_invariant2 i146 i2160 i259 i369 i752old nextGOPendingIs_general_rule_3_0 nextLoad_DeviceSIAGO_WritePull) done
show goal254: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> nextStore ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(147) MESI_State.distinct(149) MESI_State.distinct(151) MESI_State.distinct(167) MESI_State.distinct(169) MESI_State.distinct(171) i216) done
show goal255: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> nextStore ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis CSTATE_SIAGO_WritePull_otherside_invariant2 i371 nextStore_otherside_rule_1_0) done
show goal256: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> (dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<or> nextSnpRespIs RspSFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> HSTATE SD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]))"
apply  (insert assms) apply (smt (verit) CSTATE_different1 MESI_State.distinct(141) MESI_State.distinct(95) i207 i211 i216) done
show goal257: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> (dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<or> nextSnpRespIs RspSFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> HSTATE SD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]))"
apply  (insert assms) apply (metis aux542 dthdatas2_SIAGO_WritePull dthdatas2_remove_op i2160 i217 nextGOPendingIs_general_rule_3_0) done
show goal258: "CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) i211) done
show goal259: "CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (metis CSTATE_otherside_rule_4_0 CSTATE_remove_op HSTATE_SIAGO_WritePull_invariant SharedSnpInv'_MAD_CSTATE_invariant5 assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i221 i768 i813 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal260: "CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) i207) done
show goal261: "CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i221 i774 i813 nextGOPendingIs_general_rule_3_0 nextHTDDataPending_general_rule_3_0 remove_instr_HSTATE) done
show goal262: "CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(145) i216) done
show goal263: "CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis CSTATE_otherside_rule_4_0 CSTATE_remove_op SharedSnpInv'_MAD_CSTATE_invariant5 g302aux i213 i214 i2160 i378 nextGOPendingIs_general_rule_3_0 reqresps2_SIAGO_WritePull reqresps2_remove_op snpresps1_SIAGO_WritePull snpresps1_remove_op snps1_SIAGO_WritePull) done
show goal264: "CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> \<not> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) assms aux1_103p i313) done
show goal265: "CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> \<not> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) \<open>\<not> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0\<close>) done
show goal266: "CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i215) done
show goal267: "CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis CSTATE_otherside_rule_4_0 CSTATE_remove_op SharedSnpInv'_MAD_CSTATE_invariant5 i2160 i382 nextGOPendingIs_general_rule_3_0 reqresps2_SIAGO_WritePull reqresps2_remove_op) done
show goal268: "CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) i209) done
show goal269: "CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) empty_no_snoop2 i214) done
show goal270: "CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i209) done
show goal271: "CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) empty_no_snoop_variant2 i214) done
show goal272: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i209) done
show goal273: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) empty_no_snoop_variant2 i214) done
show goal274: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) i209) done
show goal275: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) empty_no_snoop2 i214) done
show goal276: "nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) \<open>\<not> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0\<close>) done
show goal277: "nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis CSTATE_SIAGO_WritePull_IMAD_invariant CSTATE_otherside_rule_4_0 CSTATE_remove_op SharedSnpInv'_MAD_CSTATE_invariant5 i2160 i393 nextGOPendingIs_general_rule_3_0 nextReqIs_SIAGO_WritePull_IMAD_invariant2) done
show goal278: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> CXL_SPG_used ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i209) done
show goal279: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> CXL_SPG_used ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) empty_no_snoop_variant2 i214) done
show goal280: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) i209) done
show goal281: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) empty_no_snoop2 i214) done
show goal282: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i209) done
show goal283: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) empty_no_snoop_variant2 i214) done
show goal284: "HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i225) done
show goal285: "HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i225) done
show goal286: "HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i225) done
show goal287: "HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> nextReqIs CleanEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i225) done
show goal288: "HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> nextReqIs CleanEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i225) done
show goal289: "HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i225) done
show goal290: "HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) HOST_State.distinct(265) HOST_State.distinct(267) HOST_State.distinct(269) HOST_State.distinct(285) HOST_State.distinct(287) HOST_State.distinct(289) HSTATE_invariant3 i2201) done
show goal291: "HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant aux192 i2160 nextDTHDataFrom_otherside_rule_3_0) done
show goal292: "HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis assms i2160 i316 snpresps2_SIAGO_WritePull snpresps2_remove_op snps1_general_rule_3_0) done
show goal293: "HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis g302aux i2160 nextDTHDataFrom_otherside_rule_3_0 snpresps1_SIAGO_WritePull snpresps1_remove_op) done
show goal294: "HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> nextReqIs CleanEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i254 reqs1_empty_not_nextReqIs_general_invariant) done
show goal295: "HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> nextReqIs CleanEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant aux192 i2160 nextDTHDataFrom_otherside_rule_3_0) done
show goal296: "HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> reqs2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) HOST_State.distinct(265) HOST_State.distinct(267) HOST_State.distinct(269) HOST_State.distinct(285) HOST_State.distinct(287) HOST_State.distinct(289) HSTATE_invariant4 i2201) done
show goal297: "HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> reqs1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis aux192 i2160 nextDTHDataFrom_otherside_rule_3_0 reqs1_SIAGO_WritePull) done
show goal298: "HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) HOST_State.distinct(265) HOST_State.distinct(267) HOST_State.distinct(269) HOST_State.distinct(285) HOST_State.distinct(287) HOST_State.distinct(289) HSTATE_invariant4 i2201) done
show goal299: "HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i215) done
show goal300: "(HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE SA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])) \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<longrightarrow> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<or> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i207 nextHTDDataPending_various_forms1) done
show goal301: "(HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE SA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])) \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<longrightarrow> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<or> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis assms htddatas2_SIAGO_WritePull i119 i2160 nextGOPendingIs_general_rule_3_0 reqresps_empty_noGOPendingIs1 snpresps2_SIAGO_WritePull snpresps2_remove_op) done
show goal302: "nextSnpRespIs RspSFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (metis CSTATE_SIAGO_WritePull_IMAD_invariant SIAGO_WritePull_nextSnpRespIs_sameside g302aux i2160 nextSnpRespIs_general_rule_3_0 nextSnpRespIs_invariant1) done
show goal303: "nextSnpRespIs RspSFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis CSTATE_SIAGO_WritePull_IMAD_invariant SARspSFwdM_invariant2 SIAGO_WritePull_nextSnpRespIs_otherside assms i2160 i316 nextGOPendingIs_general_rule_3_0 nextSnpRespIs_invariant2 nextSnpRespIs_invariant_variant1 nextSnpRespIs_remove_op snpresps2_remove_op) done
show goal304: "(CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) HOST_State.distinct(243) HOST_State.distinct(245) HOST_State.distinct(247) HOST_State.distinct(285) HOST_State.distinct(287) HOST_State.distinct(289) HSTATE_invariant3 i2201) done
show goal305: "(CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) HOST_State.distinct(243) HOST_State.distinct(245) HOST_State.distinct(247) HOST_State.distinct(285) HOST_State.distinct(287) HOST_State.distinct(289) HSTATE_invariant3 i2201) done
show goal306: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) i217) done
show goal307: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) empty_no_snoop2 i214) done
show goal308: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i217) done
show goal309: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) empty_no_snoop_variant2 i214) done
show goal310: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) i209) done
show goal311: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) empty_no_snoop2 i214) done
show goal312: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i209) done
show goal313: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) empty_no_snoop_variant2 i214) done
show goal314: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) i209) done
show goal315: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) empty_no_snoop2 i214) done
show goal316: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i209) done
show goal317: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) empty_no_snoop_variant2 i214) done
show goal318: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) i209) done
show goal319: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) empty_no_snoop2 i214) done
show goal320: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i209) done
show goal321: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) empty_no_snoop_variant2 i214) done
show goal322: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant Invalid_not_eq_MIA i216) done
show goal323: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) empty_no_snoop2 i214) done
show goal324: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant Invalid_not_eq_MIA i216) done
show goal325: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) empty_no_snoop_variant2 i214) done
show goal326: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) i217) done
show goal327: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) empty_no_snoop2 i214) done
show goal328: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i217) done
show goal329: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) empty_no_snoop_variant2 i214) done
show goal330: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> reqs1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i217) done
show goal331: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> reqs2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis CSTATE_otherside_rule_4_0 CSTATE_remove_op SharedSnpInv'_MAD_CSTATE_invariant5 i2160 i492 nextGOPendingIs_general_rule_3_0 reqs2_SIAGO_WritePull reqs2_remove_op) done
show goal332: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i217) done
show goal333: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis CSTATE_otherside_rule_4_0 CSTATE_remove_op SharedSnpInv'_MAD_CSTATE_invariant5 g302aux htddatas2_SIAGO_WritePull htddatas2_remove_op i213 i2160 i494 nextGOPendingIs_general_rule_3_0 reqresps2_SIAGO_WritePull reqresps2_remove_op snpresps1_SIAGO_WritePull snpresps1_remove_op snps1_SIAGO_WritePull) done
show goal334: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextReqIs RdShared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i254 nextReqIs_not_various_forms1) done
show goal335: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextReqIs RdShared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i579 nextGOPendingIs_XIAGOWP_otherside1 remove_instr_HSTATE) done
show goal336: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i579 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal337: "nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) \<open>\<not> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0\<close>) done
show goal338: "nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis CSTATE_SIAGO_WritePull_IMAD_invariant CSTATE_otherside_rule_4_0 CSTATE_remove_op SharedSnpInv'_MAD_CSTATE_invariant5 i2160 i499 nextGOPendingIs_general_rule_3_0 nextReqIs_SIAGO_WritePull_IMAD_invariant2) done
show goal339: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) \<open>\<not> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0\<close>) done
show goal340: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i579 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal341: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) \<open>\<not> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0\<close>) done
show goal342: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i579 nextGOPendingIs_XIAGOWP_otherside1 remove_instr_HSTATE) done
show goal343: "CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i209) done
show goal344: "CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) empty_no_snoop_variant2 i214) done
show goal345: "CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) i209) done
show goal346: "CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) empty_no_snoop2 i214) done
show goal347: "CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> CXL_SPG_used ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> nextReqIs CleanEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i209) done
show goal348: "CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> CXL_SPG_used ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> nextReqIs CleanEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) empty_no_snoop_variant2 i214) done
show goal349: "CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i209) done
show goal350: "CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) empty_no_snoop_variant2 i214) done
show goal351: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i209) done
show goal352: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) empty_no_snoop_variant2 i214) done
show goal353: "HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i224) done
show goal354: "HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> (\<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i255) done
show goal355: "HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> (\<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i313 nextGOPendingIs_XIAGOWP_otherside1 remove_instr_HSTATE) done
show goal356: "HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i224) done
show goal357: "HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i224) done
show goal358: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i211) done
show goal359: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis CSTATE_otherside_rule_4_0 CSTATE_remove_op HTDDataPending_htddatas_invariant2 SharedSnpInv'_MAD_CSTATE_invariant5 htddatas2_SIAGO_WritePull htddatas2_remove_op i2160 i520 nextGOPendingIs_general_rule_3_0 nextGOPending_DeviceSIAGO_WritePull) done
show goal360: "C_msg_P_oppo SMAD nextGOPending (\<lambda>T i. \<not> nextSnoopPending T i) ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) apply (smt (verit) i211 i212) done
show goal361: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i254 reqs1_empty_not_nextReqIs_general_invariant) done
show goal362: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i800 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal363: "nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<or> nextReqRespStateIs Invalid (reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]))"
apply  (insert assms) apply (smt (verit) i215 reqresps_empty_noGOPendingIs1) done
show goal364: "nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<or> nextReqRespStateIs Invalid (reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]))"
apply  (insert assms) apply (smt (verit) i215) done
show goal365: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> nextEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i254 reqs1_empty_not_nextReqIs_general_invariant) done
show goal366: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> nextEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i800 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal367: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextReqIs CleanEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> nextEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i254 reqs1_empty_not_nextReqIs_general_invariant) done
show goal368: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextReqIs CleanEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> nextEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i800 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal369: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i254 reqs1_empty_not_nextReqIs_general_invariant) done
show goal370: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i800 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal371: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextReqIs CleanEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i254 reqs1_empty_not_nextReqIs_general_invariant) done
show goal372: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextReqIs CleanEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i800 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal373: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) CSTATE_disj1 Invalid_not_eq_MIA i216) done
show goal374: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i800 nextGOPendingIs_XIAGOWP_otherside1 remove_instr_HSTATE) done
show goal375: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextReqIs CleanEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) CSTATE_disj1 Invalid_not_eq_MIA i216) done
show goal376: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextReqIs CleanEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i800 nextGOPendingIs_XIAGOWP_otherside1 remove_instr_HSTATE) done
show goal377: "CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i209) done
show goal378: "CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) empty_no_snoop_variant2 i214) done
show goal379: "nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> nextEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i255) done
show goal380: "nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> nextEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis SIAGO_WritePull_nextEvict_otherside i2160 i543 nextGOPendingIs_general_rule_3_0 nextReqIs_SIAGO_WritePull_IMAD_invariant2) done
show goal381: "nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) i255) done
show goal382: "nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i579 nextDTHDataFrom_otherside_rule_3_0 remove_instr_HSTATE) done
show goal383: "nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i255) done
show goal384: "nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i579 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal385: "nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<or> nextReqRespStateIs Invalid (reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]))"
apply  (insert assms) apply (smt (verit) i255) done
show goal386: "nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<or> nextReqRespStateIs Invalid (reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]))"
apply  (insert assms) apply (smt (verit) i215) done
show goal387: "CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> (CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1)"
apply  (insert assms) apply (smt (verit) i207) done
show goal388: "CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> (CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0)"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(141) i207 i216) done
show goal389: "CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i207) done
show goal390: "CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) empty_no_snoop2 i214) done
show goal391: "CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i207) done
show goal392: "CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) empty_no_snoop2 i214) done
show goal393: "CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i207) done
show goal394: "CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis CSTATE_otherside_rule_4_0 CSTATE_remove_op SIAGO_WritePull_nextHTDDataPending_real SharedSnpInv'_MAD_CSTATE_invariant5 g302aux i213 i2160 i557 nextGOPendingIs_general_rule_3_0 reqresps2_SIAGO_WritePull reqresps2_remove_op snpresps1_SIAGO_WritePull snpresps1_remove_op snps1_SIAGO_WritePull) done
show goal395: "CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i207) done
show goal396: "CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i255) done
show goal397: "nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> nextReqIs CleanEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i254 reqs1_empty_not_nextReqIs_general_invariant) done
show goal398: "nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> nextReqIs CleanEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis CSTATE_SIAGO_WritePull_IMAD_invariant CSTATE_otherside_rule_4_0 CSTATE_remove_op SharedSnpInv'_MAD_CSTATE_invariant5 i2160 i561 i947 nextGOPendingIs_general_rule_3_0 nextReqIs_SIAGO_WritePull_IMAD_invariant2) done
show goal399: "CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) i225) done
show goal400: "CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) CSTATE_different1 MESI_State.distinct(95) i216) done
show goal401: "CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) HOST_State.distinct(267) HOST_State.distinct(269) HOST_State.distinct(285) HOST_State.distinct(287) HOST_State.distinct(289) HOST_State.distinct(377) HSTATE_invariant3 i2201) done
show goal402: "nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> nextReqIs CleanEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> nextEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i254 reqs1_empty_not_nextReqIs_general_invariant) done
show goal403: "nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> nextReqIs CleanEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> nextEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis SIAGO_WritePull_nextEvict_otherside i2160 i566 nextGOPendingIs_general_rule_3_0 nextReqIs_general_rule_3_0) done
show goal404: "nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> nextReqIs CleanEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(145) i216) done
show goal405: "nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> nextReqIs CleanEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis CSTATE_SIAGO_WritePull_IMAD_invariant CSTATE_SIAGO_WritePull_otherside_invariant2 i2160 i568 nextGOPendingIs_general_rule_3_0 nextReqIs_SIAGO_WritePull_IMAD_invariant2) done
show goal406: "nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> nextReqIs CleanEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant Invalid_not_eq_MIA i216) done
show goal407: "nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> nextReqIs CleanEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis CSTATE_SIAGO_WritePull_IMAD_invariant CSTATE_otherside_rule_4_0 CSTATE_remove_op SharedSnpInv'_MAD_CSTATE_invariant5 i2160 i570 nextGOPendingIs_general_rule_3_0 nextReqIs_SIAGO_WritePull_IMAD_invariant2) done
show goal408: "CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextReqIs RdShared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i254 reqs1_empty_not_nextReqIs_general_invariant) done
show goal409: "CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextReqIs RdShared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i579 nextGOPendingIs_XIAGOWP_otherside1 remove_instr_HSTATE) done
show goal410: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i579 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal411: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> ((CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> (nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0)) \<and> \<not> ((CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> (nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1))"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i579 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal412: "nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i579 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal413: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant Invalid_not_eq_MIA i216) done
show goal414: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(149) MESI_State.distinct(169) i207 i216) done
show goal415: "nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i215 reqresps_empty_noGOPendingIs1) done
show goal416: "nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i215 reqresps_empty_noGOPendingIs1) done
show goal417: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) CSTATE_different1 MESI_State.distinct(149) MESI_State.distinct(169) i207 i216) done
show goal418: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (metis CSTATE_SIAGO_WritePull_otherside_invariant2 CSTATE_otherside_rule_4_0 CSTATE_remove_op HSTATE_SIAGO_WritePull_invariant SIAGO_WritePull_nextHTDDataPending_real SharedSnpInv'_MAD_CSTATE_invariant5 assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i183 i2160 i313 i345 i585 i813 i863 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal419: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant Invalid_not_eq_MIA i216) done
show goal420: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis CSTATE_otherside_rule_4_0 CSTATE_remove_op SharedSnpInv'_MAD_CSTATE_invariant5 g302aux htddatas2_SIAGO_WritePull htddatas2_remove_op i213 i2160 i587 nextGOPendingIs_general_rule_3_0 snpresps1_SIAGO_WritePull snpresps1_remove_op snps1_SIAGO_WritePull) done
show goal421: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) i209) done
show goal422: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) empty_no_snoop2 i214) done
show goal423: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i209) done
show goal424: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) empty_no_snoop_variant2 i214) done
show goal425: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i313 i579 i800 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal426: "CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPendingIs GO_WritePullDrop ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) i215 reqresps_empty_noGOPendingIs1) done
show goal427: "CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPendingIs GO_WritePullDrop ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) CSTATE_different1 MESI_State.distinct(163) i216) done
show goal428: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis assms dthdatas2_SIAGO_WritePull hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i579 remove_instr_HSTATE snps1_general_rule_3_0) done
show goal429: "CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i209) done
show goal430: "CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) empty_no_snoop_variant2 i214) done
show goal431: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i217) done
show goal432: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant Invalid_not_eq_MIA i216) done
show goal433: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i209) done
show goal434: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) empty_no_snoop2 i214) done
show goal435: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i211) done
show goal436: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis g302aux i213 i2160 nextGOPendingIs_general_rule_3_0 snpresps1_SIAGO_WritePull snpresps1_remove_op snps1_SIAGO_WritePull) done
show goal437: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i209) done
show goal438: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) empty_no_snoop2 i214) done
show goal439: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant HSTATE_rule_1 assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i224 i579 remove_instr_HSTATE) done
show goal440: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i224 i579 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal441: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant HSTATE_rule_1 assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i224 i579 remove_instr_HSTATE) done
show goal442: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i224 i579 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal443: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant HSTATE_rule_1 assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i224 i579 remove_instr_HSTATE) done
show goal444: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i224 i579 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal445: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> (CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> (nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0))"
apply  (insert assms) apply (smt (verit) i207 i211) done
show goal446: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> (nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0))"
apply  (insert assms) apply (smt (verit) i207 i211) done
show goal447: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> (CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> (nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0))"
apply  (insert assms) apply (smt (verit) i207 i211) done
show goal448: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> (CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> (nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1))"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i224 i579 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal449: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> (nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1))"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i224 i579 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal450: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<or> HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> (CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> (nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1))"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i224 i579 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal451: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i209) done
show goal452: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) empty_no_snoop_variant2 i214) done
show goal453: "CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i209) done
show goal454: "CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) empty_no_snoop_variant2 i214) done
show goal455: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i209) done
show goal456: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) empty_no_snoop_variant2 i214) done
show goal457: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i209) done
show goal458: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) empty_no_snoop_variant2 i214) done
show goal459: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i209) done
show goal460: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) empty_no_snoop_variant2 i214) done
show goal461: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i209) done
show goal462: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) empty_no_snoop_variant2 i214) done
show goal463: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i211) done
show goal464: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) empty_no_snoop_variant2 i214) done
show goal465: "CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i209) done
show goal466: "CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) empty_no_snoop_variant2 i214) done
show goal467: "CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i209) done
show goal468: "CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) empty_no_snoop_variant2 i214) done
show goal469: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) i225) done
show goal470: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) i225) done
show goal471: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> (nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<longrightarrow> \<not> HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) i207 i211) done
show goal472: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> (nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<longrightarrow> \<not> HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) i225) done
show goal473: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) CSTATE_different1 MESI_State.distinct(139) i216) done
show goal474: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) HOST_State.distinct(107) HOST_State.distinct(285) HOST_State.distinct(287) HOST_State.distinct(289) HOST_State.distinct(377) HOST_State.distinct(379) HSTATE_invariant3 i2201) done
show goal475: "CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) CSTATE_different1 MESI_State.distinct(141) i216) done
show goal476: "CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) HOST_State.distinct(267) HOST_State.distinct(269) HOST_State.distinct(285) HOST_State.distinct(287) HOST_State.distinct(289) HOST_State.distinct(377) HSTATE_invariant3 i2201) done
show goal477: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> (CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1)"
apply  (insert assms) apply (smt (verit) i207) done
show goal478: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> (CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0)"
apply  (insert assms) apply (smt (verit) i211) done
show goal479: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i207) done
show goal480: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(141) i207 i216) done
show goal481: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i207) done
show goal482: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(95) i216) done
show goal483: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) i209) done
show goal484: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) empty_no_snoop2 i214) done
show goal485: "CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) i209) done
show goal486: "CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) empty_no_snoop2 i214) done
show goal487: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) i211) done
show goal488: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) empty_no_snoop2 i214) done
show goal489: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) i207) done
show goal490: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) empty_no_snoop2 i214) done
show goal491: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant HSTATE_rule_1 assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i800 remove_instr_HSTATE) done
show goal492: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i800 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal493: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant HSTATE_rule_1 assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i800 remove_instr_HSTATE) done
show goal494: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i800 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal495: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> (nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0))"
apply  (insert assms) apply (smt (verit) i207 i211) done
show goal496: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> (nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1))"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i800 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal497: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> (CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> (nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0))"
apply  (insert assms) apply (smt (verit) i207 i211) done
show goal498: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> (CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> (nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1))"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i800 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal499: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i800 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal500: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i579 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal501: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant HSTATE_rule_1 assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i579 remove_instr_HSTATE) done
show goal502: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i579 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal503: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> (CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0)"
apply  (insert assms) apply (smt (verit) i211) done
show goal504: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> (CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1)"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i579 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal505: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0)"
apply  (insert assms) apply (smt (verit) i211) done
show goal506: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1)"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i579 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal507: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> (CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0)"
apply  (insert assms) apply (smt (verit) i211) done
show goal508: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> (CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1)"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i579 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal509: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant HSTATE_rule_1 assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i579 remove_instr_HSTATE) done
show goal510: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i579 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal511: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i207) done
show goal512: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i579 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal513: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant HSTATE_rule_1 assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i579 remove_instr_HSTATE) done
show goal514: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i579 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal515: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i217) done
show goal516: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i579 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal517: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i207) done
show goal518: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis CSTATE_otherside_rule_4_0 CSTATE_remove_op SharedSnpInv'_MAD_CSTATE_invariant5 g302aux i213 i2160 i763 nextGOPendingIs_general_rule_3_0 reqresps2_SIAGO_WritePull reqresps2_remove_op snpresps1_SIAGO_WritePull snpresps1_remove_op snps1_SIAGO_WritePull) done
show goal519: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i211) done
show goal520: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis g302aux i213 i2160 nextGOPendingIs_general_rule_3_0 snpresps1_SIAGO_WritePull snpresps1_remove_op snps1_SIAGO_WritePull) done
show goal521: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(151) i216) done
show goal522: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) empty_no_snoop_variant2 i214) done
show goal523: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(149) i216) done
show goal524: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) empty_no_snoop_variant2 i214) done
show goal525: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(147) i216) done
show goal526: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) empty_no_snoop_variant2 i214) done
show goal527: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) empty_no_snoop_variant i213) done
show goal528: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) empty_no_snoop2 i214) done
show goal529: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) empty_no_snoop_variant i213) done
show goal530: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) empty_no_snoop2 i214) done
show goal531: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) empty_no_snoop_variant i213) done
show goal532: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) empty_no_snoop2 i214) done
show goal533: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis CSTATE_disj1 CSTATE_otherside_rule_6 CSTATE_remove_op HSTATE_SIAGO_WritePull_invariant MESI_State.distinct(95) SIAGO_WritePull_CSTATE_aux SharedSnpInv'_CSTATE_invariant5 SharedSnpInv'_MAD_CSTATE_invariant5 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i1x i2160 i217 i221 i703 i706 i813 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal534: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) \<open>\<not> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0\<close>) done
show goal535: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis CSTATE_otherside_rule_4_0 CSTATE_remove_op HSTATE_SIAGO_WritePull_invariant SharedSnpInv'_MAD_CSTATE_invariant5 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i705 nextGOPendingIs_general_rule_3_0 nextReqIs_SIAGO_WritePull_IMAD_invariant2 remove_instr_HSTATE) done
show goal536: "HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis CSTATE_otherside_rule_4_0 CSTATE_remove_op HSTATE_SIAGO_WritePull_invariant SharedSnpInv'_MAD_CSTATE_invariant5 assms i2160 i217 i221 i703 i706 i813 nextGOPendingIs_general_rule_3_0) done
show goal537: "HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> length (dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])) \<le> 1 \<and> length (dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])) \<le> 1"
apply  (insert assms) apply (metis aux4_r113 aux542 aux_r113 dthdatas1_perform_instr dthdatas2_SIAGO_WritePull dthdatas2_remove_op i2160 i883 list.size(3) nextGOPendingIs_general_rule_3_0) done
show goal538: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> length (dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])) \<le> 1 \<and> length (dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])) \<le> 1"
apply  (insert assms) apply (metis aux4_r113 aux542 aux_r113 dthdatas1_perform_instr dthdatas2_SIAGO_WritePull dthdatas2_remove_op i2160 i883 list.size(3) nextGOPendingIs_general_rule_3_0) done
show goal539: "HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis CSTATE_otherside_rule_4_0 CSTATE_remove_op HSTATE_SIAGO_WritePull_invariant SharedSnpInv'_MAD_CSTATE_invariant5 assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i817 nextDTHDataFrom_otherside_rule_3_0 remove_instr_HSTATE) done
show goal540: "HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant aux192 i2160 nextDTHDataFrom_otherside_rule_3_0) done
show goal541: "HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> length (dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])) \<le> 1 \<and> length (dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])) \<le> 1"
apply  (insert assms) apply (metis assms dthdatas2_SIAGO_WritePull hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i813 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal542: "HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis aux542 dthdatas2_SIAGO_WritePull dthdatas2_remove_op i2160 snps1_general_rule_3_0) done
show goal543: "HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant aux192 i2160 nextDTHDataFrom_otherside_rule_3_0) done
show goal544: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis aux542 dthdatas2_SIAGO_WritePull dthdatas2_remove_op i2160 snps1_general_rule_3_0) done
show goal545: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant aux192 i2160 nextDTHDataFrom_otherside_rule_3_0) done
show goal546: "HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis assms dthdatas2_SIAGO_WritePull hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i813 remove_instr_HSTATE snps1_general_rule_3_0) done
show goal547: "HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i813 nextDTHDataFrom_otherside_rule_3_0 remove_instr_HSTATE) done
show goal548: "HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i213 i214) done
show goal549: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i213 i214) done
show goal550: "HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i213 i214) done
show goal551: "HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i215) done
show goal552: "HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis aux192 i2160 nextDTHDataFrom_otherside_rule_3_0 reqresps2_SIAGO_WritePull) done
show goal553: "HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i215) done
show goal554: "HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i813 nextDTHDataFrom_otherside_rule_3_0 remove_instr_HSTATE reqresps2_SIAGO_WritePull) done
show goal555: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i215) done
show goal556: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis aux192 i2160 nextDTHDataFrom_otherside_rule_3_0 reqresps2_SIAGO_WritePull) done
show goal557: "HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (metis CSTATE_disj1 HSTATE_rule_1 MESI_State.distinct(151) MESI_State.distinct(171) i216 i2160) done
show goal558: "HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis CSTATE_otherside_rule_4_0 CSTATE_remove_op HSTATE_SIAGO_WritePull_invariant SharedSnpInv'_MAD_CSTATE_invariant5 assms i2160 i221 i728 i730 i813 nextGOPendingIs_general_rule_3_0) done
show goal559: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) CSTATE_different1 MESI_State.distinct(151) MESI_State.distinct(171) i216) done
show goal560: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis CSTATE_otherside_rule_4_0 CSTATE_remove_op HSTATE_SIAGO_WritePull_invariant SharedSnpInv'_MAD_CSTATE_invariant5 assms i2160 i221 i728 i730 i813 nextGOPendingIs_general_rule_3_0) done
show goal561: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> lastSharer ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i254 nextReqIs_not_various_forms1) done
show goal562: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> lastSharer ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i800 lastSharer_non_Invalid_rule_1_0 remove_instr_HSTATE) done
show goal563: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> lastSharer ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> (CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1)"
apply  (insert assms) apply (smt (verit) i254 nextReqIs_not_various_forms1) done
show goal564: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> lastSharer ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> (CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0)"
apply  (insert assms) apply (smt (verit) i211) done
show goal565: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i207) done
show goal566: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis assms i2160 i316 nextGOPendingIs_general_rule_3_0 snpresps2_SIAGO_WritePull snpresps2_remove_op) done
show goal567: "HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i222) done
show goal568: "HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i222) done
show goal569: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i207) done
show goal570: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) HOST_State.distinct(107) HOST_State.distinct(285) HOST_State.distinct(287) HOST_State.distinct(289) HOST_State.distinct(377) HOST_State.distinct(379) HSTATE_invariant3 i2201) done
show goal571: "HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> (\<not> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> nextGOPendingIs GO_WritePullDrop ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> (\<not> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> nextGOPendingIs GO_WritePullDrop ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1)"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i313 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal572: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<longrightarrow> \<not> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis g302aux i2160 nextGOPendingIs_XIAGOWP_otherside1 snpresps1_SIAGO_WritePull snpresps1_remove_op) done
show goal573: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<longrightarrow> \<not> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis assms i119 i2160 nextGOPendingIs_XIAGOWP_otherside1 reqresps_empty_noGOPendingIs1 snpresps2_SIAGO_WritePull snpresps2_remove_op) done
show goal574: "HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i225) done
show goal575: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1)"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant Invalid_not_eq_MIA i216) done
show goal576: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0)"
apply  (insert assms) apply (smt (verit) i211) done
show goal577: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> (CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1)"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant Invalid_not_eq_MIA i216) done
show goal578: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> (CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0)"
apply  (insert assms) apply (smt (verit) i211) done
show goal579: "HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) \<open>\<not> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0\<close>) done
show goal580: "HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) assms aux1_103p i313 i750) done
show goal581: "HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i313 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal582: "HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i225) done
show goal583: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<longrightarrow> \<not> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis g302aux i2160 nextGOPendingIs_XIAGOWP_otherside1 snpresps1_SIAGO_WritePull snpresps1_remove_op) done
show goal584: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<longrightarrow> \<not> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis assms i2160 i316 nextGOPendingIs_XIAGOWP_otherside1 snpresps2_SIAGO_WritePull snpresps2_remove_op) done
show goal585: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant Invalid_not_eq_MIA i216) done
show goal586: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i313 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal587: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant Invalid_not_eq_MIA i216) done
show goal588: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i313 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal589: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> (nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1))"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant Invalid_not_eq_MIA i216) done
show goal590: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> (nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0))"
apply  (insert assms) apply (smt (verit) i207 i211) done
show goal591: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant Invalid_not_eq_MIA i216) done
show goal592: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i313 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal593: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis CSTATE_otherside_rule_4_0 CSTATE_remove_op SharedSnpInv'_MAD_CSTATE_invariant5 i2160 i763 nextGOPendingIs_general_rule_3_0 reqresps2_SIAGO_WritePull reqresps2_remove_op) done
show goal594: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i215) done
show goal595: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant SIAGO_WritePull_nextGOPendingIs_otherside assms i2160 i582 nextDTHDataFrom_otherside_rule_3_0) done
show goal596: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i215 reqresps_empty_noGOPendingIs1) done
show goal597: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) CSTATE_different1 MESI_State.distinct(139) MESI_State.distinct(141) i216) done
show goal598: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis CSTATE_otherside_rule_4_0 CSTATE_remove_op HSTATE_SIAGO_WritePull_invariant SharedSnpInv'_MAD_CSTATE_invariant5 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i768 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal599: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (metis CSTATE_assign_rule_4 CSTATE_disj1 CSTATE_remove_op HSTATE_rule_1 MESI_State.distinct(169) MESI_State.distinct(171) SharedSnpInv'_MAD_CSTATE_invariant5) done
show goal600: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis CSTATE_otherside_rule_4_0 CSTATE_remove_op HSTATE_SIAGO_WritePull_invariant SharedSnpInv'_MAD_CSTATE_invariant5 assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i221 i728 i770 i813 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal601: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (metis CSTATE_assign_rule_4 CSTATE_disj1 CSTATE_remove_op HSTATE_rule_1 MESI_State.distinct(149) MESI_State.distinct(151) SharedSnpInv'_MAD_CSTATE_invariant5) done
show goal602: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis CSTATE_otherside_rule_4_0 CSTATE_remove_op HSTATE_SIAGO_WritePull_invariant SharedSnpInv'_MAD_CSTATE_invariant5 assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i221 i728 i772 i813 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal603: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis CSTATE_inequality_invariant CSTATE_otherside_rule_4_0 CSTATE_remove_op HSTATE_SIAGO_WritePull_invariant Invalid_not_eq_MIA SharedSnpInv'_MAD_CSTATE_invariant5 assms i216 i2160 i221 i773 i813 i945 nextGOPendingIs_general_rule_3_0) done
show goal604: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant SIAGO_WritePull_nextHTDDataPending_real hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i207 i2160 i774 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal605: "HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i224) done
show goal606: "HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i224) done
show goal607: "HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i215) done
show goal608: "HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i224) done
show goal609: "HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i224) done
show goal610: "HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i207) done
show goal611: "HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextReqIs RdShared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i254 reqs1_empty_not_nextReqIs_general_invariant) done
show goal612: "HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextReqIs RdShared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i219) done
show goal613: "HSTATE SD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i223) done
show goal614: "HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i222) done
show goal615: "HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i222) done
show goal616: "HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i225) done
show goal617: "snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<and> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis g302aux i2160 nextGOPendingIs_XIAGOWP_otherside1 snpresps1_SIAGO_WritePull snpresps1_remove_op) done
show goal618: "snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<and> HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis assms i2160 i316 nextGOPendingIs_XIAGOWP_otherside1 snpresps2_SIAGO_WritePull snpresps2_remove_op) done
show goal619: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i225) done
show goal620: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i225) done
show goal621: "nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i225) done
show goal622: "nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i225) done
show goal623: "HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextSnpRespIs RspSFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i222) done
show goal624: "HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextSnpRespIs RspSFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i217) done
show goal625: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i211) done
show goal626: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(95) i216 i217) done
show goal627: "HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis assms dthdatas2_SIAGO_WritePull hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i813 remove_instr_HSTATE snps1_general_rule_3_0) done
show goal628: "HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i813 nextDTHDataFrom_otherside_rule_3_0 remove_instr_HSTATE) done
show goal629: "HSTATE SA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i220) done
show goal630: "HSTATE SharedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i800 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal631: "CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> HSTATE SA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i220) done
show goal632: "CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> HSTATE SA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i220) done
show goal633: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<longrightarrow> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<or> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i207 nextHTDDataPending_various_forms1) done
show goal634: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<longrightarrow> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<or> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis assms htddatas2_SIAGO_WritePull i119 i2160 nextGOPendingIs_XIAGOWP_otherside1 reqresps_empty_noGOPendingIs1 snpresps2_SIAGO_WritePull snpresps2_remove_op) done
show goal635: "HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i813 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal636: "HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i216) done
show goal637: "HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i813 nextDTHDataFrom_otherside_rule_3_0 remove_instr_HSTATE) done
show goal638: "HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i813 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal639: "HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i813 remove_instr_HSTATE snpresps1_SIAGO_WritePull snps1_general_rule_3_0) done
show goal640: "HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i813 nextDTHDataFrom_otherside_rule_3_0 remove_instr_HSTATE) done
show goal641: "HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i813 nextDTHDataFrom_otherside_rule_3_0 remove_instr_HSTATE) done
show goal642: "HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i813 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal643: "HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i813 nextDTHDataFrom_otherside_rule_3_0 remove_instr_HSTATE) done
show goal644: "HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) \<open>\<not> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0\<close>) done
show goal645: "HSTATE MB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i813 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal646: "CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i215 reqresps_empty_noGOPendingIs1) done
show goal647: "CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant SIAGO_WritePull_nextGOPendingIs_otherside assms i2160 i582 nextGOPendingIs_general_rule_3_0) done
show goal648: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i871 nextDTHDataFrom_otherside_rule_3_0 nextReqIs_SIAGO_WritePull_IMAD_invariant2 remove_instr_HSTATE) done
show goal649: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i255) done
show goal650: "HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant SIAGO_WritePull_nextGOPendingIs_otherside assms i215 i2160 i582 nextDTHDataFrom_otherside_rule_3_0 reqresps1_SIAGO_WritePull_aux1 reqresps1_remove_op reqresps_empty_noGOPendingIs1) done
show goal651: "HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant aux192 i2160 nextDTHDataFrom_otherside_rule_3_0) done
show goal652: "HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis CSTATE_inequality_invariant CSTATE_otherside_rule_4_0 CSTATE_remove_op HSTATE_SIAGO_WritePull_invariant Invalid_not_eq_MIA SharedSnpInv'_MAD_CSTATE_invariant5 assms i216 i2160 i221 i773 i813 i945 nextDTHDataFrom_otherside_rule_3_0) done
show goal653: "HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant aux192 i2160 nextDTHDataFrom_otherside_rule_3_0) done
show goal654: "HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i224) done
show goal655: "HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i224) done
show goal656: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i217) done
show goal657: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> nextReqIs RdOwn ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis CSTATE_SIAGO_WritePull_IMAD_invariant CSTATE_otherside_rule_4_0 CSTATE_remove_op SharedSnpInv'_MAD_CSTATE_invariant5 i2160 i828 nextGOPendingIs_general_rule_3_0 nextReqIs_SIAGO_WritePull_IMAD_invariant2) done
show goal658: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i211) done
show goal659: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(139) i216) done
show goal660: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> (CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1)"
apply  (insert assms) apply (smt (verit) i211) done
show goal661: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> (CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0)"
apply  (insert assms) apply (smt (verit) i211) done
show goal662: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1)"
apply  (insert assms) apply (smt (verit) i211) done
show goal663: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0)"
apply  (insert assms) apply (smt (verit) i211) done
show goal664: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> (CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1)"
apply  (insert assms) apply (smt (verit) i211) done
show goal665: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> (CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0)"
apply  (insert assms) apply (smt (verit) i211) done
show goal666: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1)"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(141) MESI_State.distinct(95) i207 i211 i216) done
show goal667: "CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0)"
apply  (insert assms) apply (smt (verit) i211) done
show goal668: "HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i214) done
show goal669: "HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i213) done
show goal670: "HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant Invalid_not_eq_MIA i216) done
show goal671: "HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant aux192 i2160 nextDTHDataFrom_otherside_rule_3_0) done
show goal672: "HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) HOST_State.distinct(135) HOST_State.distinct(137) HOST_State.distinct(139) HOST_State.distinct(265) HOST_State.distinct(267) HOST_State.distinct(269) HSTATE_invariant3 i2201) done
show goal673: "HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant aux192 i2160 nextDTHDataFrom_otherside_rule_3_0) done
show goal674: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> (htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<or> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1)"
apply  (insert assms) apply (smt (verit) i217) done
show goal675: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> (htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<or> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0)"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant HTDDataPending_htddatas_invariant1 MESI_State.distinct(149) MESI_State.distinct(169) i207 i216) done
show goal676: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i217) done
show goal677: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(167) i216) done
show goal678: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i217) done
show goal679: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis assms i2160 i316 nextGOPendingIs_general_rule_3_0 snpresps2_SIAGO_WritePull snpresps2_remove_op) done
show goal680: "CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> (CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1)"
apply  (insert assms) apply (smt (verit) i211) done
show goal681: "CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> (CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0)"
apply  (insert assms) apply (smt (verit) i211) done
show goal682: "CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i211) done
show goal683: "CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE ISA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(141) MESI_State.distinct(95) i216) done
show goal684: "CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i211) done
show goal685: "CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) HTDDataPending_htddatas_invariant1 i207) done
show goal686: "CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i211) done
show goal687: "CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(149) i216) done
show goal688: "CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i213) done
show goal689: "CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i214) done
show goal690: "HSTATE SD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i223) done
show goal691: "HSTATE SD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i223) done
show goal692: "HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i222) done
show goal693: "HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i222) done
show goal694: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i211) done
show goal695: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> CSTATE ISAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) empty_no_snoop2 i214) done
show goal696: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i211) done
show goal697: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i255) done
show goal698: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i211) done
show goal699: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis g302aux i213 i2160 nextGOPendingIs_general_rule_3_0 snpresps1_SIAGO_WritePull snpresps1_remove_op snps1_SIAGO_WritePull) done
show goal700: "CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i215 reqresps_empty_noGOPendingIs1) done
show goal701: "CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i255) done
show goal702: "CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i215 reqresps_empty_noGOPendingIs1) done
show goal703: "CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant Invalid_not_eq_MIA i216) done
show goal704: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i255) done
show goal705: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i579 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal706: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> (\<not> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> nextGOPendingIs GO_WritePullDrop ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> (\<not> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> nextGOPendingIs GO_WritePullDrop ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1)"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i579 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal707: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextSnpRespIs RspIFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis CSTATE_otherside_rule_4_0 CSTATE_remove_op HSTATE_SIAGO_WritePull_invariant SIAGO_WritePull_nextSnpRespIs_sameside SharedSnpInv'_MAD_CSTATE_invariant5 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i878 nextGOPendingIs_general_rule_3_0 nextHTDDataPending_general_rule_3_0 remove_instr_HSTATE) done
show goal708: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextSnpRespIs RspIFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms i2160 i316 nextGOPendingIs_general_rule_3_0 nextSnpRespIs_invariant2 snpresps2_SIAGO_WritePull snpresps2_remove_op) done
show goal709: "length (dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])) \<le> 1"
apply  (insert assms) apply (smt (verit) aux4_r113 aux5_r113) done
show goal710: "length (dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])) \<le> 1"
apply  (insert assms) apply (metis aux542 dthdatas2_SIAGO_WritePull dthdatas2_remove_op i2160 le0 list.size(3) nextGOPendingIs_general_rule_3_0) done
show goal711: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i215 reqresps_empty_noGOPendingIs1) done
show goal712: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i255) done
show goal713: "HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) HOST_State.distinct(135) HOST_State.distinct(137) HOST_State.distinct(139) HOST_State.distinct(265) HOST_State.distinct(267) HOST_State.distinct(269) HSTATE_invariant3 i2201) done
show goal714: "HSTATE MAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant aux192 i2160 nextDTHDataFrom_otherside_rule_3_0) done
show goal715: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<longrightarrow> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis g302aux i2160 nextGOPendingIs_XIAGOWP_otherside1 snpresps1_SIAGO_WritePull snpresps1_remove_op) done
show goal716: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> [] \<longrightarrow> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis assms i119 i2160 nextGOPendingIs_XIAGOWP_otherside1 reqresps_empty_noGOPendingIs1 snpresps2_SIAGO_WritePull snpresps2_remove_op) done
show goal717: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i211) done
show goal718: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i225) done
show goal719: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> (htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<or> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1)"
apply  (insert assms) apply (smt (verit) i211) done
show goal720: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> (htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<or> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0)"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant HTDDataPending_htddatas_invariant1 MESI_State.distinct(149) MESI_State.distinct(169) i207 i216) done
show goal721: "CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> (htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<or> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1)"
apply  (insert assms) apply (smt (verit) i211) done
show goal722: "CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> (htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<or> CSTATE ISDI ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0)"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant HTDDataPending_htddatas_invariant1 MESI_State.distinct(149) MESI_State.distinct(169) i207 i216) done
show goal723: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i217) done
show goal724: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis aux542 dthdatas2_SIAGO_WritePull dthdatas2_remove_op i2160 nextGOPendingIs_general_rule_3_0) done
show goal725: "nextSnpRespIs RspIHitSE ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(149) MESI_State.distinct(169) i216) done
show goal726: "nextSnpRespIs RspIHitSE ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis CSTATE_SIAGO_WritePull_IMAD_invariant SIAGO_WritePull_nextSnpRespIs_otherside assms i2160 i316 nextGOPendingIs_general_rule_3_0 nextSnpRespIs_property2) done
show goal727: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i207) done
show goal728: "CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(167) i216) done
show goal729: "CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i207) done
show goal730: "CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(167) i216) done
show goal731: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i211) done
show goal732: "CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(167) i216) done
show goal733: "CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i211) done
show goal734: "CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(167) i216) done
show goal735: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i211) done
show goal736: "CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(167) i216) done
show goal737: "HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i225) done
show goal738: "HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i225) done
show goal739: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i211) done
show goal740: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(167) i216) done
show goal741: "HSTATE InvalidM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i579 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal742: "HSTATE IB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (metis CSTATE_disj1 CSTATE_otherside_rule_6 CSTATE_remove_op MESI_State.distinct(167) SharedSnpInv'_MAD_CSTATE_invariant5 hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i216 i2160 i916 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal743: "HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i224) done
show goal744: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextSnpRespIs RspIHitSE ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i255) done
show goal745: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextSnpRespIs RspIHitSE ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant SIAGO_WritePull_nextSnpRespIs_otherside hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i919 nextGOPendingIs_general_rule_3_0 nextReqIs_SIAGO_WritePull_IMAD_invariant2 remove_instr_HSTATE) done
show goal746: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i217) done
show goal747: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) HTDDataPending_htddatas_invariant1 i207) done
show goal748: "HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i213 i214) done
show goal749: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i207) done
show goal750: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) empty_no_snoop_variant2 i214) done
show goal751: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextSnpRespIs RspIFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i255) done
show goal752: "CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextSnpRespIs RspIFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) CSTATE_different1 MESI_State.distinct(167) i216) done
show goal753: "CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> HSTATE SA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i220) done
show goal754: "CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> HSTATE SA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i217) done
show goal755: "CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i207) done
show goal756: "CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis CSTATE_SIAGO_WritePull_IMAD_invariant CSTATE_SIAGO_WritePull_otherside_invariant2 CSTATE_otherside_rule_4_0 CSTATE_remove_op HTDDataPending_htddatas_invariant2 SIAGO_WritePull_nextHTDDataPending_real SharedSnpInv'_MAD_CSTATE_invariant5 assms i216 i2160 i381 i930 nextGOPendingIs_general_rule_3_0 nextHTDDataPending_def nextHTDDataPending_remove_op reqresps_empty_noGOPendingIs1) done
show goal757: "CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPendingState Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i211) done
show goal758: "CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPendingState Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = [] \<and> htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis CSTATE_otherside_rule_4_0 CSTATE_remove_op HTDDataPending_htddatas_invariant2 SharedSnpInv'_MAD_CSTATE_invariant5 g302aux htddatas2_SIAGO_WritePull htddatas2_remove_op i213 i2160 i930 nextGOPending_overlooked_reqresp_rule_3_0 snpresps1_SIAGO_WritePull snpresps1_remove_op snps1_SIAGO_WritePull) done
show goal759: "(CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPendingState Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> (CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i211) done
show goal760: "(CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPendingState Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> (CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i313 nextGOPending_overlooked_reqresp_rule_3_0 remove_instr_HSTATE) done
show goal761: "(CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPendingState Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> []"
apply  (insert assms) apply (smt (verit) i211) done
show goal762: "(CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPendingState Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> []"
apply  (insert assms) apply (smt (verit) i225) done
show goal763: "(CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPendingState Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i211) done
show goal764: "(CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPendingState Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) HOST_State.distinct(269) HOST_State.distinct(285) HOST_State.distinct(287) HOST_State.distinct(289) HOST_State.distinct(377) HOST_State.distinct(379) HSTATE_invariant3 i2201) done
show goal765: "CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPendingState Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i211) done
show goal766: "CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPendingState Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i214) done
show goal767: "CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPendingState Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> reqs1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i211) done
show goal768: "CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPendingState Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> reqs2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (metis i2160 i95 nextGOPending_DeviceSIAGO_WritePull nextGOPending_overlooked_reqresp_rule_3_0 reqresps_empty_noGOPending2 reqs2_SIAGO_WritePull reqs2_remove_op) done
show goal769: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextSnpRespIs RspIFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i207) done
show goal770: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextSnpRespIs RspIFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant SIAGO_WritePull_nextHTDDataPending_real SIAGO_WritePull_nextSnpRespIs_otherside hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i944 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal771: "HSTATE SB ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis CSTATE_inequality_invariant CSTATE_otherside_rule_4_0 CSTATE_remove_op HSTATE_SIAGO_WritePull_invariant Invalid_not_eq_MIA SharedSnpInv'_MAD_CSTATE_invariant5 assms i216 i2160 i221 i773 i813 i945 nextGOPendingIs_general_rule_3_0) done
show goal772: "nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i254 reqs1_empty_not_nextReqIs_general_invariant) done
show goal773: "nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis CSTATE_SIAGO_WritePull_IMAD_invariant CSTATE_otherside_rule_4_0 CSTATE_remove_op SharedSnpInv'_MAD_CSTATE_invariant5 i2160 i947 nextGOPendingIs_general_rule_3_0 nextReqIs_SIAGO_WritePull_IMAD_invariant2) done
show goal774: "nextSnpRespIs RspIHitSE ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (metis CSTATE_SIAGO_WritePull_IMAD_invariant SIAGO_WritePull_nextSnpRespIs_sameside g302aux i2160 nextSnpRespIs_general_rule_3_0 nextSnpRespIs_property1) done
show goal775: "nextSnpRespIs RspIHitSE ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (metis CSTATE_SIAGO_WritePull_IMAD_invariant aux192 i2160 nextDTHDataFrom_otherside_rule_3_0) done
show goal776: "nextSnpRespIs RspIFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i254 reqs1_empty_not_nextReqIs_general_invariant) done
show goal777: "nextSnpRespIs RspIFwdM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> nextReqIs CleanEvictNoData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (metis CSTATE_SIAGO_WritePull_IMAD_invariant SIAGO_WritePull_nextSnpRespIs_otherside assms i2160 i316 nextGOPendingIs_general_rule_3_0 nextSnpRespIs_invariant2) done
show goal778: "CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextSnoopIs SnpData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) i211) done
show goal779: "CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextSnoopIs SnpData ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
apply  (insert assms) apply (smt (verit) empty_no_snoop2 i214) done
show goal780: "(CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPendingIs GO_WritePullDrop ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> (CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i215 reqresps_empty_noGOPendingIs1) done
show goal781: "(CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPendingIs GO_WritePullDrop ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> (CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i313 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE) done
show goal782: "(CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPendingIs GO ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPendingState Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> GTS ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> (CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i215 reqresps_empty_noGOPendingIs1) done
show goal783: "(CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPendingIs GO ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPendingState Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> GTS ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> (CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> (CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (metis HSTATE_SIAGO_WritePull_invariant assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i313 nextGOPending_overlooked_reqresp_rule_3_0 remove_instr_HSTATE) done
show goal784: "(CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPendingIs GO ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPendingState Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> GTS ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> dthdatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> []"
apply  (insert assms) apply (smt (verit) i225) done
show goal785: "(CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPendingIs GO ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPendingState Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> GTS ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> HSTATE MD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<noteq> []"
apply  (insert assms) apply (smt (verit) i225) done
show goal786: "(CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPendingIs GO ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPendingState Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> GTS ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i215 reqresps_empty_noGOPendingIs1) done
show goal787: "(CSTATE SIAC ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPendingIs GO ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPendingState Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> \<not> CSTATE IIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> GTS ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> (CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0) \<and> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) HOST_State.distinct(269) HOST_State.distinct(285) HOST_State.distinct(287) HOST_State.distinct(289) HOST_State.distinct(377) HOST_State.distinct(379) HSTATE_invariant3 i2201) done
show goal788: "HSTATE SD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i214) done
show goal789: "HSTATE SD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i213) done
show goal790: "HSTATE SD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i215) done
show goal791: "HSTATE SD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
apply  (insert assms) apply (smt (verit) i223) done
show goal792: "HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 0 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> nextGOPendingIs GO_WritePullDrop ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i224) done
show goal793: "HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> nextGOPendingIs GO_WritePullDrop ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i224) done
show goal794: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<or> nextGOPendingIs GO_WritePullDrop ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i224) done
show goal795: "CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> nextGOPendingIs GO_WritePull ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<and> HSTATE ID ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE SIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<or> nextGOPendingIs GO_WritePullDrop ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply  (insert assms) apply (smt (verit) i224) done
show goal796: "HSTATE SAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextDTHDataFrom 1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<longrightarrow> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<and> \<not> CSTATE MIA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply  (insert assms) apply (smt (verit) i222) done
qed
qed
find_theorems "_ = _ = _"
lemma SIAGO_WritePull_helper: shows "f T \<Longrightarrow>
 (\<And>T m dthd.
  f T \<and> CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<Longrightarrow>
  f ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])) \<Longrightarrow>
 Lall
  (if CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 
   then [let devID = nat_to_id 0; v = read_dev_value 0 T; tid = nextGOID T 0; dthd = D2HData tid v (clock T);
 m = nextGO T 0
   in if 0 = 0 then  T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ devID +=d2hd dthd] [ -=i 0]
   else  T\<lparr>buffer2 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ devID +=d2hd dthd] [ -=i 1]]
   else [])
  f"
apply(simp only:simp_thms(6) if_True)
using general_helper
by (metis Lall.simps(1) Lall.simps(2) nat_to_id.simps(1) one_mod_two_eq_one plus_nat.add_0)
lemma SIAGO_WritePull_coherent: shows "
SWMR_state_machine T \<Longrightarrow> Lall (SIAGO_WritePull' T 0) SWMR_state_machine
"
unfolding SIAGO_WritePull'_def consumeGOSendData_def
apply(insert SIAGO_WritePull'_coherent_aux_simpler)
using general_helper
by (metis SIAGO_WritePull'_coherent_aux_simpler SIAGO_WritePull_helper)
end