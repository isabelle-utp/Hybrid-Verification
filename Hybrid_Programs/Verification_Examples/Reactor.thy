section \<open> Nuclear Reactor \<close>

theory Reactor
  imports "Hybrid-Verification.Hybrid_Verification"
begin

dataspace original_reactor =
  constants 
    T\<^sub>M :: real \<comment> \<open> Max temperature reaction threshold\<close>
    T\<^sub>m :: real \<comment> \<open> Min temperature reaction threshold\<close>
    t\<^sub>R :: real \<comment> \<open> rod resting time \<close>
    K\<^sub>u\<^sub>p :: real \<comment> \<open> reactor's temperature-increase rate \<close>
    K\<^sub>1 :: real \<comment> \<open> reactor's temperature-decrease rate by rod 1 \<close>
    K\<^sub>2 :: real \<comment> \<open> reactor's temperature-decrease rate by rod 2 \<close>
  assumes Tm_ge0: "0 < T\<^sub>m" 
    and Tm_le: "T\<^sub>m < T\<^sub>M" 
    and tR_ge0: "0 < t\<^sub>R" 
    and Ks_ge0: 
      "0 < K\<^sub>u\<^sub>p"
      "0 < K\<^sub>1"
      "0 < K\<^sub>2"
    and rest_constraints: 
      "t\<^sub>R < 2 * (T\<^sub>M - T\<^sub>m) / K\<^sub>u\<^sub>p + (T\<^sub>M - T\<^sub>m) / K\<^sub>1"
      "t\<^sub>R < 2 * (T\<^sub>M - T\<^sub>m) / K\<^sub>u\<^sub>p + (T\<^sub>M - T\<^sub>m) / K\<^sub>2"
      "(T\<^sub>M - T\<^sub>m) / K\<^sub>u\<^sub>p < t\<^sub>R"
  variables
    rod1 :: bool
    rod2 :: bool
    temp :: real
    time1 :: real
    time2 :: real
    T :: real
    t :: real

context original_reactor
begin

text \<open> The original reactor model adds the guards @{term "$T \<ge> T\<^sub>M"} 
and @{term "$T \<ge> T\<^sub>m"} to the ODEs. This forces the reactor's temperature
to remain in a "safe" range. Thus, we provide the control below to produce 
the intended dynamics of the original model. \<close>

definition "reactor_ctrl \<equiv>
  temp ::= T; 
  time1 ::= time1 + t; 
  time2 ::= time2 + t;
  t ::= 0;
  IF temp = T\<^sub>m \<and> rod1 THEN rod1 ::= False; time1 ::= 0
  ELSE (IF temp = T\<^sub>m \<and> rod2 THEN rod2 ::= False; time2 ::= 0
  ELSE (IF temp = T\<^sub>M \<and> \<not> rod1 \<and> \<not> rod2 THEN 
    (IF time1 > t\<^sub>R THEN rod1 ::= True
    ELSE (IF time2 > t\<^sub>R THEN rod2 ::= True))))
"

definition "reactor_ode \<equiv>
  IF rod1 THEN {T` = - K\<^sub>1, t` = 1 | T \<ge> T\<^sub>m}
  ELSE IF rod2 THEN {T` = - K\<^sub>2, t` = 1 | T \<ge> T\<^sub>m}
  ELSE {T` = K\<^sub>u\<^sub>p, t` = 1 | T \<le> T\<^sub>M}
"

definition "reactor = (reactor_ctrl; reactor_ode)\<^sup>*"

lemma [local_flow]: "local_flow_on [T \<leadsto> K, t \<leadsto> 1] (T +\<^sub>L t) UNIV UNIV
  (\<lambda>\<tau>. [T \<leadsto> K * \<tau>  + T, t \<leadsto> \<tau> + t])"
  by local_flow_on_auto

lemma safe1: 
" H{T\<^sub>m \<le> T \<and> T \<le> T\<^sub>M} 
  reactor 
  {T\<^sub>m \<le> T \<and> T \<le> T\<^sub>M}"
  unfolding reactor_def reactor_ctrl_def reactor_ode_def
  unfolding loopi_def[symmetric, where I="(T\<^sub>m \<le> T \<and> T \<le> T\<^sub>M)\<^sub>e"]
  apply intro_loops
  using Ks_ge0 apply (wlp_full local_flow: local_flow)
  by (safe; clarsimp simp: add_increasing add_increasing2 diff_le_eq)
    expr_auto+

lemma safe2: 
" H{(rod1 \<longrightarrow> \<not> rod2) \<and> (rod2 \<longrightarrow> \<not> rod1)} 
  reactor 
  {(rod1 \<longrightarrow> \<not> rod2) \<and> (rod2 \<longrightarrow> \<not> rod1)}"
  unfolding reactor_def reactor_ctrl_def reactor_ode_def
  unfolding loopi_def[symmetric, where I="((rod1 \<longrightarrow> \<not> rod2) \<and> (rod2 \<longrightarrow> \<not> rod1))\<^sub>e"]
  by (wlp_full local_flow: local_flow)

abbreviation "time_up \<equiv> (T\<^sub>M - T\<^sub>m) / K\<^sub>u\<^sub>p"  (* t\<^sub>u\<^sub>p *)

abbreviation "time_up_down1 \<equiv> time_up + (T\<^sub>M - T\<^sub>m) / K\<^sub>1"  (* t\<^sub>\<up>\<^sub>\<down>\<^sub>1 *)

abbreviation "time_up_down2 \<equiv> time_up + (T\<^sub>M - T\<^sub>m) / K\<^sub>2"  (* t\<^sub>\<up>\<^sub>\<down>\<^sub>2 *)

abbreviation "cycle1 \<equiv> time_up + time_up_down1" (* t\<^sub>c\<^sub>1 *)

abbreviation "cycle2 \<equiv> time_up + time_up_down2" (* t\<^sub>c\<^sub>2 *)

(* 
      |
T\<^sub>M _ _|_ _ _ _ _ _ __ _ _ _ _ _ __ _ _ _ _ _ __ _ _ _ _ _ 
      |     /|\<^bsub>               /|\<setminus>          /\<^bsub>
      |    / |  \<^bsub>            / | \<setminus>        /   \<^bsub>
\<dots>    |   /  |    \<^bsub>         /  |  \<setminus>      /          \<dots>
      |  /   |      \<^bsub>      /   |   \<setminus>    /
    \<setminus> | /    |        \<^bsub>   /    |    \<setminus>  /
T\<^sub>m_ _\<setminus>|/_____|__________\<^bsub>/_____|_____\<setminus>/____________________
      |      |          |      |
             t\<^sub>u\<^sub>p        t\<^sub>\<up>\<^sub>\<down>\<^sub>2    t\<^sub>c\<^sub>2
*)

expression inv is "
  (rod1 \<longrightarrow> \<not> rod2) \<and> (rod2 \<longrightarrow> \<not> rod1) \<and> (T\<^sub>m \<le> T \<and> T \<le> T\<^sub>M)
  \<and> (rod1 \<and> \<not> rod2 \<longrightarrow> (
      T = T\<^sub>M - K\<^sub>1 * (time2 + t - time_up)
      \<and> T = T\<^sub>M - K\<^sub>1 * (time1 + t - cycle2)))
  \<and> (\<not> rod1 \<and> rod2 \<longrightarrow> (
      T = T\<^sub>M - K\<^sub>2 * (time2 + t - cycle1)
      \<and> T = T\<^sub>M - K\<^sub>2 * (time1 + t - time_up)))
  \<and> (\<not> rod1 \<and> \<not> rod2 \<longrightarrow> 
      (T = T\<^sub>m + K\<^sub>u\<^sub>p * (time1 + t)
      \<and> T = T\<^sub>m + K\<^sub>u\<^sub>p * (time2 + t - time_up_down1))
    \<or> (T = T\<^sub>m + K\<^sub>u\<^sub>p * (time2 + t)
      \<and> T = T\<^sub>m + K\<^sub>u\<^sub>p * (time1 + t - time_up_down2)))"

lemma 
  "`inv \<longrightarrow> rod1 \<and> \<not> rod2 \<longrightarrow> time1 + t = cycle2 \<longleftrightarrow> time2 + t = time_up`"
  "`inv \<longrightarrow> rod1 \<and> \<not> rod2 \<longrightarrow> time2 + t = time_up_down1 \<longleftrightarrow> T = T\<^sub>m`"
  "`inv \<longrightarrow> rod1 \<and> \<not> rod2 \<longrightarrow> cycle2 \<le> time1 + t`"
  "`inv \<longrightarrow> rod1 \<and> \<not> rod2 \<longrightarrow> time_up \<le> time2 + t \<and> time2 + t \<le> time_up_down1`"
  "`inv \<longrightarrow> \<not> rod1 \<and> rod2 \<longrightarrow> time2 + t = cycle1 \<longleftrightarrow> time1 + t = time_up`"
  "`inv \<longrightarrow> \<not> rod1 \<and> rod2 \<longrightarrow> time1 + t = time_up_down2 \<longleftrightarrow> T = T\<^sub>m`"
  "`inv \<longrightarrow> \<not> rod1 \<and> rod2 \<longrightarrow> cycle1 \<le> time2 + t`"
  "`inv \<longrightarrow> \<not> rod1 \<and> rod2 \<longrightarrow> time_up \<le> time1 + t \<and> time1 + t \<le> time_up_down2`"
  subgoal 
    apply (expr_simp; clarsimp)
    using Ks_ge0
    by fastforce
  subgoal 
    using Ks_ge0 Tm_le Tm_ge0
    apply (expr_simp; clarsimp)
    apply (intro conjI iffI)
    by fastforce
      (clarsimp simp: field_simps)
  subgoal 
    using Ks_ge0 Tm_le Tm_ge0
    by (expr_simp; clarsimp simp add: zero_compare_simps(1-8))
  subgoal
    using Ks_ge0 Tm_le Tm_ge0
    apply (expr_simp; clarsimp simp add: zero_compare_simps(1-8))
    by (metis Groups.add_ac(2) Groups.mult_ac(2) diff_le_eq le_diff_eq pos_le_divide_eq)
  subgoal 
    apply (expr_simp; clarsimp)
    using Ks_ge0
    by fastforce
  subgoal 
    using Ks_ge0 Tm_le Tm_ge0
    apply (expr_simp; clarsimp)
    apply (intro conjI iffI)
    apply (smt (verit, ccfv_SIG) divide_pos_pos factor_fracR(3) zero_compare_simps(8))
    by (smt (verit, best) factor_fracR(3) zero_compare_simps(4,8))
  subgoal
    using Ks_ge0 Tm_le Tm_ge0
    by (expr_simp; clarsimp simp add: zero_compare_simps(1-8))
  subgoal
    using Ks_ge0 Tm_le Tm_ge0
    apply (expr_simp; clarsimp simp add: zero_compare_simps(1-8))
    by (smt (verit) factor_fracR(3) zero_compare_simps(1-8))
  done

(* this first attempt is implied by inv *)
expression inv2 is "
  (rod1 \<longrightarrow> \<not> rod2) \<and> (rod2 \<longrightarrow> \<not> rod1) \<and> (T\<^sub>m \<le> T \<and> T \<le> T\<^sub>M)
  \<and> (rod1 \<and> \<not> rod2 \<longrightarrow> (
      (time1 + t = cycle2 \<longleftrightarrow> time2 + t = time_up)
      \<and> (time2 + t = time_up_down1 \<longleftrightarrow> T = T\<^sub>m)
      \<and> (cycle2 \<le> time1 + t \<and> time_up \<le> time2 + t \<and> time2 + t \<le> time_up_down1)))
  \<and> (\<not> rod1 \<and> rod2 \<longrightarrow> (
      (time2 + t = cycle1 \<longleftrightarrow> time1 + t = time_up)
      \<and> (time1 + t = time_up_down2 \<longleftrightarrow> T = T\<^sub>m)
      \<and> (cycle1 \<le> time2 + t \<and> time_up \<le> time1 + t \<and> time1 + t \<le> time_up_down2)))
  \<and> (\<not> rod1 \<and> \<not> rod2 \<longrightarrow> 
      ((time1 + t = 0 \<longleftrightarrow> time2 + t = time_up_down1)
      \<and> (time1 + t = time_up \<longleftrightarrow> T = T\<^sub>M)
      \<and> (time1 + t = time_up \<longleftrightarrow> time2 + t = cycle1)
      \<and> (0 \<le> time1 + t \<and> time1 + t \<le> time_up \<and> time_up_down1 \<le> time2 + t \<and> time2 + t \<le> cycle1))
    \<or> ((time2 + t = 0 \<longleftrightarrow> time1 + t = time_up_down2)
      \<and> (time2 + t = time_up \<longleftrightarrow> T = T\<^sub>M)
      \<and> (time2 + t = time_up \<longleftrightarrow> time1 + t = cycle2)
      \<and> (0 \<le> time2 + t \<and> time2 + t \<le> time_up \<and> time_up_down2 \<le> time1 + t \<and> time1 + t \<le> cycle2)))"


lemma safe_inv: "H{inv} reactor {inv}"
  unfolding reactor_def reactor_ctrl_def reactor_ode_def
  unfolding loopi_def[symmetric, where I="inv", unfolded inv_def]
  apply intro_loops
    apply (symbolic_exec; symbolic_exec?; symbolic_exec?; symbolic_exec?; symbolic_exec?; symbolic_exec?)
  subgoal 
    (* case 1:
        \<bullet> IF temp = T\<^sub>m \<and> rod1 THEN rod1 ::= False; time1 ::= 0
        \<bullet> rod1  *)
    by wlp_full
  subgoal for time1\<^sub>0 time2\<^sub>0 \<tau> rod1\<^sub>0 old_time1
    (* case 2:
        \<bullet> IF temp = T\<^sub>m \<and> rod1 THEN rod1 ::= False; time1 ::= 0
        \<bullet> \<not> rod1 \<and> rod2 *)
    using Ks_ge0 Tm_le
    by wlp_full
  subgoal for time1\<^sub>0 time2\<^sub>0 \<tau> rod1\<^sub>0 old_time1
    (* case 3:
        \<bullet> IF temp = T\<^sub>m \<and> rod1 THEN rod1 ::= False; time1 ::= 0
        \<bullet> \<not> rod1 \<and> \<not> rod2 *)
    apply (wlp_full local_flow: local_flow)
    apply (rename_tac s tmax)
    using Ks_ge0 Tm_le Tm_ge0
    apply (intro conjI iffI)
     apply (erule_tac x=tmax in allE, clarsimp)
    apply (erule_tac x=tmax in allE, clarsimp)
    apply (smt (verit, ccfv_threshold) factor_fracR(3) mult_eq_0_iff)
    done
  subgoal
    (* case 4:
        \<bullet> ELSE IF temp = T\<^sub>m \<and> rod2 THEN rod2 ::= False; time2 ::= 0
        \<bullet> rod1  *)
    by wlp_full
  subgoal for time1\<^sub>0 time2\<^sub>0 \<tau> rod2\<^sub>0 old_time2
    (* case 5:
        \<bullet> ELSE IF temp = T\<^sub>m \<and> rod2 THEN rod2 ::= False; time2 ::= 0
        \<bullet> \<not> rod1 \<and> rod2 *)
    using Ks_ge0 Tm_le
    by wlp_full
  subgoal for time1\<^sub>0 time2\<^sub>0 \<tau> rod2\<^sub>0 old_time2
    (* case 6:
        \<bullet> ELSE IF temp = T\<^sub>m \<and> rod2 THEN rod2 ::= False; time2 ::= 0
        \<bullet> \<not> rod1 \<and> \<not> rod2 *)
    apply (wlp_full local_flow: local_flow)
    apply (rename_tac s tmax)
    using Ks_ge0 Tm_le Tm_ge0
    apply (intro conjI iffI)
    apply (erule_tac x=tmax in allE, clarsimp)
    apply (smt (verit, best) diff_divide_distrib divide_pos_pos factor_fracR(3) zero_compare_simps(4,8))
    done
  subgoal for time1\<^sub>0 time2\<^sub>0 \<tau> rod1\<^sub>0
    (* case 7:
        \<bullet> ELSE IF temp = T\<^sub>M \<and> \<not> rod1 \<and> \<not> rod2 THEN 
            IF time1 > t\<^sub>R THEN rod1 ::= True
        \<bullet> rod1 *)
    using Ks_ge0 Tm_le Tm_ge0 Tm_le rest_constraints
    apply -
    apply (rule local_flow[THEN hl_ode_frame], simp, simp add: usubst usubst_eval, expr_taut, expr_simp)
    apply clarify
    apply (rename_tac s tmax)
    apply (simp only: , clarsimp)
    apply (smt (verit, best) diff_divide_distrib divide_pos_pos nonzero_mult_div_cancel_left)
    done
  subgoal for time1\<^sub>0 time2\<^sub>0 \<tau> rod1\<^sub>0
    (* case 8:
        \<bullet> ELSE IF temp = T\<^sub>M \<and> \<not> rod1 \<and> \<not> rod2 THEN 
            IF time1 > t\<^sub>R THEN rod1 ::= True
        \<bullet> \<not> rod1 \<and> rod2 *)
    apply wlp_full
    done
  subgoal for time1\<^sub>0 time2\<^sub>0 \<tau> rod1\<^sub>0
    (* case 9:
        \<bullet> ELSE IF temp = T\<^sub>M \<and> \<not> rod1 \<and> \<not> rod2 THEN 
            IF time1 > t\<^sub>R THEN rod1 ::= True
        \<bullet> \<not> rod1 \<and> \<not> rod2 *)
    apply wlp_full
    done
  subgoal for time1\<^sub>0 time2\<^sub>0 \<tau> rod2\<^sub>0
    (* case 10:
        \<bullet> ELSE IF temp = T\<^sub>M \<and> \<not> rod1 \<and> \<not> rod2 THEN 
            ELSE IF time2 > t\<^sub>R THEN rod2 ::= True
        \<bullet> rod1 *)
    apply wlp_full
    done
  subgoal for time1\<^sub>0 time2\<^sub>0 \<tau> rod2\<^sub>0
    (* case 11:
        \<bullet> ELSE IF temp = T\<^sub>M \<and> \<not> rod1 \<and> \<not> rod2 THEN 
            ELSE IF time2 > t\<^sub>R THEN rod2 ::= True
        \<bullet> \<not> rod1 \<and> rod2 *)
    using Ks_ge0 Tm_le rest_constraints
    apply -
    apply (rule local_flow[THEN hl_ode_frame], simp, simp add: usubst usubst_eval, expr_taut, expr_simp)
    apply clarify
    apply (rename_tac s tmax)
    apply (simp only: , clarsimp)
    apply (intro conjI iffI)
    apply fastforce+
    done
  subgoal for time1\<^sub>0 time2\<^sub>0 \<tau> rod1\<^sub>0
    (* case 12:
        \<bullet> ELSE IF temp = T\<^sub>M \<and> \<not> rod1 \<and> \<not> rod2 THEN 
            ELSE IF time2 > t\<^sub>R THEN rod2 ::= True
        \<bullet> \<not> rod1 \<and> \<not> rod2 *)
    apply wlp_full
    done
  subgoal for time1\<^sub>0 time2\<^sub>0 \<tau>
    (* case 13:
        \<bullet> ELSE IF temp = T\<^sub>M \<and> \<not> rod1 \<and> \<not> rod2 THEN 
            ELSE skip
        \<bullet> rod1 *)
    apply wlp_full
    done
  subgoal for time1\<^sub>0 time2\<^sub>0 \<tau>
    (* case 14:
        \<bullet> ELSE IF temp = T\<^sub>M \<and> \<not> rod1 \<and> \<not> rod2 THEN 
            ELSE skip
        \<bullet> \<not> rod1 \<and> rod2 *)
    apply wlp_full
    done
  subgoal for time1\<^sub>0 time2\<^sub>0 \<tau>
    (* case 15:
        \<bullet> ELSE IF temp = T\<^sub>M \<and> \<not> rod1 \<and> \<not> rod2 THEN 
            ELSE skip
        \<bullet> \<not> rod1 \<and> \<not> rod2 *)
    using Ks_ge0 Tm_le
    apply -
    apply (rule local_flow[THEN hl_ode_frame], simp, simp add: usubst usubst_eval, expr_taut, expr_simp)
    apply clarify
    apply (rename_tac s tmax)
    apply (simp only: , clarsimp)
    apply (intro conjI iffI)
     apply fastforce
    apply argo
    done
  subgoal for time1\<^sub>0 time2\<^sub>0 \<tau>
    (* case 16:
        \<bullet> ELSE skip
        \<bullet> rod1 *)
    using Ks_ge0 Tm_le
    apply (wlp_full local_flow: local_flow)
    apply (rename_tac s tmax)
    apply (intro conjI iffI; clarsimp simp: zero_compare_simps(1-8))
    apply (smt (verit, ccfv_threshold) zero_compare_simps(4))
    apply argo
    apply (smt (verit, ccfv_SIG) nat_distrib(2))
    done
  subgoal for time1\<^sub>0 time2\<^sub>0 \<tau>
    (* case 17:
        \<bullet> ELSE skip
        \<bullet> \<not> rod1 \<and> rod2 *)
    using Ks_ge0 Tm_le
    apply (wlp_full local_flow: local_flow)
    apply (rename_tac s tmax)
    apply (intro conjI iffI; clarsimp simp: zero_compare_simps(1-8))
    apply (smt (verit, ccfv_threshold) zero_compare_simps(4))
    apply argo
    apply (smt (verit, ccfv_SIG) nat_distrib(2))
    done
  subgoal for time1\<^sub>0 time2\<^sub>0 \<tau>
    (* case 18:
        \<bullet> ELSE skip
        \<bullet> \<not> rod1 \<and> \<not> rod2 *)
    using Ks_ge0 Tm_le
    apply (wlp_full local_flow: local_flow)
    apply (rename_tac s tmax)
    apply (intro conjI iffI; clarsimp simp: zero_compare_simps(1-8))
    apply (smt (verit, best) Rings.ring_distribs(1) mult_le_cancel_left_pos)
    done
  using Ks_ge0 Tm_le
  unfolding inv_def
  by ((expr_simp; clarsimp simp: zero_compare_simps(1-8)), (intro conjI iffI; force))+

lemma reactor_safe: "
  H{(T = T\<^sub>m \<and> time1 = 0 \<and> time2 = time_up_down1 \<and> \<not> rod1 \<and> \<not> rod2 \<and> t = 0)
  \<or> (T = T\<^sub>m \<and> time2 = 0 \<and> time1 = time_up_down2 \<and> \<not> rod2 \<and> \<not> rod1 \<and> t = 0)} 
  reactor 
  {T = T\<^sub>M \<longrightarrow> time1 + t > t\<^sub>R \<or> time2 + t > t\<^sub>R}"
  apply (rule hoare_conseq[OF safe_inv])
   prefer 2
  subgoal
    using Ks_ge0 Tm_le
    unfolding inv_def
    apply (expr_simp; clarsimp simp: zero_compare_simps(1-8))
    by (smt (verit, ccfv_SIG) diff_divide_distrib nonzero_mult_div_cancel_left rest_constraints(1,2))
  subgoal
    using Ks_ge0 Tm_le
    unfolding inv_def
    by (expr_simp; clarsimp simp: zero_compare_simps(1-8))
  done

end

thm original_reactor_def
    original_reactor_def[of 1000 250 80 34 25 10, simplified]
    original_reactor_def[of 1100 250 80 34 25 10, simplified]




dataspace time_triggered_reactor =
  constants 
    T\<^sub>M :: real \<comment> \<open> Max temperature reaction threshold\<close>
    T\<^sub>m :: real \<comment> \<open> Min temperature reaction threshold\<close>
    t\<^sub>R :: real \<comment> \<open> rod resting time \<close>
    K\<^sub>u\<^sub>p :: real \<comment> \<open> reactor's temperature-increase rate \<close>
    K\<^sub>1 :: real \<comment> \<open> reactor's temperature-decrease rate by rod 1 \<close>
    K\<^sub>2 :: real \<comment> \<open> reactor's temperature-decrease rate by rod 2 \<close>
    \<theta> :: real \<comment> \<open> time-range that triggers a control intervention \<close>
  assumes Tm_ge0: "0 < T\<^sub>m" 
    and Tm_le: "T\<^sub>m < T\<^sub>M" 
    and tR_ge0: "0 < t\<^sub>R" 
    and Ks_ge0: 
      "0 < K\<^sub>u\<^sub>p"
      "0 < K\<^sub>1"
      "0 < K\<^sub>2"
    and rest_constraints: 
      "t\<^sub>R < 2 * (T\<^sub>M - T\<^sub>m) / K\<^sub>u\<^sub>p + (T\<^sub>M - T\<^sub>m) / K\<^sub>1"
      "t\<^sub>R < 2 * (T\<^sub>M - T\<^sub>m) / K\<^sub>u\<^sub>p + (T\<^sub>M - T\<^sub>m) / K\<^sub>2"
      "(T\<^sub>M - T\<^sub>m) / K\<^sub>u\<^sub>p < t\<^sub>R"
    and theta_hyp: "\<exists>n > 3. n * \<theta> > T\<^sub>M - T\<^sub>m"
  variables
    rod1 :: bool
    rod2 :: bool
    temp :: real
    time1 :: real
    time2 :: real
    T :: real
    t :: real

context time_triggered_reactor
begin

text \<open>
To modify the original model and make it time-triggered, 
let's assume that the temperature sensor is triggered
every @{term "\<theta>"} seconds. We model this with the modified
system of ODEs below.
\<close>

definition "reactor_ode \<equiv>
  IF rod1 THEN {T` = - K\<^sub>1, t` = 1 | t \<le> \<theta> }
  ELSE IF rod2 THEN {T` = - K\<^sub>2, t` = 1 | t \<le> \<theta>}
  ELSE {T` = K\<^sub>u\<^sub>p, t` = 1 | t \<le> \<theta>}"

lemma [local_flow]: "local_flow_on [T \<leadsto> K, t \<leadsto> 1] (T +\<^sub>L t) UNIV UNIV
  (\<lambda>\<tau>. [T \<leadsto> K * \<tau>  + T, t \<leadsto> \<tau> + t])"
  by local_flow_on_auto

text \<open>
This means that after every @{term \<theta>} units of time,
@{term "$rod1 \<and> \<not> $rod2 \<Longrightarrow> $T = - K\<^sub>1 * \<theta> + $temp"},
@{term "\<not> $rod1 \<and> $rod2 \<Longrightarrow> $T = - K\<^sub>2 * \<theta> + $temp"}, and
@{term "\<not> $rod1 \<and> \<not> $rod2 \<Longrightarrow> $T = K\<^sub>u\<^sub>p * \<theta> + $temp"}.

In particular, this means that the control must react when 
@{term "$temp + K\<^sub>u\<^sub>p * \<theta> \<ge> T\<^sub>M"},
@{term "$temp - K\<^sub>1 * \<theta> \<le> T\<^sub>m"}, and
@{term "$temp - K\<^sub>2 * \<theta> \<le> T\<^sub>m"}.
\<close>

definition "reactor_ctrl \<equiv>
  temp ::= T; 
  time1 ::= time1 + t; 
  time2 ::= time2 + t;
  t ::= 0;
  IF temp - K\<^sub>1 * \<theta> \<le> T\<^sub>m \<and> rod1 THEN rod1 ::= False; time1 ::= 0
  ELSE IF temp - K\<^sub>2 * \<theta> \<le> T\<^sub>m \<and> rod2 THEN rod2 ::= False; time2 ::= 0
  ELSE IF temp + K\<^sub>u\<^sub>p * \<theta> \<ge> T\<^sub>M \<and> \<not> rod1 \<and> \<not> rod2 THEN 
    IF time1 > t\<^sub>R THEN rod1 ::= True
    ELSE IF time2 > t\<^sub>R THEN rod2 ::= True
    ELSE skip
  ELSE skip
"

definition "reactor = (reactor_ctrl; reactor_ode)\<^sup>*"

abbreviation "time_up \<equiv> (T\<^sub>M - T\<^sub>m) / K\<^sub>u\<^sub>p"

abbreviation "time_up_down1 \<equiv> time_up + (T\<^sub>M - T\<^sub>m) / K\<^sub>1"

abbreviation "time_up_down2 \<equiv> time_up + (T\<^sub>M - T\<^sub>m) / K\<^sub>2"

abbreviation "cycle1 \<equiv> time_up + time_up_down1"

abbreviation "cycle2 \<equiv> time_up + time_up_down2"

expression inv is "
  (rod1 \<longrightarrow> \<not> rod2) \<and> (rod2 \<longrightarrow> \<not> rod1) \<and> (T\<^sub>m \<le> T \<and> T \<le> T\<^sub>M)
  \<and> (rod1 \<and> \<not> rod2 \<longrightarrow> (
      T = T\<^sub>M - K\<^sub>1 * (time2 + t - time_up)
      \<and> T = T\<^sub>M - K\<^sub>1 * (time1 + t - cycle2)))
  \<and> (\<not> rod1 \<and> rod2 \<longrightarrow> (
      T = T\<^sub>M - K\<^sub>2 * (time2 + t - cycle1)
      \<and> T = T\<^sub>M - K\<^sub>2 * (time1 + t - time_up)))
  \<and> (\<not> rod1 \<and> \<not> rod2 \<longrightarrow> 
      (T = T\<^sub>m + K\<^sub>u\<^sub>p * (time1 + t)
      \<and> T = T\<^sub>m + K\<^sub>u\<^sub>p * (time2 + t - time_up_down1))
    \<or> (T = T\<^sub>m + K\<^sub>u\<^sub>p * (time2 + t)
      \<and> T = T\<^sub>m + K\<^sub>u\<^sub>p * (time1 + t - time_up_down2)))"

lemma safe_inv: "H{inv} reactor {inv}"
  unfolding reactor_def reactor_ctrl_def reactor_ode_def
  unfolding loopi_def[symmetric, where I="inv", unfolded inv_def]
  apply intro_loops
    apply (symbolic_exec; symbolic_exec?; symbolic_exec?; symbolic_exec?; symbolic_exec?; symbolic_exec?)
  subgoal 
    (* case 1:
        \<bullet> IF temp = T\<^sub>m \<and> rod1 THEN rod1 ::= False; time1 ::= 0
        \<bullet> rod1  *)
    by wlp_full
  subgoal for time1\<^sub>0 time2\<^sub>0 \<tau> rod1\<^sub>0 old_time1
    (* case 2:
        \<bullet> IF temp = T\<^sub>m \<and> rod1 THEN rod1 ::= False; time1 ::= 0
        \<bullet> \<not> rod1 \<and> rod2 *)
    using Ks_ge0 Tm_le
    by wlp_full
  subgoal for time1\<^sub>0 time2\<^sub>0 \<tau> rod1\<^sub>0 old_time1
    (* case 3:
        \<bullet> IF temp = T\<^sub>m \<and> rod1 THEN rod1 ::= False; time1 ::= 0
        \<bullet> \<not> rod1 \<and> \<not> rod2 *)
    apply (wlp_full local_flow: local_flow)
    apply (rename_tac s tmax)
    using Ks_ge0 Tm_le Tm_ge0
    apply (intro conjI iffI)
     apply (erule_tac x=tmax in allE, clarsimp)
    apply (meson add_increasing less_eq_real_def mult_sign_intros(1))
     apply (erule_tac x=tmax in allE, clarsimp)

    sorry
  oops

end










end