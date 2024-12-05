section \<open> Pendulum with force \<close>

theory Temp_Controller
  imports "Hybrid-Verification.Hybrid_Verification"
begin



pretty_exprs

lemma fbox_comp_inv_iff: "((I)\<^sub>e \<le> |F] |G] I) \<longleftrightarrow> (((I)\<^sub>e \<le> |F] I) \<and> ((I)\<^sub>e \<le> |G] I))"
  by (auto simp: fbox_def)

lemma fbox_kcomp_put[wlp]: "fbox (\<langle>\<lambda>s. put\<^bsub>x\<^esub> s v\<rangle> ; F) = fbox (F\<lbrakk>v/x\<rbrakk>)"
  unfolding fbox_def kcomp_eq
  by (auto simp: expr_defs assigns_def)

lemma temp_dyn_down_real_arith:
  assumes "a > 0" and Thyps: "0 < Tmin" "Tmin \<le> T" "T \<le> Tmax"
    and thyps: "0 \<le> (t::real)" "\<forall>\<tau>\<in>{0..t}. \<tau> \<le> - (ln (Tmin / T) / a) "
  shows "Tmin \<le> exp (-a * t) * T" and "exp (-a * t) * T \<le> Tmax"
proof-
  have "0 \<le> t \<and> t \<le> - (ln (Tmin / T) / a)"
    using thyps by auto
  hence "ln (Tmin / T) \<le> - a * t \<and> - a * t \<le> 0"
    using assms(1) divide_le_cancel by fastforce
  also have "Tmin / T > 0"
    using Thyps by auto
  ultimately have obs: "Tmin / T \<le> exp (-a * t)" "exp (-a * t) \<le> 1"
    using exp_ln exp_le_one_iff by (metis exp_less_cancel_iff not_less, simp)
  thus "Tmin \<le> exp (-a * t) * T"
    using Thyps by (simp add: pos_divide_le_eq)
  show "exp (-a * t) * T \<le> Tmax"
    using Thyps mult_left_le_one_le[OF _ exp_ge_zero obs(2), of T]
      less_eq_real_def order_trans_rules(23) by blast
qed

lemma temp_dyn_up_real_arith:
  assumes "a > 0" and Thyps: "Tmin \<le> T" "T \<le> Tmax" "Tmax < (L::real)"
    and thyps: "0 \<le> t" "\<forall>\<tau>\<in>{0..t}. \<tau> \<le> - (ln ((L - Tmax) / (L - T)) / a) "
  shows "L - Tmax \<le> exp (-(a * t)) * (L - T)"
    and "L - exp (-(a * t)) * (L - T) \<le> Tmax"
    and "Tmin \<le> L - exp (-(a * t)) * (L - T)"
proof-
  have "0 \<le> t \<and> t \<le> - (ln ((L - Tmax) / (L - T)) / a)"
    using thyps by auto
  hence "ln ((L - Tmax) / (L - T)) \<le> - a * t \<and> - a * t \<le> 0"
    using assms(1) divide_le_cancel by fastforce
  also have "(L - Tmax) / (L - T) > 0"
    using Thyps by auto
  ultimately have "(L - Tmax) / (L - T) \<le> exp (-a * t) \<and> exp (-a * t) \<le> 1"
    using exp_ln exp_le_one_iff by (metis exp_less_cancel_iff not_less)
  moreover have "L - T > 0"
    using Thyps by auto
  ultimately have obs: "(L - Tmax) \<le> exp (-a * t) * (L - T) \<and> exp (-a * t) * (L - T) \<le> (L - T)"
    by (simp add: pos_divide_le_eq)
  thus "(L - Tmax) \<le> exp (-(a * t)) * (L - T)"
    by auto
  thus "L - exp (-(a * t)) * (L - T) \<le> Tmax"
    by auto
  show "Tmin \<le> L - exp (-(a * t)) * (L - T)"
    using Thyps and obs by auto
qed


dataspace sys = 
  constants 
    Tmax :: real (* maximum comfortable temp. *)
    Tmin :: real (* minimum comfortable temp. *)
    h :: real (* highest temp. when thermostat is on *)
    K :: real (* heating rate *)    
  assumes 
    Tmin_ge0: "0 < Tmin" 
    and Tmin_le_Tmax: "Tmin + 1 < Tmax" 
    and Tmax_le_Tlim: "Tmax < h"
    and K_ge0: "K > 0"
  variables 
    (* physical *)
    T :: real      (* temperature *)
    t :: real      (* time *)
    (* program *)
    temp :: real   (* for temperature measurements *)
    active :: bool (* whether thermostat is on or off *)
context sys
begin

(*
K - heating rate

Inactive
(1) x(t) = \<theta> * e^{-K*t}
\<Longrightarrow> x'(t) = -K * \<theta> * e^{-K*t}
\<Longrightarrow> x'(t) = -K * x(t)

Active
(2) x(t) = \<theta> * e^{-K*t} + h * (1 - e^{-K*t})
  = (\<theta> - h) * e^{-K*t} + h
\<Longrightarrow> x'(t) = -K * \<theta> * e^{-K*t} + K * h *e^{-K*t}
\<Longrightarrow> x'(t) = - K * (\<theta> - h) * e^{-K*t} 
   = - K * x(t) - K * h = - K * (x(t) - h)

(1) \<and> (2) \<Longrightarrow> x'(t) = - K * (x(t) - c)
  where c = if active then h else 0
*)

lemma local_flow1: "local_flow_on [T \<leadsto> - K * (T - c), t \<leadsto> 1] (T +\<^sub>L t) UNIV UNIV
  (\<lambda>\<tau>. [T \<leadsto> - exp (-K * \<tau>) * (c - T) + c, t \<leadsto> \<tau> + t])"
  by local_flow_on_auto


abbreviation "dyn1 \<equiv> IF \<not> active 
  THEN {T` = - K * T, t` = 1 | t \<le> - (ln (Tmin/temp))/K} 
  ELSE {T` = - K * (T - h), t` = 1 | t \<le> - (ln ((h - Tmax)/(h - temp)))/K}"

abbreviation "pre_ctrl1 \<equiv> 
  IF \<not> active \<and> temp \<le> Tmin + 1 THEN active ::= True
  ELSE IF active \<and> temp \<ge> Tmax - 1 THEN active ::= False ELSE skip"

abbreviation "ctrl1 \<equiv> t ::= 0; temp ::= T; pre_ctrl1"

abbreviation "inv1 \<equiv> (Tmin \<le> $T \<and> $T \<le> Tmax)\<^sub>e"

abbreviation "pos_inv1 \<equiv> (Tmin \<le> $T \<and> $T \<le> Tmax \<and> temp = T \<and> t = 0)\<^sub>e"

lemma weird_intro_rule: "(
(inv1 \<le> |F] pos_inv1)
\<Longrightarrow> (pos_inv1 \<le> |G] inv1)
\<Longrightarrow> (inv1 \<le> |F] fbox G inv1)
)"
  apply (expr_simp add: fbox_def)
  unfolding le_fun_def le_bool_def
  by blast
  

lemma
  "\<^bold>{Tmin \<le> T \<and> T \<le> Tmax\<^bold>} 
    (LOOP (ctrl1; dyn1) INV (Tmin \<le> T \<and> T \<le> Tmax))
   \<^bold>{Tmin \<le> T \<and> T \<le> Tmax\<^bold>}"
  apply (intro_loops)
    apply (subst fbox_kcomp)
    apply(intro conjI weird_intro_rule)
     apply (wlp_full)
    apply (rule hoare_if_then_else)
  using Tmin_ge0
  apply (wlp_full local_flow: local_flow1[where c=0, simplified])
      apply (wlp_full local_flow: local_flow1)
  using temp_dyn_down_real_arith[OF K_ge0 Tmin_ge0] apply auto[1]
  using temp_dyn_down_real_arith[OF K_ge0 Tmin_ge0] apply auto[1]
  apply (wlp_full local_flow: local_flow1[where c=h, simplified])
  using temp_dyn_up_real_arith[OF K_ge0 _ _ Tmax_le_Tlim] apply auto[1]
  using temp_dyn_up_real_arith[OF K_ge0 _ _ Tmax_le_Tlim] 
  by expr_auto+


end


end