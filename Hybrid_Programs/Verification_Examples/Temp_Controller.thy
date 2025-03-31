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


dataspace thermostat = 
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
context thermostat
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

subsection \<open> Improved thermostat \<close>

text \<open>
This thermostat hybrid model improves on the literature versions by adding 
a guard and modifying the control so that it reacts before surpassing the
comfortable temperatures @{term Tmin} and @{term Tmax}. The consequence
is that we can prove that the room's temperature @{term T} always remains 
within the comfortable range @{term "{Tmin--Tmax}"}.
\<close>

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

lemma weird_intro_rule: "(inv1 \<le> |F] pos_inv1)
  \<Longrightarrow> (pos_inv1 \<le> |G] inv1)
  \<Longrightarrow> (inv1 \<le> |F] fbox G inv1)"
  apply (expr_simp add: fbox_def)
  unfolding le_fun_def le_bool_def
  by blast

lemma thermostat1:
  "H{Tmin \<le> T \<and> T \<le> Tmax} 
    (LOOP (ctrl1; dyn1) INV (Tmin \<le> T \<and> T \<le> Tmax))
   {Tmin \<le> T \<and> T \<le> Tmax}"
  apply (intro_loops)
    apply (subst fbox_kcomp)
    apply(intro conjI weird_intro_rule)
     apply (wlp_full)
    apply (rule hoare_if_then_else)
  apply (wlp_full local_flow: local_flow1[where c=0, simplified])
      apply (wlp_full local_flow: local_flow1)
  using temp_dyn_down_real_arith[OF K_ge0 Tmin_ge0] apply auto[1]
  using temp_dyn_down_real_arith[OF K_ge0 Tmin_ge0] apply auto[1]
  apply (wlp_full local_flow: local_flow1[where c=h, simplified])
  using temp_dyn_up_real_arith[OF K_ge0 _ _ Tmax_le_Tlim] apply auto[1]
  using temp_dyn_up_real_arith[OF K_ge0 _ _ Tmax_le_Tlim] 
  by expr_auto+


subsection \<open> Original thermostat \<close>

text \<open>
This original thermostat model is reactionary. It changes when it detects that
the temperature of the room is uncomfortable. Thus, the guards directly correspond 
to the invariant to guarantee the preservation of @{term "Tmin \<le> $T \<and> $T \<le> Tmax"}.
\<close>


abbreviation "dyn2 \<equiv> IF \<not> active 
  THEN {T` = - K * T | Tmin \<le> T} 
  ELSE {T` = - K * (T - h) | T \<le> Tmax}"

abbreviation "pre_ctrl2 \<equiv> 
  IF \<not> active \<and> temp \<le> Tmin THEN active ::= True
  ELSE IF active \<and> temp \<ge> Tmax THEN active ::= False ELSE skip"

abbreviation "ctrl2 \<equiv> temp ::= T; pre_ctrl2"

abbreviation "pos_inv2 \<equiv> ((Tmin \<le> $T \<and> $T \<le> Tmax) \<and> temp = T)\<^sub>e"

lemma weird_intro_rule2: "(inv1 \<le> |F] pos_inv2)
  \<Longrightarrow> (pos_inv2 \<le> |G] inv1)
  \<Longrightarrow> (inv1 \<le> |F] fbox G inv1)"
  apply (expr_simp add: fbox_def)
  unfolding le_fun_def le_bool_def
  using Tmin_le_Tmax
  by meson

lemma local_flow2: "local_flow_on [T \<leadsto> - K * (T - c)] T UNIV UNIV
  (\<lambda>\<tau>. [T \<leadsto> - exp (-K * \<tau>) * (c - T) + c])"
  by local_flow_on_auto

lemma thermostat2:
  assumes le0: "Tmin \<le> Tmax"
  shows "H{Tmin \<le> T \<and> T \<le> Tmax} 
    (LOOP (ctrl2; dyn2) INV (Tmin \<le> T \<and> T \<le> Tmax))
   {Tmin \<le> T \<and> T \<le> Tmax}"
  apply (intro_loops)
    apply (subst fbox_kcomp)
  apply (rule weird_intro_rule2)
     apply (wlp_full)
    apply (rule hoare_if_then_else)
     apply (wlp_full local_flow: local_flow2[where c=0, simplified])
     apply (smt (verit, best) K_ge0 Tmin_ge0 assms div_by_1 exp_ge_zero exp_le_one_iff 
      max_zero_mult_nonneg_le minus_mult_minus mult.commute mult_eq_0_iff mult_le_0_iff 
      mult_nonneg_nonneg mult_right_mono_neg nonzero_mult_div_cancel_left one_le_exp_iff 
      times_divide_eq_left)
    apply (wlp_full local_flow: local_flow2[where c=h, simplified])
  using K_ge0 Tmin_ge0 assms
    apply (smt (verit, best) Groups.mult_ac(2) Tmax_le_Tlim div_by_1 divide_self_if exp_zero 
      landau_omega.R_mult_left_mono mult_eq_0_iff mult_sign_intros(1) nonzero_mult_div_cancel_left 
      nonzero_mult_div_cancel_right one_le_exp_iff times_divide_eq_right) 
  by expr_auto+

lemma "Tmin \<le> Tmax \<Longrightarrow> Tmin \<le> T' \<or> T' \<le> Tmax" for T'::real
  by linarith


end

lemma decr_in_ivl:
  assumes "(K::real) > 0" and "0 < \<epsilon>" and "\<epsilon> < Tmin" and "h > Tmax + \<epsilon>" and "t \<ge> 0"
    and T_ivl1: "\<not> T \<le> Tmin + 11 * \<epsilon> / 10"
    and key: "t \<le> - (ln (1 - \<epsilon> / T) / K)" (is "t \<le> - (ln ?expr / K)")
  shows "Tmin \<le> exp (- (K * t)) * T"
proof-
  have "?expr > 0"
    using assms by auto
  hence "exp (- (K * t)) \<ge> 1 - \<epsilon> / T"
    using key
    by (metis add.inverse_inverse \<open>K > 0\<close> pos_le_minus_divide_eq
        exp_le_cancel_iff exp_ln mult.commute neg_le_iff_le) 
  hence "T - T *  exp (- (K * t)) \<le> \<epsilon>"
    by (smt (verit, ccfv_SIG) T_ivl1 \<open>0 < \<epsilon>\<close> \<open>\<epsilon> < Tmin\<close> 
        divide_less_eq_1_pos factor_fracR(2) mult_left_le 
        mult_pos_pos times_divide_eq_right zero_le_divide_iff)
  moreover have "T - Tmin \<ge> 1.1 * \<epsilon>"
    using T_ivl1 
    by auto
  ultimately show "Tmin \<le> exp (- (K * t)) * T"
    using \<open>0 < \<epsilon>\<close> by argo
qed

lemma incr_in_ivl:
  assumes "(K::real) > 0" and "0 < \<epsilon>" and "\<epsilon> < Tmin" and "h > Tmax + \<epsilon>" and "t \<ge> 0"
    and "Tmin \<le> T"
    and T_ivl2: "\<not> Tmax - 11 * \<epsilon> / 10 \<le> T"
    and key: "t \<le> - (ln (\<epsilon> / (T - h) + 1) / K)" (is "t \<le> - (ln ?expr / K)")
  shows "h - exp (- (K * t)) * (h - T) \<le> Tmax"
proof-
  have "exp (- (K * t)) * T \<le> T"
    using assms
    by force
  hence "?expr > 0"
    using \<open>\<epsilon> > 0\<close>
    by (smt (verit) \<open>h > Tmax + \<epsilon>\<close> T_ivl2 divide_less_eq_1_neg 
        divide_minus_left divide_nonneg_nonneg) 
  hence "?expr \<le> exp (- K * t)"
    using key
    by (smt (verit, best) \<open>K > 0\<close> divide_minus_left divide_pos_pos exp_ln 
        factor_fracR(4) ln_ge_iff mult_eq_0_iff mult_minus_left mult_nonneg_nonneg)
  hence "h - exp (- (K * t)) * (h - T) \<le> h + ?expr * (T - h)"
    using assms
    by (smt (verit, ccfv_threshold) divide_pos_pos mult_minus_left 
        mult_minus_right nonzero_mult_div_cancel_right pos_le_divide_eq)
  also have "... = h + (\<epsilon> / (T - h) + (T - h)/(T - h)) * (T - h)"
    by simp
  also have "... = \<epsilon> + T"
    by (smt (verit, ccfv_SIG) assms diff_divide_eq_iff divide_cancel_right divide_pos_pos)
  finally have "h - exp (- (K * t)) * (h - T) \<le> \<epsilon> + T" .
  moreover have "\<epsilon> + T < 1.1 * \<epsilon> + T"
    using assms
    by auto
  ultimately show ?thesis
    using T_ivl2
    by auto
qed


dataspace time_triggered_thermostat = 
  constants 
    Tmax :: real (* maximum comfortable temp. *)
    Tmin :: real (* minimum comfortable temp. *)
    h :: real (* highest temp. when thermostat is on *)
    K :: real (* heating rate *)    
    \<epsilon> :: real (* max increment/decrement of temp per sensing interval *)
  assumes 
    K_ge0: "K > 0"
    and eps_ge0: "\<epsilon> > 0"
    and eps_le_Tmin: "\<epsilon> < Tmin"
    and delta_ge_3eps: "Tmax - Tmin > 3 * \<epsilon>" 
    and h_ge_Tmax_eps: "h > Tmax + \<epsilon>"
  variables 
    (* physical *)
    T :: real      (* temperature *)
    t :: real      (* time *)
    (* program *)
    temp :: real   (* for temperature measurements *)
    active :: bool (* whether thermostat is on or off *)
context time_triggered_thermostat
begin

lemma 
  shows Tmin_le_Tmax: "Tmin < Tmax"
    and Tmax_le_h: "Tmax < h"
  using delta_ge_3eps eps_ge0 h_ge_Tmax_eps
  by linarith+

lemma local_flow: "local_flow_on [T \<leadsto> - K * (T - c), t \<leadsto> 1] (T +\<^sub>L t) UNIV UNIV
  (\<lambda>\<tau>. [T \<leadsto> - exp (-K * \<tau>) * (c - T) + c, t \<leadsto> \<tau> + t])"
  by local_flow_on_auto

(* Temperature advances at most \<epsilon> units upwards or downwards 
before our sensor makes a measurement. *)
abbreviation "dyn \<equiv> IF \<not> active 
  THEN {T` = - K * T, t` = 1 | t \<le> - ln (1 - \<epsilon> / temp) / K} 
  ELSE {T` = - K * (T - h), t` = 1 | t \<le> - ln (\<epsilon> / (temp - h) + 1) / K}"

(* Drawing:
|--------h
|
|--------Tmax
|--------close_to_Tmax
|
|
|--------close_to_Tmin
|--------Tmin
*)
abbreviation "close_to_Tmin \<T> \<equiv> \<T> \<le> Tmin + 1.1 * \<epsilon>"
abbreviation "close_to_Tmax \<T> \<equiv> \<T> \<ge> Tmax - 1.1 * \<epsilon>"

abbreviation "pre_ctrl \<equiv> 
  IF \<not> active \<and> close_to_Tmin temp THEN active ::= True
  ELSE IF active \<and> close_to_Tmax temp THEN active ::= False ELSE skip"

abbreviation "ctrl \<equiv> t ::= 0; temp ::= T; pre_ctrl"

abbreviation "inv1 \<equiv> (Tmin \<le> $T \<and> $T \<le> Tmax)\<^sub>e"

abbreviation "pos_inv1 \<equiv> (Tmin \<le> $T \<and> $T \<le> Tmax \<and> temp = T \<and> t = 0 
  \<and> (close_to_Tmin temp \<longrightarrow> active) \<and> (close_to_Tmax temp \<longrightarrow> \<not> active))\<^sub>e"

lemma weird_intro_rule: "(inv1 \<le> |F] pos_inv1)
  \<Longrightarrow> (pos_inv1 \<le> |G] inv1)
  \<Longrightarrow> (inv1 \<le> |F] fbox G inv1)"
  apply (expr_simp add: fbox_def)
  unfolding le_fun_def le_bool_def
  by blast

lemma thermostat2:
  "H{Tmin \<le> T \<and> T \<le> Tmax} 
    (LOOP (ctrl; dyn) INV (Tmin \<le> T \<and> T \<le> Tmax))
   {Tmin \<le> T \<and> T \<le> Tmax}"
  (* apply (wlp_flow local_flow: local_flow) *)
  apply (intro_loops)
    apply (subst fbox_kcomp)
    apply (rule weird_intro_rule)
  using delta_ge_3eps 
     apply (wlp_full)
    apply (rule hoare_if_then_else)
     apply (wlp_full local_flow: local_flow[where c=0, simplified])
  subgoal 
    using decr_in_ivl[OF K_ge0 eps_ge0 eps_le_Tmin h_ge_Tmax_eps] 
    by blast
  subgoal 
    by (smt (verit, best) K_ge0 eps_ge0 eps_le_Tmin exp_le_one_iff 
        mult_left_le_one_le zero_le_mult_iff)
  subgoal 
    using decr_in_ivl[OF K_ge0 eps_ge0 eps_le_Tmin h_ge_Tmax_eps] 
    by blast
  subgoal 
    by (smt (verit, best) K_ge0 eps_ge0 eps_le_Tmin exp_le_one_iff 
        mult_left_le_one_le zero_le_mult_iff)
    apply (wlp_full local_flow: local_flow[where c=h, simplified])
  subgoal
    by (smt (verit, best) K_ge0 eps_ge0 exp_ge_zero exp_le_one_iff 
        h_ge_Tmax_eps mult_left_le_one_le mult_sign_intros(1))
  subgoal
    using incr_in_ivl[OF K_ge0 eps_ge0 eps_le_Tmin h_ge_Tmax_eps]
    by blast
  subgoal
    by (smt (verit, best) K_ge0 eps_ge0 exp_ge_zero exp_le_one_iff 
        h_ge_Tmax_eps mult_left_le_one_le mult_sign_intros(1))
  subgoal
    using incr_in_ivl[OF K_ge0 eps_ge0 eps_le_Tmin h_ge_Tmax_eps]
    by blast
  by expr_auto+

end

thm time_triggered_thermostat_def
 time_triggered_thermostat_def[of 25 20 30 "0.2" "1.6", simplified]


(*
T(\<tau>) = - exp (-K * \<tau>) * (c - T\<^sub>0) + c
\<and> t(\<tau>) = \<tau> + t\<^sub>0
\<and> active \<longrightarrow> c = h \<and> \<not> active \<longrightarrow> c = 0

where T\<^sub>0 is the initial value of the temperature that due to our precondition we 
assume to satisfy Tmin \<le> T\<^sub>0 \<le> Tmax < h.
Let \<epsilon> > 0 be a temperature increment:

If c=h (i.e. active):
T\<^sub>0 + \<epsilon> = - exp (-K * \<tau>) * (h - T\<^sub>0) + h
\<Longrightarrow> \<epsilon> + T\<^sub>0 - h = - exp (-K * \<tau>) * (h - T\<^sub>0)
\<Longrightarrow> \<epsilon> + T\<^sub>0 - h = exp (-K * \<tau>) * (T\<^sub>0 - h)
\<Longrightarrow> \<epsilon> / (T\<^sub>0 - h) + 1 = exp (-K * \<tau>)
\<Longrightarrow> ln (\<epsilon>/(T\<^sub>0 - h) + 1) = -K * \<tau>

We want 1 \<ge> \<epsilon> / (T\<^sub>0 - h) + 1 > 0
\<Longleftrightarrow> 0 \<ge> \<epsilon> / (T\<^sub>0 - h) > -1
because in that way, the logarithm exists
(due to the right inequality) and the 
magnitudes have physical sense (ln returns a negative due 
to the left inequality).

Observe that since \<epsilon> > 0 \<and> T\<^sub>0 < h, the lhs
(0 > \<epsilon> / (T\<^sub>0 - h)) holds. However, we must 
require \<epsilon> < h - T\<^sub>0 to guarantee the rhs 
(\<epsilon> / (T\<^sub>0 - h) > -1).

If this holds, then we could define the guard for active as
\<tau> \<le> -K\<^sup>-\<^sup>1 * ln (\<epsilon>/(T\<^sub>0 - h) + 1) 

Similarly, if c=0 (i.e. if inactive):
T\<^sub>0 - \<epsilon> = - exp (-K * \<tau>) * (c - T\<^sub>0) + c
(c = 0) \<Longrightarrow> T\<^sub>0 - \<epsilon> = T\<^sub>0 * exp (-K * \<tau>)
\<Longrightarrow> 1 - \<epsilon> / T\<^sub>0 = exp (-K * \<tau>)
\<Longrightarrow> ln (1 - \<epsilon> / T\<^sub>0) = - K * \<tau>

Then we want 1 > 1 - \<epsilon> / T\<^sub>0 > 0
\<Longleftrightarrow> 0 < \<epsilon> / T\<^sub>0 < 1
Thus, we need \<epsilon> < T\<^sub>0.

If this holds, then we could define the guard for inactive as
\<tau> \<le> -K\<^sup>-\<^sup>1 * ln (1 - \<epsilon> / T\<^sub>0)

Now the condition for the control. At most, if the guards 
are defined as above, the temperature will increase (or 
decrease) \<epsilon> units. Thus, we can define:
pre_ctrl \<equiv> 
  IF \<not> active \<and> temp \<le> Tmin - 1.1 * \<epsilon> THEN active ::= True
  ELSE IF active \<and> temp \<ge> Tmax - 1.1 * \<epsilon> THEN active ::= False ELSE skip

*)

end