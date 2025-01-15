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
  shows "\<^bold>{Tmin \<le> T \<and> T \<le> Tmax\<^bold>} 
    (LOOP (ctrl2; dyn2) INV (Tmin \<le> T \<and> T \<le> Tmax))
   \<^bold>{Tmin \<le> T \<and> T \<le> Tmax\<^bold>}"
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

(*
T(\<tau>) = - exp (-K * \<tau>) * (c - T\<^sub>0) + c
\<and> t(\<tau>) = \<tau> + t\<^sub>0
\<and> active \<longrightarrow> c = h \<and> \<not> active \<longrightarrow> c = 0

where T\<^sub>0 is the initial value of the temperature that due to our precondition we 
assume to satisfy Tmin \<le> T\<^sub>0 \<le> Tmax < h.
Let N \<ge> 3, be the number of segments that we are splitting the interval [Tmin, Tmax]:

If c=h (i.e. active):
T\<^sub>0 + (Tmax - Tmin)/N = - exp (-K * \<tau>) * (c - T\<^sub>0) + c
\<Longrightarrow> (Tmax - Tmin)/N + T\<^sub>0 - h = - exp (-K * \<tau>) * (h - T\<^sub>0)
\<Longrightarrow> (Tmax - Tmin)/N + N * (T\<^sub>0 - h)/N = exp (-K * \<tau>) * (T\<^sub>0 - h)
\<Longrightarrow> (Tmax - Tmin)/(N * (T\<^sub>0 - h)) + 1 = exp (-K * \<tau>)
\<Longrightarrow> ln ((Tmax - Tmin)/(N * (T\<^sub>0 - h)) + 1) = -K * \<tau>

We want 1 \<ge> (Tmax - Tmin)/(N * (T\<^sub>0 - h)) + 1 > 0
\<Longleftrightarrow> 0 \<ge> (Tmax - Tmin)/(N * (T\<^sub>0 - h)) > -1
because in that way, the logarithm exists
(due to the right inequality) and the 
magnitudes have physical sense (ln returns a negative due 
to the left inequality).

Observe that because of Tmax > Tmin \<and> N \<ge> 3 \<and> T\<^sub>0 < h:
0 > (Tmax - Tmin)/(N * (T\<^sub>0 - h))

However, we must require Tmax - Tmin < N * (h - T\<^sub>0)
to guarantee that (Tmax - Tmin)/(N * (h - T\<^sub>0)) < 1
(and thus that (Tmax - Tmin)/(N * (T\<^sub>0 - h)) > -1).
It suffices to require that Tmax - Tmin < h - Tmax
(we could relax this condition).

If this holds, then we could define the guard for active as
\<tau> \<le> -K\<^sup>-\<^sup>1 * ln ((Tmax - Tmin)/(N * (T\<^sub>0 - h)) + 1) 

Similarly, if c=0 (i.e. if inactive):
T\<^sub>0 - (Tmax - Tmin)/N = - exp (-K * \<tau>) * (c - T\<^sub>0) + c
\<Longrightarrow> T\<^sub>0 - (Tmax - Tmin)/N = T\<^sub>0 * exp (-K * \<tau>)
\<Longrightarrow> 1 - (Tmax - Tmin)/(N * T\<^sub>0) = exp (-K * \<tau>)

Then we want 1 > 1 - (Tmax - Tmin)/(N * T\<^sub>0) > 0
\<Longleftrightarrow> 0 < (Tmax - Tmin)/(N * T\<^sub>0) < 1

Thus, we need Tmax - Tmin < N * T\<^sub>0
It suffices to require that Tmax - Tmin < Tmin

If this holds, then we could define the guard for inactive as
\<tau> \<le> -K\<^sup>-\<^sup>1 * ln (1 - (Tmax - Tmin)/(N * T\<^sub>0))

Now the condition for the control.
At most, if the guards are defined as above, the temperature
will increase (or decrease) (Tmax - Tmin)/N.
Thus, we can define:
pre_ctrl \<equiv> 
  IF \<not> active \<and> temp - 1.1 * (Tmax - Tmin)/N \<le> Tmin THEN active ::= True
  ELSE IF active \<and> temp + 1.1 * (Tmax - Tmin)/N \<ge> Tmax THEN active ::= False ELSE skip

*)


end

end