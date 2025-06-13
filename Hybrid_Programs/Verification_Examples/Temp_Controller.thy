section \<open> Pendulum with force \<close>

theory Temp_Controller
  imports "Hybrid-Verification.Hybrid_Verification"
begin


subsection \<open> Event-triggered thermostat \<close>

dataspace event_triggered_thermostat = 
  constants 
    Tmax :: real (* maximum comfortable temp. *)
    Tmin :: real (* minimum comfortable temp. *)
    L :: real (* highest temp. when thermostat is on *)
    K :: real (* freezing factor *)    
  assumes 
    Tmin_ge0: "0 < Tmin" 
    and Tmax_le_Tlim: "Tmax < L"
    and K_ge0: "K > 0"
  variables 
    (* physical *)
    T :: real      (* temperature *)
    (* program *)
    active :: bool (* whether thermostat is on or off *)

context event_triggered_thermostat
begin 

abbreviation "dyn \<equiv> IF \<not> active 
  THEN {T` = - K * T | Tmin \<le> T} 
  ELSE {T` = - K * (T - L) | T \<le> Tmax}"

abbreviation "ctrl \<equiv> 
  IF \<not> active \<and> T \<le> Tmin THEN active ::= True
  ELSE IF active \<and> T \<ge> Tmax THEN active ::= False ELSE skip"

lemma event_triggered_therm_flow [local_flow]: "local_flow_on [T \<leadsto> - K * (T - c)] T UNIV UNIV
  (\<lambda>\<tau>. [T \<leadsto> - exp (-K * \<tau>) * (c - T) + c])"
  by local_flow_on_auto

lemma thermostat_safe:
  shows "H{Tmin \<le> T \<and> T \<le> Tmax} 
    (LOOP (ctrl; dyn) INV (Tmin \<le> T \<and> T \<le> Tmax))
   {Tmin \<le> T \<and> T \<le> Tmax}"
  apply intro_loops
    apply (sequence "Tmin \<le> T \<and> T \<le> Tmax")
     apply wlp_full
    apply symbolic_exec
     apply (wlp_full local_flow: local_flow[where c=0, simplified] simp: field_simps)
  apply (smt (verit, best) K_ge0 Tmin_ge0 exp_le_one_iff mult_left_le split_mult_pos_le)
    apply (wlp_full local_flow: local_flow[where c=L, simplified])
  using K_ge0 Tmin_ge0
    apply (clarsimp simp: field_simps)
    apply (smt (verit, best) Tmax_le_Tlim affine_ineq exp_le_one_iff factorL(4) mult_nonneg_nonneg)
  by expr_auto+

end


subsection \<open> Refined thermostat \<close>
                              
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

dataspace refined_thermostat = 
  constants 
    Tmax :: real (* maximum comfortable temp. *)
    Tmin :: real (* minimum comfortable temp. *)
    L :: real (* highest temp. when thermostat is on *)
    K :: real (* freezing factor *)    
  assumes 
    Tmin_ge0: "0 < Tmin" 
    and Tmin_le_Tmax: "Tmin + 1 < Tmax" 
    and Tmax_le_Tlim: "Tmax < L"
    and K_ge0: "K > 0"
  variables 
    (* physical *)
    T :: real      (* temperature *)
    t :: real      (* time *)
    (* program *)
    temp :: real   (* for temperature measurements *)
    active :: bool (* whether thermostat is on or off *)

context refined_thermostat
begin

abbreviation "dyn \<equiv> IF \<not> active 
  THEN {T` = - K * T, t` = 1 | t \<le> - (ln (Tmin/temp))/K} 
  ELSE {T` = - K * (T - L), t` = 1 | t \<le> - (ln ((L - Tmax)/(L - temp)))/K}"

abbreviation "decide \<equiv> 
  IF \<not> active \<and> temp \<le> Tmin + 1 THEN active ::= True
  ELSE IF active \<and> temp \<ge> Tmax - 1 THEN active ::= False ELSE skip"

abbreviation "ctrl \<equiv> t ::= 0; temp ::= T; decide"

lemma refined_therm_flow [local_flow]: 
  "local_flow_on [T \<leadsto> - K * (T - c), t \<leadsto> 1] (T +\<^sub>L t) UNIV UNIV
  (\<lambda>\<tau>. [T \<leadsto> - exp (-K * \<tau>) * (c - T) + c, t \<leadsto> \<tau> + t])"
  by local_flow_on_auto

lemma thermostat_safe:
  "H{Tmin \<le> T \<and> T \<le> Tmax} 
    (LOOP (ctrl; dyn) INV (Tmin \<le> T \<and> T \<le> Tmax))
   {Tmin \<le> T \<and> T \<le> Tmax}"
  apply (intro_loops)
    apply (sequence "Tmin \<le> T \<and> T \<le> Tmax \<and> temp = T \<and> t = 0")
     apply (wlp_full)
    apply symbolic_exec
     apply (wlp_flow local_flow: local_flow[where c=0, simplified])
     apply (clarsimp simp: le_fun_def)
  using temp_dyn_down_real_arith[OF K_ge0 Tmin_ge0]
     apply expr_simp
    apply (wlp_flow local_flow: local_flow[where c=L, simplified])
    apply (clarsimp simp: le_fun_def)
  using temp_dyn_up_real_arith[OF K_ge0 _ _ Tmax_le_Tlim]
  by expr_auto+

end


subsection \<open> Time-triggered thermostat \<close>

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
    L :: real (* highest temp. when thermostat is on *)
    K :: real (* freezing factor *)    
    \<epsilon> :: real (* max increment/decrement of temp per sensing interval *)
  assumes 
    K_ge0: "K > 0"
    and eps_ge0: "\<epsilon> > 0"
    and eps_le_Tmin: "\<epsilon> < Tmin"
    and delta_ge_3eps: "Tmax - Tmin > 3 * \<epsilon>" 
    and L_ge_Tmax_eps: "L > Tmax + \<epsilon>"
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
    and Tmax_le_L: "Tmax < L"
  using delta_ge_3eps eps_ge0 L_ge_Tmax_eps
  by linarith+

lemma local_flow: "local_flow_on [T \<leadsto> - K * (T - c), t \<leadsto> 1] (T +\<^sub>L t) UNIV UNIV
  (\<lambda>\<tau>. [T \<leadsto> - exp (-K * \<tau>) * (c - T) + c, t \<leadsto> \<tau> + t])"
  by local_flow_on_auto

(* Temperature advances at most \<epsilon> units upwards or downwards 
before our sensor makes a measurement. *)
abbreviation "dyn \<equiv> IF \<not> active 
  THEN {T` = - K * T, t` = 1 | t \<le> - ln (1 - \<epsilon> / temp) / K} 
  ELSE {T` = - K * (T - L), t` = 1 | t \<le> - ln (\<epsilon> / (temp - L) + 1) / K}"

abbreviation "close_to_Tmin \<T> \<equiv> \<T> \<le> Tmin + 1.1 * \<epsilon>"
abbreviation "close_to_Tmax \<T> \<equiv> \<T> \<ge> Tmax - 1.1 * \<epsilon>"

abbreviation "decide \<equiv> 
  IF \<not> active \<and> close_to_Tmin temp THEN active ::= True
  ELSE IF active \<and> close_to_Tmax temp THEN active ::= False ELSE skip"

abbreviation "ctrl \<equiv> t ::= 0; temp ::= T; decide"

expression "pos_inv" is "Tmin \<le> T \<and> T \<le> Tmax \<and> temp = T \<and> t = 0 
  \<and> (close_to_Tmin temp \<longrightarrow> active) \<and> (close_to_Tmax temp \<longrightarrow> \<not> active)"

lemma thermostat_safe:
  "H{Tmin \<le> T \<and> T \<le> Tmax} 
    (LOOP (ctrl; dyn) INV (Tmin \<le> T \<and> T \<le> Tmax))
   {Tmin \<le> T \<and> T \<le> Tmax}"
  apply intro_loops
    apply (sequence pos_inv)
     apply wlp_full
  using delta_ge_3eps eps_ge0 apply force
    apply symbolic_exec
     apply (wlp_full local_flow: local_flow[where c=0, simplified])
     apply (hol_intros)
    using decr_in_ivl[OF K_ge0 eps_ge0 eps_le_Tmin L_ge_Tmax_eps]
        apply blast
       apply (smt (verit) K_ge0 affine_ineq eps_ge0 eps_le_Tmin 
        exp_le_one_iff more_arith_simps(8) zero_le_mult_iff) 
      apply (wlp_full local_flow: local_flow[where c=L, simplified])
      apply (hol_intros)
       apply (smt (verit, ccfv_SIG) K_ge0 L_ge_Tmax_eps affine_ineq eps_ge0 
        exp_le_one_iff more_arith_simps(8) zero_le_mult_iff)
    using incr_in_ivl[OF K_ge0 eps_ge0 eps_le_Tmin L_ge_Tmax_eps]
    by expr_auto+

end





end