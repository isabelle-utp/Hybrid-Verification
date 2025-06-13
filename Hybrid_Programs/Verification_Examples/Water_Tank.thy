section \<open> Pendulum with force \<close>

theory Water_Tank
  imports "Hybrid-Verification.Hybrid_Verification"
begin


subsection \<open> Event-triggered water tank \<close>


dataspace event_triggered_water_tank =
  constants 
    c\<^sub>o :: real (* rate of outflow *)
    c\<^sub>i :: real (* rate of inflow *)
    Hmax :: real (* maximum safe water-level *)
    Hmin :: real (* minimum safe water-level *)    
  assumes 
    co_ge_0: "0 < c\<^sub>o" 
    and ci_ge_0: "c\<^sub>o < c\<^sub>i"
  variables 
    (* physical *)
    h :: real      (* water level *)
    (* program *)
    active :: bool (* whether the pump is on or off *)

context event_triggered_water_tank
begin

abbreviation "ctrl \<equiv>
  IF \<not> active \<and> h \<le> Hmin THEN active := True
  ELSE IF active \<and> h \<ge> Hmax THEN active := False"

abbreviation "dyn \<equiv> IF \<not> active 
  THEN {h` = - c\<^sub>o | h \<ge> Hmin}
  ELSE {h` = c\<^sub>i - c\<^sub>o | h \<le> Hmax}"

lemma tank_flow [local_flow]: 
  "local_flow_on [h \<leadsto> k] h UNIV UNIV (\<lambda>\<tau>. [h \<leadsto> k * \<tau> + h])"
  by local_flow_on_auto

lemma "H{Hmin \<le> h \<and> h \<le> Hmax} 
    (LOOP (ctrl; dyn) INV (Hmin \<le> h \<and> h \<le> Hmax))
   {Hmin \<le> h \<and> h \<le> Hmax}"
  apply intro_loops
    apply (sequence "Hmin \<le> h \<and> h \<le> Hmax")
     apply wlp_full
    apply symbolic_exec
     apply (wlp_full local_flow: local_flow simp: field_simps)
     apply (metis co_ge_0 cross3_simps(21) le_add_same_cancel1 
      less_le_not_le order.trans zero_le_mult_iff)
    apply (wlp_full local_flow: local_flow simp: field_simps)
     apply (metis (no_types, opaque_lifting) ci_ge_0 diff_add_cancel diff_add_eq 
      diff_ge_0_iff_ge less_le_not_le order.trans right_diff_distrib zero_le_mult_iff)
  by expr_simp+

lemma water_tank_safe: 
  "H{Hmin \<le> h \<and> h \<le> Hmax} 
    (LOOP (ctrl; dyn) INV (Hmin \<le> h \<and> h \<le> Hmax))
   {Hmin \<le> h \<and> h \<le> Hmax}"
  by (wlp_full local_flow: tank_flow)
    (metis add.commute add_increasing2 ci_ge_0 co_ge_0 
      diff_ge_0_iff_ge diff_le_eq less_le_not_le zero_le_mult_iff)

end


subsection \<open> Refined water tank \<close>

dataspace refined_water_tank =
  constants 
    c\<^sub>o :: real (* rate of outflow *)
    c\<^sub>i :: real (* rate of inflow *)
    Hmax :: real (* maximum safe water-level *)
    Hmin :: real (* minimum safe water-level *)    
  assumes 
    co_ge_0: "0 < c\<^sub>o" 
    and ci_ge_0: "c\<^sub>o < c\<^sub>i"
  variables 
    (* physical *)
    h :: real      (* water level *)
    t :: real      (* time *)
    (* program *)
    height :: real (* for height measurements *)
    active :: bool (* whether the pump is on or off *)

context refined_water_tank
begin

abbreviation "ctrl \<equiv> t := 0; height := h;
  IF \<not> active \<and> height \<le> Hmin THEN active := True
  ELSE IF active \<and> height \<ge> Hmax THEN active := False"

abbreviation "dyn \<equiv> IF \<not> active 
  THEN {h` = - c\<^sub>o, t` = 1 | t \<le> (Hmin - height)/(- c\<^sub>o)}
  ELSE {h` = c\<^sub>i - c\<^sub>o, t` = 1 | t \<le> (Hmax - height)/(c\<^sub>i - c\<^sub>o)}"

lemma tank_flow [local_flow]: 
  "local_flow_on [h \<leadsto> k, t \<leadsto> 1] (h+\<^sub>Lt) UNIV UNIV (\<lambda>\<tau>. [h \<leadsto> k * \<tau> + h, t \<leadsto> \<tau> + t])"
  by local_flow_on_auto

lemma
  "H{Hmin \<le> h \<and> h \<le> Hmax} 
    (LOOP (ctrl; dyn) INV (Hmin \<le> h \<and> h \<le> Hmax))
   {Hmin \<le> h \<and> h \<le> Hmax}"
  apply intro_loops
    apply (sequence "Hmin \<le> h \<and> h \<le> Hmax \<and> height = h \<and> t = 0")
     apply wlp_full
    apply symbolic_exec
     apply (wlp_full local_flow: tank_flow simp: field_simps)
     apply (smt (verit, best) co_ge_0 diff_divide_distrib pos_le_divide_eq zero_le_mult_iff)
    apply (wlp_full local_flow: tank_flow simp: field_simps)
    apply (smt (verit, best) ci_ge_0 mult_mono pos_le_divide_eq right_diff_distrib)
  by expr_simp+

lemma water_tank_safe:
  "H{Hmin \<le> h \<and> h \<le> Hmax} 
    (LOOP (ctrl; dyn) INV (Hmin \<le> h \<and> h \<le> Hmax))
   {Hmin \<le> h \<and> h \<le> Hmax}"
  by (wlp_full local_flow: tank_flow simp: field_simps)
    (hol_intros; smt (verit, best) ci_ge_0 co_ge_0 le_minus_divide_eq mult_le_0_iff 
      mult_sign_intros(1) mult_mono' pos_le_divide_eq right_diff_distrib)

end

lemma level_tank_arith:
  assumes "Hmin \<le> h" and "h \<le> Hmax" and "0 \<le> (t::real)"
    and bound: "\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> \<tau> \<le> \<epsilon> / (c\<^sub>i - c\<^sub>o)"
    and "c\<^sub>o < c\<^sub>i" and "\<epsilon> > 0"
    and not_close_to_Hmax: "\<not> Hmax - 11 * \<epsilon> / 10 \<le> h"
  shows "Hmin \<le> (c\<^sub>i - c\<^sub>o) * t + h" 
    and "(c\<^sub>i - c\<^sub>o) * t + h \<le> Hmax"
proof-
  show "Hmin \<le> (c\<^sub>i - c\<^sub>o) * t + h" 
    using \<open>0 \<le> t\<close> \<open>c\<^sub>o < c\<^sub>i\<close> \<open>Hmin \<le> h\<close>
    by (simp add: add.commute add_increasing2)
  have "Hmax > h + 11 * \<epsilon> / 10"
    using not_close_to_Hmax
    by linarith
  moreover have "h + 11 * \<epsilon> / 10 > h + \<epsilon>"
    using \<open>\<epsilon> > 0\<close>
    by simp
  moreover have "h + \<epsilon> \<ge> (c\<^sub>i - c\<^sub>o) * t + h"
    using bound \<open>0 \<le> t\<close>
    by (simp add: assms(5) mult.commute pos_le_divide_eq)
  ultimately show "(c\<^sub>i - c\<^sub>o) * t + h \<le> Hmax"
    by linarith
qed  


subsection \<open> Level-triggered water tank \<close>

dataspace level_triggered_water_tank =
  constants 
    c\<^sub>o :: real (* rate of outflow *)
    c\<^sub>i :: real (* rate of inflow *)
    Hmax :: real (* maximum safe water-level *)
    Hmin :: real (* minimum safe water-level *)
    \<epsilon> :: real (* max increment/decrement of water level per sensing interval *)
  assumes 
    co_ge_0: "0 < c\<^sub>o" 
    and ci_ge_0: "c\<^sub>o < c\<^sub>i"
    and eps_ge0: "\<epsilon> > 0"
    and eps_le_Tmin: "\<epsilon> < Hmin"
    and delta_ge_3eps: "Hmax - Hmin > 3 * \<epsilon>" 
  variables 
    (* physical *)
    h :: real      (* water level *)
    t :: real      (* time *)
    (* program *)
    height :: real (* for height measurements *)
    active :: bool (* whether the pump is on or off *)

context level_triggered_water_tank
begin

abbreviation "ctrl \<equiv> t := 0; height := h;
  IF \<not> active \<and> height \<le> Hmin + 1.1 * \<epsilon> THEN active := True
  ELSE IF active \<and> height \<ge> Hmax - 1.1 * \<epsilon> THEN active := False"

abbreviation "dyn \<equiv> IF \<not> active 
  THEN {h` = - c\<^sub>o, t` = 1 | t \<le> \<epsilon>/(- c\<^sub>o)}
  ELSE {h` = c\<^sub>i - c\<^sub>o, t` = 1 | t \<le> \<epsilon>/(c\<^sub>i - c\<^sub>o)}"

lemma tank_flow [local_flow]: 
  "local_flow_on [h \<leadsto> k, t \<leadsto> 1] (h+\<^sub>Lt) UNIV UNIV (\<lambda>\<tau>. [h \<leadsto> k * \<tau> + h, t \<leadsto> \<tau> + t])"
  by local_flow_on_auto

expression "pos_inv" is "Hmin \<le> h \<and> h \<le> Hmax \<and> height = h \<and> t = 0 
  \<and> (h \<le> Hmin + 1.1 * \<epsilon> \<longrightarrow> active) \<and> (h \<ge> Hmax - 1.1 * \<epsilon> \<longrightarrow> \<not> active)"

lemma water_tank_safe:
  "H{Hmin \<le> h \<and> h \<le> Hmax} 
    (LOOP (ctrl; dyn) INV (Hmin \<le> h \<and> h \<le> Hmax))
   {Hmin \<le> h \<and> h \<le> Hmax}"
  apply intro_loops
    apply (sequence pos_inv)
  apply wlp_full
  using delta_ge_3eps eps_ge0 apply force
    apply symbolic_exec
     apply (wlp_full local_flow: tank_flow simp: field_simps)
  using co_ge_0 divide_pos_pos eps_ge0 apply force
     apply (wlp_full local_flow: tank_flow)
  using level_tank_arith[of Hmin \<open>h<_>\<close> Hmax] ci_ge_0 eps_ge0
    apply blast
  by expr_simp+

end


subsection \<open> Time-triggered water tank \<close>

dataspace time_triggered_water_tank =
  constants 
    c\<^sub>o :: real (* rate of outflow *)
    c\<^sub>i :: real (* rate of inflow *)
    Hmax :: real (* maximum safe water-level *)
    Hmin :: real (* minimum safe water-level *)
    \<epsilon> :: real (* max increment/decrement of water level per sensing interval *)
  assumes 
    co_ge_0: "0 < c\<^sub>o"
    and ci_ge_0: "c\<^sub>o < c\<^sub>i"
    and eps_ge0: "\<epsilon> > 0"
    and eps_le_Tmin: "\<epsilon> < Hmin"
    and delta_ge_3eps: "Hmax - Hmin > 3 * max (c\<^sub>o * \<epsilon>) ((c\<^sub>i - c\<^sub>o) * \<epsilon>)" 
  variables 
    (* physical *)
    h :: real      (* water level *)
    t :: real      (* time *)
    (* program *)
    height :: real (* for height measurements *)
    active :: bool (* whether the pump is on or off *)

context time_triggered_water_tank
begin

abbreviation "ctrl \<equiv> t := 0; height := h;
  IF \<not> active \<and> height \<le> Hmin + c\<^sub>o * \<epsilon> THEN active := True
  ELSE IF active \<and> height \<ge> Hmax - (c\<^sub>i - c\<^sub>o) * \<epsilon> THEN active := False"

abbreviation "dyn \<equiv> IF \<not> active 
  THEN {h` = - c\<^sub>o, t` = 1 | t \<le> \<epsilon>}
  ELSE {h` = c\<^sub>i - c\<^sub>o, t` = 1 | t \<le> \<epsilon>}"

lemma tank_flow [local_flow]: 
  "local_flow_on [h \<leadsto> k, t \<leadsto> 1] (h+\<^sub>Lt) UNIV UNIV (\<lambda>\<tau>. [h \<leadsto> k * \<tau> + h, t \<leadsto> \<tau> + t])"
  by local_flow_on_auto

expression "pos_inv" is "Hmin \<le> h \<and> h \<le> Hmax \<and> height = h \<and> t = 0 
  \<and> (h \<le> Hmin + c\<^sub>o * \<epsilon> \<longrightarrow> active) \<and> (h \<ge> Hmax - (c\<^sub>i - c\<^sub>o) * \<epsilon> \<longrightarrow> \<not> active)"

lemma water_tank_safe:
  "H{Hmin \<le> h \<and> h \<le> Hmax} 
    (LOOP (ctrl; dyn) INV (Hmin \<le> h \<and> h \<le> Hmax))
   {Hmin \<le> h \<and> h \<le> Hmax}"
  apply intro_loops
    apply (sequence pos_inv)
  apply wlp_full
  using delta_ge_3eps eps_ge0 apply force
    apply symbolic_exec
     apply (wlp_full local_flow: tank_flow)
  apply (smt (verit, best) co_ge_0 mult.commute mult_less_0_iff mult_right_mono)
     apply (wlp_full local_flow: tank_flow)
  apply (smt (verit, best) ci_ge_0 mult_mono zero_le_mult_iff)
  by expr_simp+

end

end