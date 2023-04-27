theory Pendulum_with_force
  imports "Hybrid-Verification.Proof_Automation" "HOL-Decision_Procs.Approximation"
begin

lemma trig_prop:
  fixes g L k :: real
  assumes "L > 0" "k > 0" "g > 0" "g / L * (1 - cos(\<theta>)) + (1/2 * w\<^sup>2) < g / L" "-pi < \<theta>" "\<theta> < pi"
  shows "- pi / 2 < \<theta>" "\<theta> < pi / 2"
proof -
  have ge_0: "L * w\<^sup>2 / (2*g) \<ge> 0"
    using assms(1) assms(3) by auto
  from assms have less_cos: "L * w\<^sup>2 / (2*g) < cos \<theta>"
    by (simp add: field_simps)
  hence less_1: "L * w\<^sup>2 / (2*g) < 1"
    by (metis add.commute add_le_cancel_left add_mono_thms_linordered_field(3) cos_le_one not_less)
  hence "arccos(L * w\<^sup>2 / (2*g)) > arccos(cos(\<theta>))"
    using arccos_less_arccos ge_0 less_cos by auto
  hence "arccos(L * w\<^sup>2 / (2*g)) > \<theta>"
    by (smt (verit, best) arccos arccos_cos assms(6) ge_0 less_1)
  thus "- pi / 2 < \<theta>" "\<theta> < pi / 2"
    apply (smt (verit) \<open>arccos (cos \<theta>) < arccos (L * w\<^sup>2 / (2 * g))\<close> arccos_0 arccos_cos2 arccos_le_arccos assms(5) divide_minus_left ge_0 less_1)
    using \<open>\<theta> < arccos (L * w\<^sup>2 / (2 * g))\<close> arccos_le_pi2 ge_0 less_1 by fastforce
qed

dataspace sys = 
  constants g :: real L :: real k :: real
  assumes L_gr_0: "L > 0" and K_gr_0: "k > 0" and g_gr_0: "g > 0"
  variables w :: real \<theta> :: real push :: real
context sys
begin

lemma L_neq_0 [simp]: "L \<noteq> 0"
  using L_gr_0 by blast
  

abbreviation "program \<equiv> LOOP ((push ::= ? ; IF (1/2 * (w - push)\<^sup>2 < g / L * cos(\<theta>)) THEN w ::= w - push ELSE skip);
                              {\<theta>` = w, w` = -g/L * sin(\<theta>) - k * w}) INV (g / L * (1 - cos(\<theta>)) + (1/2 * w\<^sup>2) < g / L)"

lemma ode_correct: "\<^bold>{(g / L * (1 - cos(\<theta>)) + (1/2 * w\<^sup>2) < g / L)\<^bold>} {\<theta>` = w, w` = -g/L * sin(\<theta>) - k * w | -pi < \<theta> \<and> \<theta> < pi} \<^bold>{(g / L * (1 - cos(\<theta>)) + (1/2 * w\<^sup>2) < g / L)\<^bold>}"
  by (dInduct_auto, meson K_gr_0 dual_order.order_iff_strict mult_nonneg_nonneg zero_le_square)

lemma ctrl_correct: "\<^bold>{(g / L * (1 - cos(\<theta>)) + (1/2 * w\<^sup>2) < g / L)\<^bold>} (push ::= ? ; IF (1/2 * (w - push)\<^sup>2 < g / L * cos(\<theta>)) THEN w ::= w - push ELSE skip) \<^bold>{(g / L * (1 - cos(\<theta>)) + (1/2 * w\<^sup>2) < g / L)\<^bold>}"
  apply wlp_simp
  apply (simp_all add: usubst_eval)
  apply (expr_auto)
  using L_gr_0 apply (simp add: field_simps)
  by (metis (no_types, opaque_lifting) distrib_left mult.left_commute mult_less_cancel_left_pos)

lemma inv_impl_postcondition: "`g / L * (1 - cos(\<theta>)) + (1/2 * w\<^sup>2) < g / L \<and> -pi < \<theta> \<and> \<theta> < pi \<longrightarrow> - pi / 2 < \<theta> \<and> \<theta> < pi / 2`"
  by (metis (no_types, lifting) L_gr_0 SEXP_def g_gr_0 tautI trig_prop(1) trig_prop(2))


end



end