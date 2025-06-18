section \<open> Pendulum with force \<close>

theory Pendulum_with_force
  imports "Hybrid-Verification.Hybrid_Verification"
begin

lemma trig_prop:
  fixes g L k :: real
  assumes "L > 0" "k > 0" "g > 0" "g / L * (1 - cos(\<theta>)) + (1/2 * \<omega>\<^sup>2) < g / L" "-pi \<le> \<theta>" "\<theta> \<le> pi"
  shows "- pi / 2 < \<theta>" "\<theta> < pi / 2"
proof -
  have ge_0: "L * \<omega>\<^sup>2 / (2*g) \<ge> 0"
    using assms(1) assms(3) by auto
  from assms have less_cos: "L * \<omega>\<^sup>2 / (2*g) < cos \<theta>"
    by (simp add: field_simps)
  hence less_1: "L * \<omega>\<^sup>2 / (2*g) < 1"
    by (metis add.commute add_le_cancel_left add_mono_thms_linordered_field(3) cos_le_one not_less)
  hence "arccos(L * \<omega>\<^sup>2 / (2*g)) > arccos(cos(\<theta>))"
    using arccos_less_arccos ge_0 less_cos by auto
  hence "arccos(L * \<omega>\<^sup>2 / (2*g)) > \<theta>"
    by (smt (verit, best) arccos arccos_cos assms(6) ge_0 less_1)
  thus "- pi / 2 < \<theta>" "\<theta> < pi / 2"
    apply (smt (verit) \<open>arccos (cos \<theta>) < arccos (L * \<omega>\<^sup>2 / (2 * g))\<close> arccos_0 arccos_cos2 arccos_le_arccos assms(5) divide_minus_left ge_0 less_1)
    using \<open>\<theta> < arccos (L * \<omega>\<^sup>2 / (2 * g))\<close> arccos_le_pi2 ge_0 less_1 by fastforce
qed

dataspace sys = 
  constants g :: real L :: real k :: real
  assumes L_gr_0: "L > 0" and K_gr_0: "k > 0" and g_gr_0: "g > 0"
  variables \<omega> :: real \<theta> :: real push :: real
context sys
begin

lemma L_neq_0 [simp]: "L \<noteq> 0"
  using L_gr_0 by blast

abbreviation "ctrl \<equiv> push ::= ?; IF (1/2 * (\<omega> - push)\<^sup>2 < g / L * cos(\<theta>)) THEN \<omega> ::= \<omega> - push ELSE skip"

abbreviation "ode \<equiv> {\<theta>` = \<omega>, \<omega>` = -g/L * sin(\<theta>) - k * \<omega> | -pi \<le> \<theta> \<and> \<theta> \<le> pi}"

abbreviation "program \<equiv> LOOP (ctrl ; ode) INV (-pi \<le> \<theta> \<and> \<theta> \<le> pi \<and> g / L * (1 - cos(\<theta>)) + (1/2 * \<omega>\<^sup>2) < g / L)"

abbreviation "invariant \<equiv> (-pi \<le> \<theta> \<and> \<theta> \<le> pi \<and> (g / L * (1 - cos(\<theta>)) + (1/2 * \<omega>\<^sup>2) < g / L))\<^sup>e"

lemma ode_correct: "H{invariant} ode {invariant}"
  by (dInduct_mega, meson K_gr_0 dual_order.order_iff_strict mult_nonneg_nonneg zero_le_square)

lemma ctrl_correct: "H{invariant} ctrl {invariant}"
  apply wlp_simp
  apply (expr_auto)
  using L_gr_0 apply (simp add: field_simps)
  by (smt (verit, del_insts) factorR(1) mult.commute mult.left_commute mult_less_cancel_left_pos)

lemma inv_impl_postcondition: "`invariant \<longrightarrow> - pi / 2 < \<theta> \<and> \<theta> < pi / 2`"
  by (metis (no_types, lifting) L_gr_0 SEXP_def g_gr_0 tautI trig_prop(1) trig_prop(2))

lemma program_correct: "H{\<theta> = 0 \<and> \<omega> = 0} program {- pi / 2 < \<theta> \<and> \<theta> < pi / 2}"
  apply intro_loops
  apply (rule hoare_kcomp_inv)
  using ctrl_correct apply blast
  using ode_correct apply blast
  apply expr_simp
  using L_gr_0 divide_pos_pos g_gr_0 apply blast
  using inv_impl_postcondition apply blast
  done

end



end