theory HS_Exponential_Ex
  imports "Hybrid-Verification.Hybrid_Verification"
begin

subsubsection \<open> Classical exponential example \<close>

dataspace exponential =
  variables x::real y::real z::real
context exponential
begin

\<comment> \<open>Verified with differential ghosts \<close>

lemma exp_arith: "0 < (a::real) \<longleftrightarrow> (\<exists>b. a * b\<^sup>2 = 1)"
  by (auto, rule_tac x="1/sqrt(a)" in exI, simp add: power_divide)
     (metis not_square_less_zero power2_eq_square zero_less_mult_iff zero_less_one)

(* x>0 -> [{x'=-x}](x>0) *)
lemma dG_example: "H{x > 0} {x` = - x} {x > 0}"
  apply (dGhost "y" "x*y\<^sup>2 = 1" "1/2")
  apply (dInduct_auto)
  apply (expr_auto add: exp_arith)
  done

abbreviation "exp_flow \<tau> \<equiv> [x \<leadsto> x * exp (- \<tau>)]"

lemma "H{x > 0}(EVOL exp_flow G (\<lambda>s. {t. t \<ge> 0})){x > 0}"
  by (simp add: fbox_g_evol) expr_auto

lemma "H{x > 0}{EVOL x = x * exp (- \<tau>)}{x > 0}"
  by (hoare_wp_auto)

lemma local_flow_exp_flow: "local_flow_on [x \<leadsto> -x] x UNIV UNIV exp_flow"
  by (local_flow 1)

lemma flow_example: "H{x > 0} {x` = - x} {x > 0}"
  by (hoare_wp_auto local_flow: local_flow_exp_flow)

lemma "H{x \<ge> 0} {x` = - x} {x \<ge> 0}"
  apply (rule darboux_geq[of x y z, where g="-1"]; expr_simp add: framed_derivs 
      ldifferentiable closure usubst unrest_ssubst unrest usubst_eval; clarsimp?)
  subgoal
    by (subst lens_indep_comm; expr_simp)
  subgoal for s
    by expr_auto
      (rule_tac x="put\<^bsub>y\<^esub> s 1" in exI, simp)
  apply (metis indeps(3) indeps(6) lens_indep_comm)
  apply (simp add: frechet_derivative_fst)
  using bounded_linear_fst 
    bounded_linear_imp_differentiable 
  by blast

end

end