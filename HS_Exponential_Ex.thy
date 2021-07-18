theory HS_Exponential_Ex
  imports HS_Lens_Spartan HS_Lie_Derivatives
begin

lit_vars

subsubsection \<open> Classical exponential example \<close>

locale exponential_evol =
  fixes x :: "real \<Longrightarrow> real^1"
  assumes x_def [simp]: "x \<equiv> vec_lens 1"
begin

term "frame_timed x (\<lambda>t. [x \<leadsto> x])"
term " [x \<leadsto> x]"

lemma "D (\<lambda>r. frame_timed x (\<lambda>t. [x \<leadsto> x]) s 0 0) \<mapsto> (\<lambda>r. frame_timed x (\<lambda>t. [x \<leadsto> x]) s 0 0) (at t within T)"
  by (expr_auto)

lemma "D (\<lambda>t. [x \<leadsto> c] s) \<mapsto> (\<lambda>t. [x \<leadsto> 0] s) (at t within T)"
  by (expr_auto)

lemma "D (\<lambda>t. [x \<leadsto> x + y] s) \<mapsto> (\<lambda>t. [x \<leadsto> 0] s) (at t within T)"
  by (expr_auto)

\<comment> \<open>Verified with annotated dynamics \<close>

abbreviation "exp_f \<equiv> [x \<leadsto> -x]" (* x>0 -> [{x'=-x}](x>0) *)
abbreviation "exp_flow \<tau> \<equiv> [x \<leadsto> x * exp (- \<tau>)]"

lemma "D (\<lambda>t. exp_flow t s) = (\<lambda>t. exp_f (exp_flow t s)) on {0--t}"
  by (expr_auto, auto intro!: poly_derivatives)


lemma "\<^bold>{x > 0\<^bold>}(EVOL exp_flow G (\<lambda>s. {t. t \<ge> 0}))\<^bold>{x > 0\<^bold>}"
  by (simp add: fbox_g_evol) expr_auto

\<comment> \<open>Verified with the flow \<close>

lemma local_lipschitz_exp_f: "local_lipschitz UNIV UNIV (\<lambda>t::real. exp_f)"
  apply(simp_all add: local_lipschitz_def lipschitz_on_def, clarsimp)
    apply(rule_tac x="1" in exI, clarsimp, rule_tac x=1 in exI)
  by (clarsimp, expr_auto, simp add: dist_norm norm_vec_def)

lemma local_flow_exp_flow: "local_flow exp_f UNIV UNIV exp_flow"
  apply(unfold_locales)
  apply (auto)
  using local_lipschitz_exp_f apply force
   apply (expr_auto, auto intro!: poly_derivatives, expr_auto)
  done

(* x>0 -> [{x'=-x}](x>0) *)
lemma "\<^bold>{x > 0\<^bold>}(x\<acute>= exp_f & G)\<^bold>{x > 0\<^bold>}"
  apply (subst local_flow.fbox_g_ode_subset[OF local_flow_exp_flow])
   apply (simp)
  apply (expr_auto)
  done

end

dataspace exponential =
  variables x::real y::real
context exponential
begin

\<comment> \<open>Verified with differential ghosts \<close>

abbreviation "dyn \<equiv> {x` = - x}"

lemma exp_arith: "0 < (a::real) \<longleftrightarrow> (\<exists>b. a * b\<^sup>2 = 1)"
  by (auto, rule_tac x="1/sqrt(a)" in exI, simp add: power_divide)
     (metis not_square_less_zero power2_eq_square zero_less_mult_iff zero_less_one)

(* x>0 -> [{x'=-x}](x>0) *)
lemma dG_example: "\<^bold>{x > 0\<^bold>}dyn\<^bold>{x > 0\<^bold>}"
  apply (dGhost "y" "(x*y\<^sup>2 = 1)\<^sub>e" "1/2")
  apply (expr_auto add: exp_arith)
  apply (dInduct_auto)
  done

abbreviation (input) "exp_f \<equiv> [x \<leadsto> -x]" (* x>0 -> [{x'=-x}](x>0) *)
abbreviation (input) "exp_flow \<tau> \<equiv> [x \<leadsto> x * exp (- \<tau>)]"

term exp_f 
term exp_flow

term "loc_ode (\<lambda> _. exp_f) x s"

lemma "D (\<lambda>t. frame_timed x exp_flow s t (get\<^bsub>x\<^esub> s)) = 
  (\<lambda> t. frame_timed x (\<lambda> _. exp_f) s t (frame_timed x exp_flow s t (get\<^bsub>x\<^esub> s))) on {0--t}"
  by (expr_auto, auto intro!: poly_derivatives)

term "(\<lambda>t. exp_f (exp_flow t s))"

term "loc_ode (\<lambda> t. exp_f)"

lemma "\<^bold>{x > 0\<^bold>}(EVOL exp_flow G (\<lambda>s. {t. t \<ge> 0}))\<^bold>{x > 0\<^bold>}"
  by (simp add: fbox_g_evol) expr_auto

lemma "\<^bold>{x > 0\<^bold>}{EVOL x = x * exp (- \<tau>)}\<^bold>{x > 0\<^bold>}"
  by (hoare_wp_auto)

lemma local_flow_exp_flow: "local_flow_on exp_f x UNIV UNIV exp_flow"
  by (local_flow 1)

lemma flow_example: "\<^bold>{x > 0\<^bold>}dyn\<^bold>{x > 0\<^bold>}"
  by (hoare_wp_auto local_flow: local_flow_exp_flow)

end

end