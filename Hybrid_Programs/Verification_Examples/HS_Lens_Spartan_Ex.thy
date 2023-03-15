theory HS_Lens_Spartan_Ex
  imports "Hybrid-Verification.Hybrid_Verification"
begin

subsection \<open> Matrices \<close>

abbreviation mtx_circ :: "2 sq_mtx" ("A")
  where "A \<equiv> mtx  
   ([0,  1] # 
    [-1, 0] # [])"

lemma nat_of_2_type_2_eq_0: "nat_of (2::2) = 0"
  using exhaust_2 by (metis nat_of_0 zero_neq_one)

lemma "A = to_mtx \<^bold>[[0, - 1], [1, 0]\<^bold>]"
  unfolding mtx_def
  apply(simp add: to_mtx_inject vector_def)
  apply(simp only: vec_eq_iff, clarify)
  using exhaust_2 by (auto simp: nat_of_2_type_2_eq_0)


lit_vars

alphabet ss =
  x :: real
  y :: real
  z :: real

text \<open> Step-by-step Proof Strategy Example \<close>

lemma "`|\<questiondown>x > 1? ; x ::= x + 1 ; x ::= x\<^sup>2] (x > 3)`"
  \<comment> \<open> (1) Apply the simplification laws for @{const fbox} \<close>
  apply (simp add: wlp)
  \<comment> \<open> (2) Evaluate the substitution laws \<close>
  apply (simp add: usubst_eval)
  \<comment> \<open> (3) Unfold into a pure lens expression and apply introduction laws \<close>
  apply (auto simp add: taut_def)
  \<comment> \<open> (4) Expand out lenses and split state space \<close>
  apply (simp add: alpha_splits lens_defs)
  \<comment> \<open> (5) Discharge the remaining proof obligation \<close>
  apply (simp add: field_simps)
  using less_1_mult apply fastforce 
  done
    
lemma "`|\<questiondown>x > 1? ; x ::= x + 1 ; x ::= x\<^sup>2] (x > 3)`"
  apply (simp add: wlp usubst_eval taut_def)
  \<comment> \<open> (4) Expand out lenses and split state space \<close>
  apply (simp add:  lens_defs)
  \<comment> \<open> (5) Discharge the remaining proof obligation \<close>
  apply (simp add: field_simps)
  using less_1_mult apply fastforce 
  done

lemma "(r\<^sup>2 = x\<^sup>2 + y\<^sup>2)\<^sub>e \<le> |x ::= 4; y ::= 3] (5\<^sup>2 = x\<^sup>2 + y\<^sup>2)"
  by (auto simp: wlp usubst_eval)

lemma pendulum: "\<^bold>{r\<^sup>2 = x\<^sup>2 + y\<^sup>2\<^bold>} {(x, y)` = (y, -x)} \<^bold>{r\<^sup>2 = x\<^sup>2 + y\<^sup>2\<^bold>}"
  by dInduct

\<comment> \<open> Partial derivatives? \<close>

lemma "\<D>\<^bsub>x\<^esub>\<langle>subst\<rangle> [expr]\<^sub>e = lframe_frechetD x subst (expr::'a ss_scheme \<Rightarrow> real)"
 by (simp add: lframe_frechetD_alt)

lemma "lframe_frechetD x subst expr s = 
  (SOME f'. D (expr \<circ> put\<^bsub>x\<^esub> s) \<mapsto> f' (at (get\<^bsub>x\<^esub> s))) (get\<^bsub>x\<^esub> (subst s))"
  unfolding lframe_frechetD_alt frechet_derivative_def by (simp add: comp_def)

lemma "lframe_frechetD x f expr s = 
  (SOME f'. bounded_linear f' \<and>
    (\<forall>e>0. \<exists>d>0. \<forall>y\<in>UNIV. \<parallel>y - get\<^bsub>x\<^esub> s\<parallel> < d \<longrightarrow>
      \<parallel>expr (put\<^bsub>x\<^esub> s y) - expr (put\<^bsub>x\<^esub> s (get\<^bsub>x\<^esub> s)) - f' (y - get\<^bsub>x\<^esub> s)\<parallel> \<le> e * \<parallel>y - get\<^bsub>x\<^esub> s\<parallel>))
  (get\<^bsub>x\<^esub> (f s))"
  unfolding lframe_frechetD_alt frechet_derivative_def has_derivative_within_alt 
  by (simp add: comp_def)

lemma "(x\<^sup>2 * y)\<^sub>e = (\<lambda>s. (get\<^bsub>x\<^esub> s)^2 * (get\<^bsub>y\<^esub> s))"
  unfolding SEXP_def by simp

lemma "\<D>\<^bsub>x\<^esub>\<langle>[x \<leadsto> 1, y \<leadsto> 1]\<rangle> (x\<^sup>2 * y) 
  = (\<lambda>s. (SOME f'. D ((x\<^sup>2 * y)\<^sub>e \<circ> (put\<^bsub>x\<^esub> s)) \<mapsto> f' (at (get\<^bsub>x\<^esub> s))) (get\<^bsub>x\<^esub> ([x \<leadsto> 1, y \<leadsto> 1] s)))"
  unfolding lframe_frechetD_alt frechet_derivative_def by (simp add: comp_def)

lemma "\<D>\<^bsub>x\<^esub>\<langle>[x \<leadsto> 1, y \<leadsto> 1]\<rangle> (x\<^sup>2 * y) = (2 * x * y)\<^sub>e"
  by (simp add: framed_derivs ldifferentiable usubst)

lemma "\<D>\<^bsub>x\<^esub>\<langle>[x \<leadsto> 2, y \<leadsto> 1]\<rangle> (x\<^sup>2 * y) = (4 * x * y)\<^sub>e"
  by (simp add: framed_derivs ldifferentiable usubst)

lemma "\<D>\<^bsub>y\<^esub>\<langle>[x \<leadsto> 3, y \<leadsto> 2]\<rangle> (x\<^sup>2 * y) = (2 * x\<^sup>2 * 1)\<^sub>e"
  by (simp add: framed_derivs ldifferentiable usubst field_simps)

lemma "\<D>\<^bsub>y\<^esub>\<langle>[x \<leadsto> 1, y \<leadsto> 1]\<rangle> (x\<^sup>2 * y) = (x\<^sup>2 * 1)\<^sub>e"
  by (simp add: framed_derivs ldifferentiable usubst)

lemma "\<D>\<^bsub>x +\<^sub>L y\<^esub>\<langle>[x \<leadsto> 1, y \<leadsto> 1]\<rangle> (x\<^sup>2 * y) = (x\<^sup>2 + 2 * x * y)\<^sub>e"
  by (simp add: framed_derivs ldifferentiable usubst)

lemma "\<D>\<^bsub>z\<^esub>\<langle>[x \<leadsto> 1, y \<leadsto> 1, z \<leadsto> 1]\<rangle> (x\<^sup>2 * y + z * y) = (y)\<^sub>e"
   by (simp add: framed_derivs ldifferentiable usubst)

lemma "\<D>\<^bsub>x +\<^sub>L y +\<^sub>L z\<^esub>\<langle>[x \<leadsto> 1, y \<leadsto> 1, z \<leadsto> 1]\<rangle> (x\<^sup>2 * y + z * y) = (x\<^sup>2 + 2 * x * y + y + z)\<^sub>e"
   by (simp add: framed_derivs ldifferentiable usubst field_simps)

lemma "\<D>\<^bsub>x +\<^sub>L y +\<^sub>L z\<^esub>\<langle>[x \<leadsto> 1, y \<leadsto> 1, z \<leadsto> 2]\<rangle> (x\<^sup>2 * y + z * y) = (x\<^sup>2 + 2 * x * y + 2*y + z)\<^sub>e"
   by (simp add: framed_derivs ldifferentiable usubst field_simps)

lemma "\<D>\<^bsub>x\<^esub>\<langle>[x \<leadsto> 2*x]\<rangle> x\<^sup>2 = (4 * x\<^sup>2)\<^sub>e"
   by (simp add: framed_derivs ldifferentiable usubst field_simps)


text \<open> We create the bouncing ball in a locale context using the command "dataspace", which
  generates abstract lenses and contextual information. \<close>

dataspace bball =
  constants 
    g :: real \<comment> \<open> Gravitational acceleration constant \<close>
    H :: real \<comment> \<open> The initial or maximum height of the ball \<close>
    c :: real \<comment> \<open> The damping coefficient applied upon rebound \<close>
  assumes g_pos: "g > 0" \<comment> \<open> The gravitational constant should be strictly positive (e.g. 9.81) \<close>
  and c_pos: "c > 0" \<comment> \<open> The damping coefficient is greater than 0... \<close>
  and c_le_one: "c \<le> 1" \<comment> \<open> ... and no greater than 1, otherwise it increases its bounce. \<close>
  and H_pos: "H \<ge> 0"
  variables h::real  v::real

context bball
begin

text \<open> Here is the invariant we wish to prove: it is sufficient to show that always $h \le H$. \<close>

abbreviation "Inv \<equiv> (h \<ge> 0 \<and> v\<^sup>2 \<le> 2*g*(H - h))\<^sup>e"
abbreviation "Dynamics \<equiv> {h` = v, v` = -g | h \<ge> 0}"
abbreviation "Ctrl \<equiv> IF h = 0 THEN v ::= -c * v ELSE skip"

definition BBall :: "'st prog" where "BBall = (Dynamics ; Ctrl)\<^sup>*"

text \<open> We first prove that it is an invariant of the dynamics using Hoare logic. \<close>

lemma "\<^bold>{@Inv\<^bold>}Dynamics\<^bold>{@Inv\<^bold>}"
  by dInduct_mega

lemma l1: "\<^bold>{@Inv\<^bold>}Dynamics\<^bold>{@Inv\<^bold>}"
  apply (rule hoare_conj_inv)
  apply (rule diff_weak_on_rule) \<comment> \<open> Differential weakening (invariant first conjunct) \<close>
   apply (simp)
   apply (dInduct)
  done

text \<open> Next, we prove its also an invariant of the controller. This requires a call to sledgehammer. \<close>

lemma l2: "\<^bold>{@Inv\<^bold>}Ctrl\<^bold>{@Inv\<^bold>}"
  by (hoare_wp_auto)
     (smt c_le_one c_pos mult_less_cancel_right1 power_le_one_iff power_mult_distrib zero_le_power2)

text \<open> As a consequence, it is an invariant of the whole system. \<close>

lemma l3: "\<^bold>{@Inv\<^bold>}BBall\<^bold>{@Inv\<^bold>}"
  unfolding BBall_def
  using hoare_kcomp_inv hoare_kstar_inv l1 l2
  by blast


text \<open> We can now show the safety property we desire using the consequence rule and sledgehammer. \<close>

lemma safety_property_1:
  "\<^bold>{0 \<le> h \<and> v\<^sup>2 \<le> 2*g*(H - h)\<^bold>}BBall\<^bold>{0 \<le> h \<and> h \<le> H\<^bold>}"
  apply (rule hoare_conseq[OF l3]) \<comment> \<open> Consequence rule \<close>
  apply (simp)
  apply (expr_simp)
  apply (smt g_pos zero_le_mult_iff zero_le_power2)
  done

text \<open> A more specific version -- the ball starts stationary and at height $h$. \<close>

lemma safety_property_2:
  "\<^bold>{h = H \<and> v = 0\<^bold>}BBall\<^bold>{0 \<le> h \<and> h \<le> H\<^bold>}"
  apply (rule hoare_conseq[OF safety_property_1])
  apply (simp add: H_pos)
  apply simp
  done

end

end