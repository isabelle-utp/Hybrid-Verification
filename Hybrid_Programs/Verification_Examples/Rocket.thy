section \<open> Rocket \<close>

theory Rocket
  imports "Hybrid-Verification.Hybrid_Verification"
begin

lemma rocket_arith:
  assumes "(k::real) > 1" and "m\<^sub>0 > k" and "x \<in> {0..}"
  shows "- k*(x\<^sup>3)/6 + m\<^sub>0*(x\<^sup>2)/2 \<le> 2*(m\<^sub>0\<^sup>3)/(3*(k\<^sup>2))" (is "?lhs \<le> _")
proof-
  let ?f = "\<lambda>t. -k*t\<^sup>3/6 + m\<^sub>0*t\<^sup>2/2" 
    and ?f' = "\<lambda>t. -k*t\<^sup>2/2 + m\<^sub>0*t"
    and ?f'' = "\<lambda>t. -k*t + m\<^sub>0"
  have "2*m\<^sub>0\<^sup>3/(3*k\<^sup>2) = -k*(2*m\<^sub>0/k)\<^sup>3/6 + m\<^sub>0*(2*m\<^sub>0/k)\<^sup>2/2" (is "_ = ?rhs")
    by (auto simp: field_simps power3_eq_cube)
  moreover have "?lhs \<le> ?rhs"
  proof(cases "x \<le> 2 * m\<^sub>0 / k")
    case True
    have ge_0_left: "0 \<le> y \<Longrightarrow> y \<le> m\<^sub>0/k \<Longrightarrow> ?f' 0 \<le> ?f' y" for y
      apply (rule has_vderiv_mono_test(1)[of "{0..m\<^sub>0/k}" ?f' ?f'' 0])
      using \<open>k > 1\<close> \<open>m\<^sub>0 > k\<close>
      by (auto intro!: vderiv_intros simp: field_simps)
    moreover have ge_0_right: "m\<^sub>0/k \<le> y \<Longrightarrow> y \<le> 2*m\<^sub>0/k \<Longrightarrow> ?f' (2*m\<^sub>0/k) \<le> ?f' y" for y
      apply(rule has_vderiv_mono_test(2)[of "{m\<^sub>0/k..2*m\<^sub>0/k}" ?f' ?f'' _ "2*m\<^sub>0/k"])
      using \<open>k > 1\<close> \<open>m\<^sub>0 > k\<close>
      by (auto intro!: vderiv_intros simp: field_simps)
    ultimately have ge_0: "\<forall>y\<in>{0..2*m\<^sub>0/k}. 0 \<le> ?f' y"
      using \<open>k > 1\<close> \<open>m\<^sub>0 > k\<close>
      by (fastforce simp: field_simps)
    show ?thesis
      apply (rule has_vderiv_mono_test(1)[of "{0..2*m\<^sub>0/k}" ?f ?f' _ "2*m\<^sub>0/k"])
      using ge_0 True \<open>x \<in> {0..}\<close> \<open>k > 1\<close> \<open>m\<^sub>0 > k\<close>
      by (auto intro!: vderiv_intros simp: field_simps)
  next
    case False
    have "2*m\<^sub>0/k \<le> y \<Longrightarrow> ?f' y \<le> ?f' (2*m\<^sub>0/k)" for y
      apply (rule has_vderiv_mono_test(2)[of "{m\<^sub>0/k..}" ?f' ?f''])
      using \<open>k > 1\<close> \<open>m\<^sub>0 > k\<close> by (auto intro!: vderiv_intros simp: field_simps)
    hence obs: "\<forall>y\<in>{2*m\<^sub>0/k..}. ?f' y \<le> 0"
      using \<open>k > 1\<close> \<open>m\<^sub>0 > k\<close>
      by (clarsimp simp: field_simps)
    show ?thesis
      apply (rule has_vderiv_mono_test(2)[of "{2*m\<^sub>0/k..}" ?f ?f'])
      using False \<open>k > 1\<close> obs
      by (auto intro!: vderiv_intros simp: field_simps)
  qed
  ultimately show ?thesis
    by simp
qed

dataspace rocket = 
  constants k :: real
  assumes k_ge_1: "k > 1" 
  variables v :: real y :: real m :: real t :: real

context rocket
begin

abbreviation "ode \<equiv> {y` = v, v` = m, t` = 1, m` = - k | (t \<ge> 0)}"

abbreviation "flow \<tau> \<equiv> 
  [y \<leadsto> -k*\<tau>\<^sup>3/6 + m*\<tau>\<^sup>2/2 + v *\<tau> + y, 
  v \<leadsto> -k*\<tau>\<^sup>2/2 + m*\<tau> + v, 
  t \<leadsto> \<tau> + t, 
  m \<leadsto> -k*\<tau> + m]"

(* m' = - k
\<Longrightarrow> m = - k * t + m\<^sub>0 is a line s.t. m = 0 \<longleftrightarrow> t = m\<^sub>0/k
\<Longrightarrow> v = - k * t\<^sup>2/2 + m\<^sub>0 * t = t * (- k * t/2 + m\<^sub>0)
  s.t. v = 0 \<longleftrightarrow> t = 0 \<or> t = 2*m\<^sub>0/k
\<Longrightarrow> y = - k * t\<^sup>3/6 + m\<^sub>0 * t\<^sup>2/2 = (t\<^sup>2 / 2) * (-k*t/3 + m\<^sub>0)
  s.t. y = 0 \<longleftrightarrow> t = 0 \<or> t = 3*m\<^sub>0/k
\<Longrightarrow> (v' = m = 0 \<Longrightarrow> t = m\<^sub>0/k \<Longrightarrow> v = m\<^sub>0\<^sup>2/k - m\<^sub>0\<^sup>2/(2*k) = m\<^sub>0\<^sup>2/(2*k))
  \<and> (y' = v = 0 \<Longrightarrow> t = 0 \<or> t = 2*m\<^sub>0/k \<Longrightarrow> y = (2*m\<^sub>0\<^sup>2/k\<^sup>2) * (m\<^sub>0/3) = 2*m\<^sub>0\<^sup>3/(3*k\<^sup>2)
\<Longrightarrow> v is a concave down parabola with maximum at t=m\<^sub>0/k and v=m\<^sub>0\<^sup>2/(2*k)
  and y is a mostly decreasing cubic line with critical points 
  at t=0 with y=0 and t=2*m\<^sub>0/k with max at t=2*m\<^sub>0/k and y=2*m\<^sub>0\<^sup>3/(3*k\<^sup>2) *)

lemma local_flow_on_rocket:
  "local_flow_on [y \<leadsto> $v, v \<leadsto> $m, t \<leadsto> 1, m \<leadsto> - k] (y +\<^sub>L v +\<^sub>L t +\<^sub>L m) UNIV UNIV flow"
  by local_flow_on_auto

lemma "(m = m\<^sub>0 \<and> m\<^sub>0 > k \<and> t = 0 \<and> v = 0 \<and> y = 0)\<^sub>e \<le> |ode] (y \<le> 2*m\<^sub>0\<^sup>3/(3*k\<^sup>2))"
  apply (wlp_solve "flow")
  using k_ge_1 rocket_arith
  by (expr_simp add: le_fun_def)

lemma "(0 \<le> h \<and> h < 2*m\<^sub>0\<^sup>3/(3*k\<^sup>2) \<and> m = m\<^sub>0 \<and> m\<^sub>0 > k \<and> t = 0 \<and> v = 0 \<and> y = 0)\<^sub>e \<le> |ode\<rangle> (y \<ge> h)"
  using k_ge_1
  by (subst fdia_g_ode_frame_flow[OF local_flow_on_rocket]; expr_simp)
    (auto simp: field_simps power3_eq_cube intro!: exI[of _ "2*m\<^sub>0/k"])

end