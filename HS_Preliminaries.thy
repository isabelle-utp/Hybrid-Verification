(*  Title:       Preliminaries for hybrid systems verification
    Maintainer:  Jonathan Julián Huerta y Munive <jonjulian23@gmail.com>
*)

section \<open> Hybrid Systems Preliminaries \<close>

text \<open>Hybrid systems combine continuous dynamics with discrete control. This section contains
auxiliary lemmas for verification of hybrid systems.\<close>

theory HS_Preliminaries
  imports 
    "Ordinary_Differential_Equations.Picard_Lindeloef_Qualitative" 
    "Hybrid-Library.Matrix_Syntax"
begin

\<comment> \<open> Notation \<close>

bundle derivative_notation
begin

no_notation has_vderiv_on (infix "(has'_vderiv'_on)" 50)

notation has_derivative ("(1(D _ \<mapsto> (_))/ _)" [65,65] 61)
     and has_vderiv_on ("(1 D _ = (_)/ on _)" [65,65] 61)

end

bundle derivative_no_notation
begin

notation has_vderiv_on (infix "(has'_vderiv'_on)" 50)

no_notation has_derivative ("(1(D _ \<mapsto> (_))/ _)" [65,65] 61)
     and has_vderiv_on ("(1 D _ = (_)/ on _)" [65,65] 61)

end

text \<open>Special syntax for cubes, power to the 4th and 5th. \<close>
abbreviation power3 :: "'a::power \<Rightarrow> 'a"  ("(_\<^sup>3)" [1000] 999)
  where "x\<^sup>3 \<equiv> x ^ 3"

abbreviation power4 :: "'a::power \<Rightarrow> 'a"  ("(_\<^sup>4)" [1000] 999)
  where "x\<^sup>4 \<equiv> x ^ 4"

abbreviation power5 :: "'a::power \<Rightarrow> 'a"  ("(_\<^sup>5)" [1000] 999)
  where "x\<^sup>5 \<equiv> x ^ 5"

bundle power_notation
begin

notation power2 ("(_\<^sup>2)" [1000] 999)
  and power3 ("(_\<^sup>3)" [1000] 999) 
  and power4 ("(_\<^sup>4)" [1000] 999)
  and power5 ("(_\<^sup>5)" [1000] 999)

end

bundle power_no_notation
begin

no_notation power2 ("(_\<^sup>2)" [1000] 999)
  and power3 ("(_\<^sup>3)" [1000] 999) 
  and power4 ("(_\<^sup>4)" [1000] 999)
  and power5 ("(_\<^sup>5)" [1000] 999)

end

unbundle power_no_notation
unbundle derivative_notation
unbundle power_notation \<comment> \<open> enable notation \<close>

lemma nat_wf_induct[case_names zero induct]: 
  assumes "P 0"
    and "(\<And>n. (\<And>m. m \<le> n \<Longrightarrow> P m) \<Longrightarrow> P (Suc n))"
  shows "P n"
  using assms
  apply (induct n rule: full_nat_induct)
  by simp (metis Suc_le_mono not0_implies_Suc)


subsection \<open> Real vector arithmetic \<close>

definition vec_upd :: "('a^'b) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'a^'b"
  where "vec_upd s i a = (\<chi> j. ((($) s)(i := a)) j)"

lemma vec_upd_eq: "vec_upd s i a = (\<chi> j. if j = i then a else s$j)"
  by (simp add: vec_upd_def)

lemma nonneg_real_within_Suc: "r \<ge> 0 \<Longrightarrow> \<exists>n. Suc n > r \<and> r \<ge> n" for r::real
  by (metis Groups.add_ac(2) Suc_n_not_le_n Suc_neq_Zero
      less_add_one less_le_not_le linorder_le_cases linorder_not_less 
      nat.inject nat_ceiling_le_eq of_nat_0_less_iff of_nat_Suc
      old.nat.exhaust order_less_le_trans real_nat_ceiling_ge)

lemma pos_real_within_Suc: "r > 0 \<Longrightarrow> \<exists>n. Suc n \<ge> r \<and> r > n" for r::real
  by (metis gr0_implies_Suc lessI of_nat_0_less_iff of_nat_less_iff 
      order_le_less nonneg_real_within_Suc)

lemma abs_le_eq:
  shows "(r::real) > 0 \<Longrightarrow> (\<bar>x\<bar> < r) = (-r < x \<and> x < r)"
    and "(r::real) > 0 \<Longrightarrow> (\<bar>x\<bar> \<le> r) = (-r \<le> x \<and> x \<le> r)"
  by linarith+

lemma real_ivl_eqs:
  assumes "0 < r"
  shows "ball x r = {x-r<--< x+r}"         and "{x-r<--< x+r} = {x-r<..< x+r}"
    and "ball (r / 2) (r / 2) = {0<--<r}"  and "{0<--<r} = {0<..<r}"
    and "ball 0 r = {-r<--<r}"             and "{-r<--<r} = {-r<..<r}"
    and "cball x r = {x-r--x+r}"           and "{x-r--x+r} = {x-r..x+r}"
    and "cball (r / 2) (r / 2) = {0--r}"   and "{0--r} = {0..r}"
    and "cball 0 r = {-r--r}"              and "{-r--r} = {-r..r}"
  unfolding open_segment_eq_real_ivl closed_segment_eq_real_ivl
  using assms by (auto simp: cball_def ball_def dist_norm field_simps)

lemma is_interval_real_nonneg[simp]: "is_interval (Collect ((\<le>) (0::real)))"
  by (auto simp: is_interval_def)

lemma open_real_segment: "open {a<--<b}" for a::real
  unfolding open_segment_eq_real_ivl by auto

lemma norm_rotate_eq[simp]:
  fixes x :: "'a:: {banach,real_normed_field}"
  shows "(x * cos t - y * sin t)\<^sup>2 + (x * sin t + y * cos t)\<^sup>2 = x\<^sup>2 + y\<^sup>2"
    and "(x * cos t + y * sin t)\<^sup>2 + (y * cos t - x * sin t)\<^sup>2 = x\<^sup>2 + y\<^sup>2"
proof-
  have "(x * cos t - y * sin t)\<^sup>2 = x\<^sup>2 * (cos t)\<^sup>2 + y\<^sup>2 * (sin t)\<^sup>2 - 2 * (x * cos t) * (y * sin t)"
    by(simp add: power2_diff power_mult_distrib)
  also have "(x * sin t + y * cos t)\<^sup>2 = y\<^sup>2 * (cos t)\<^sup>2 + x\<^sup>2 * (sin t)\<^sup>2 + 2 * (x * cos t) * (y * sin t)"
    by(simp add: power2_sum power_mult_distrib)
  ultimately show "(x * cos t - y * sin t)\<^sup>2 + (x * sin t + y * cos t)\<^sup>2 = x\<^sup>2 + y\<^sup>2"
    by (simp add: Groups.mult_ac(2) Groups.mult_ac(3) right_diff_distrib sin_squared_eq)
  thus "(x * cos t + y * sin t)\<^sup>2 + (y * cos t - x * sin t)\<^sup>2 = x\<^sup>2 + y\<^sup>2"
    by (simp add: add.commute add.left_commute power2_diff power2_sum)
qed

lemma sum_eq_Sum:
  assumes "inj_on f A"
  shows "(\<Sum>x\<in>A. f x) = (\<Sum> {f x |x. x \<in> A})"
proof-
  have "(\<Sum> {f x |x. x \<in> A}) = (\<Sum> (f ` A))"
    apply(auto simp: image_def)
    by (rule_tac f=Sum in arg_cong, auto)
  also have "... = (\<Sum>x\<in>A. f x)"
    by (subst sum.image_eq[OF assms], simp)
  finally show "(\<Sum>x\<in>A. f x) = (\<Sum> {f x |x. x \<in> A})"
    by simp
qed

lemma triangle_norm_vec_le_sum: "\<parallel>x\<parallel> \<le> (\<Sum>i\<in>UNIV. \<parallel>x $ i\<parallel>)"
  by (simp add: L2_set_le_sum norm_vec_def)


subsection \<open> Single variable derivatives \<close>

named_theorems poly_derivatives "compilation of optimised miscellaneous derivative rules."

declare has_vderiv_on_const [poly_derivatives]
    and has_vderiv_on_id [poly_derivatives]
    and has_vderiv_on_add[THEN has_vderiv_on_eq_rhs, poly_derivatives]
    and has_vderiv_on_diff[THEN has_vderiv_on_eq_rhs, poly_derivatives]
    and has_vderiv_on_mult[THEN has_vderiv_on_eq_rhs, poly_derivatives]
    and has_vderiv_on_scaleR[THEN has_vderiv_on_eq_rhs, poly_derivatives]
    and has_vderiv_on_ln[poly_derivatives]

lemma has_vderiv_Pair: 
  "\<lbrakk> D f = f' on T; D g = g' on T \<rbrakk> \<Longrightarrow> D (\<lambda>x. (f x, g x)) = (\<lambda> x. (f' x, g' x)) on T"
  by (auto intro: has_vector_derivative_Pair simp add: has_vderiv_on_def)

lemma vderiv_on_composeI:
  assumes "D f = f' on g ` T" 
    and " D g = g' on T"
    and "h = (\<lambda>t. g' t *\<^sub>R f' (g t))"
  shows "D (\<lambda>t. f (g t)) = h on T"
  apply(subst ssubst[of h], simp)
  using assms has_vderiv_on_compose by auto

lemma vderiv_uminusI[poly_derivatives]:
  "D f = f' on T \<Longrightarrow> g = (\<lambda>t. - f' t) \<Longrightarrow> D (\<lambda>t. - f t) = g on T"
  using has_vderiv_on_uminus by auto

lemma vderiv_npowI[poly_derivatives]:
  fixes f::"real \<Rightarrow> real"
  assumes "n \<ge> 1" and "D f = f' on T" and "g = (\<lambda>t. n * (f' t) * (f t)^(n-1))"
  shows "D (\<lambda>t. (f t)^n) = g on T"
  using assms unfolding has_vderiv_on_def has_vector_derivative_def 
  by (auto intro: derivative_eq_intros simp: field_simps)

lemma vderiv_divI[poly_derivatives]:
  assumes "\<forall>t\<in>T. g t \<noteq> (0::real)" and "D f = f' on T"and "D g = g' on T" 
    and "h = (\<lambda>t. (f' t * g t - f t * (g' t)) / (g t)^2)"
  shows "D (\<lambda>t. (f t)/(g t)) = h on T"
  apply(subgoal_tac "(\<lambda>t. (f t)/(g t)) = (\<lambda>t. (f t) * (1/(g t)))")
   apply(erule ssubst, rule poly_derivatives(5)[OF assms(2)])
  apply(rule vderiv_on_composeI[where g=g and f="\<lambda>t. 1/t" and f'="\<lambda>t. - 1/t^2", OF _ assms(3)])
  apply(subst has_vderiv_on_def, subst has_vector_derivative_def, clarsimp)
  using assms(1) apply(force intro!: derivative_eq_intros simp: fun_eq_iff power2_eq_square)
  using assms by (auto simp: field_simps)

lemma vderiv_cosI[poly_derivatives]:
  assumes "D (f::real \<Rightarrow> real) = f' on T" and "g = (\<lambda>t. - (f' t) * sin (f t))"
  shows "D (\<lambda>t. cos (f t)) = g on T"
  apply(rule vderiv_on_composeI[OF _ assms(1), of "\<lambda>t. cos t"])
  unfolding has_vderiv_on_def has_vector_derivative_def 
  by (auto intro!: derivative_eq_intros simp: assms)

lemma vderiv_sinI[poly_derivatives]:
  assumes "D (f::real \<Rightarrow> real) = f' on T" and "g = (\<lambda>t. (f' t) * cos (f t))"
  shows "D (\<lambda>t. sin (f t)) = g on T"
  apply(rule vderiv_on_composeI[OF _ assms(1), of "\<lambda>t. sin t"])
  unfolding has_vderiv_on_def has_vector_derivative_def 
  by (auto intro!: derivative_eq_intros simp: assms)

lemma vderiv_expI[poly_derivatives]:
  assumes "D (f::real \<Rightarrow> real) = f' on T" and "g = (\<lambda>t. (f' t) * exp (f t))"
  shows "D (\<lambda>t. exp (f t)) = g on T"
  apply(rule vderiv_on_composeI[OF _ assms(1), of "\<lambda>t. exp t"])
  unfolding has_vderiv_on_def has_vector_derivative_def 
  by (auto intro!: derivative_eq_intros simp: assms)

lemma vderiv_on_proj:
  assumes "D X = X' on T " and "X' = (\<lambda>t. (X\<^sub>1' t, X\<^sub>2' t))"
  shows has_vderiv_on_fst: "D (\<lambda>t. fst (X t)) = (\<lambda>t. X\<^sub>1' t) on T"
    and has_vderiv_on_snd: "D (\<lambda>t. snd (X t)) = (\<lambda>t. X\<^sub>2' t) on T"
  using assms unfolding has_vderiv_on_def comp_def[symmetric] apply safe
   apply(rule has_vector_derivative_fst', force)
  by (rule has_vector_derivative_snd'', force)

lemma vderiv_on_fst [poly_derivatives]:
  assumes "D X = X' on T " and "g = (\<lambda>t. fst (X' t))"
  shows "D (\<lambda>t. fst (X t)) = g on T"
  using assms unfolding has_vderiv_on_def comp_def[symmetric] apply safe
  subgoal for x by (rule_tac has_vector_derivative_fst'[of _ _ "(snd \<circ> X') x"], force)
  done

lemma vderiv_on_snd [poly_derivatives]:
  assumes "D X = X' on T " and "g = (\<lambda>t. snd (X' t))"
  shows "D (\<lambda>t. snd (X t)) = g on T"
  using assms unfolding has_vderiv_on_def comp_def[symmetric] apply safe
  subgoal for x by (rule_tac has_vector_derivative_snd''[of _ "(fst \<circ> X') x"], force)
  done

lemma vderiv_pairI[poly_derivatives]:
  assumes "D f1 = f1' on T" 
    and "D f2 = f2' on T"
    and "g = (\<lambda>t. (f1' t, f2' t))"
  shows "D (\<lambda>t. (f1 t, f2 t)) = g on T"
  apply(subst assms(3))
  using assms(1,2) unfolding has_vderiv_on_def has_vector_derivative_def
  apply (clarsimp simp: scaleR_vec_def)
  by (rule has_derivative_Pair, auto)

lemma has_vderiv_on_divideR: "\<forall>t\<in>T. g t \<noteq> (0::real) \<Longrightarrow> D f = f' on T \<Longrightarrow>  D g = g' on T 
  \<Longrightarrow> D (\<lambda>t. f t /\<^sub>R g t) = (\<lambda>t. (f' t *\<^sub>R g t - f t *\<^sub>R (g' t)) /\<^sub>R (g t)^2) on T"
  unfolding  has_vderiv_on_def has_vector_derivative_def
  by (auto simp: fun_eq_iff field_simps  intro!: derivative_eq_intros)

lemmas has_vderiv_on_divideR[THEN has_vderiv_on_eq_rhs, poly_derivatives]
thm has_vderiv_on_scaleR
thm has_vderiv_on_scaleR[THEN has_vderiv_on_eq_rhs] has_vderiv_on_mult[THEN has_vderiv_on_eq_rhs]
thm derivative_intros(33,39,45,46,50,60)

lemma vderiv_on_exp_scaleRlI:
  assumes "D f = f' on T" and "g' = (\<lambda>x. f' x *\<^sub>R exp (f x *\<^sub>R A) * A)"
  shows "D (\<lambda>x. exp (f x *\<^sub>R A)) = g' on T"
  using assms unfolding has_vderiv_on_def has_vector_derivative_def apply clarsimp
  by (rule exp_scaleR_has_derivative_right, auto simp: fun_eq_iff)

\<comment> \<open>Examples for checking derivatives\<close>

lemma "D (*) a = (\<lambda>t. a) on T"
  by (auto intro!: poly_derivatives)

lemma "a \<noteq> 0 \<Longrightarrow> D (\<lambda>t. t/a) = (\<lambda>t. 1/a) on T"
  by (auto intro!: poly_derivatives simp: power2_eq_square)

lemma "(a::real) \<noteq> 0 \<Longrightarrow> D f = f' on T \<Longrightarrow> g = (\<lambda>t. (f' t)/a) \<Longrightarrow> D (\<lambda>t. (f t)/a) = g on T"
  by (auto intro!: poly_derivatives simp: power2_eq_square)

lemma "\<forall>t\<in>T. f t \<noteq> (0::real) \<Longrightarrow> D f = f' on T \<Longrightarrow> g = (\<lambda>t. - a * f' t / (f t)^2) \<Longrightarrow> 
  D (\<lambda>t. a/(f t)) = g on T"
  by (auto intro!: poly_derivatives simp: power2_eq_square)

lemma "D (\<lambda>t. a * t\<^sup>2 / 2 + v * t + x) = (\<lambda>t. a * t + v) on T"
  by(auto intro!: poly_derivatives)

lemma "D (\<lambda>t. v * t - a * t\<^sup>2 / 2 + x) = (\<lambda>x. v - a * x) on T"
  by(auto intro!: poly_derivatives)

lemma "D x = x' on (\<lambda>\<tau>. \<tau> + t) ` T \<Longrightarrow> D (\<lambda>\<tau>. x (\<tau> + t)) = (\<lambda>\<tau>. x' (\<tau> + t)) on T"
  by (rule vderiv_on_composeI, auto intro: poly_derivatives)

lemma "a \<noteq> 0 \<Longrightarrow> D (\<lambda>t. t/a) = (\<lambda>t. 1/a) on T"
  by (auto intro!: poly_derivatives simp: power2_eq_square)

lemma "c \<noteq> 0 \<Longrightarrow> D (\<lambda>t. a5 * t^5 + a3 * (t^3 / c) - a2 * exp (t^2) + a1 * cos t + a0) = 
  (\<lambda>t. 5 * a5 * t^4 + 3 * a3 * (t^2 / c) - 2 * a2 * t * exp (t^2) - a1 * sin t) on T"
  by(auto intro!: poly_derivatives simp: power2_eq_square)

lemma "c \<noteq> 0 \<Longrightarrow> D (\<lambda>t. - a3 * exp (t^3 / c) + a1 * sin t + a2 * t^2) = 
  (\<lambda>t. a1 * cos t + 2 * a2 * t - 3 * a3 * t^2 / c * exp (t^3 / c)) on T"
  by(auto intro!: poly_derivatives simp: power2_eq_square)

lemma "c \<noteq> 0 \<Longrightarrow> D (\<lambda>t. exp (a * sin (cos (t^4) / c))) = 
  (\<lambda>t. - 4 * a * t^3 * sin (t^4) / c * cos (cos (t^4) / c) * exp (a * sin (cos (t^4) / c))) on T"
  by (intro poly_derivatives) (auto intro!: poly_derivatives simp: power2_eq_square)


subsection \<open> Intermediate Value Theorem \<close>

lemma IVT_two_functions:
  fixes f :: "('a::{linear_continuum_topology, real_vector}) \<Rightarrow> 
  ('b::{linorder_topology,real_normed_vector,ordered_ab_group_add})"
  assumes conts: "continuous_on {a..b} f" "continuous_on {a..b} g"
      and ahyp: "f a < g a" and bhyp: "g b < f b " and "a \<le> b"
    shows "\<exists>x\<in>{a..b}. f x = g x"
proof-
  let "?h x" = "f x - g x"
  have "?h a \<le> 0" and "?h b \<ge> 0"
    using ahyp bhyp by simp_all
  also have "continuous_on {a..b} ?h"
    using conts continuous_on_diff by blast 
  ultimately obtain x where "a \<le> x" "x \<le> b" and "?h x = 0"
    using IVT'[of "?h"] \<open>a \<le> b\<close> by blast
  thus ?thesis
    using \<open>a \<le> b\<close> by auto
qed

lemma IVT_two_functions_real_ivl:
  fixes f :: "real \<Rightarrow> real"
  assumes conts: "continuous_on {a--b} f" "continuous_on {a--b} g"
      and ahyp: "f a < g a" and bhyp: "g b < f b "
    shows "\<exists>x\<in>{a--b}. f x = g x"
proof(cases "a \<le> b")
  case True
  then show ?thesis 
    using IVT_two_functions assms 
    unfolding closed_segment_eq_real_ivl by auto
next
  case False
  hence "a \<ge> b"
    by auto
  hence "continuous_on {b..a} f" "continuous_on {b..a} g"
    using conts False unfolding closed_segment_eq_real_ivl by auto
  hence "\<exists>x\<in>{b..a}. g x = f x"
    using IVT_two_functions[of b a g f] assms(3,4) False by auto
  then show ?thesis  
    using \<open>a \<ge> b\<close> unfolding closed_segment_eq_real_ivl by auto force
qed

lemma mvt_ivl_general:
  fixes f :: "real \<Rightarrow> 'a::real_inner"
  assumes "a \<noteq> b" and "continuous_on {a--b} f"
    and "\<forall>x\<in>{a<--<b}. D f \<mapsto> (f' x) (at x)"
  shows "\<exists>x\<in>{a<--<b}. \<parallel>f b - f a\<parallel> \<le> \<parallel>f' x \<bar>b - a\<bar>\<parallel>"
proof(cases "a < b")
  case True
  thus ?thesis 
    using closed_segment_eq_real_ivl open_segment_eq_real_ivl
      assms mvt_general[of a b f] by force
next
  case False
  hence "b < a" "{a--b} = {b..a}" "{a<--<b} = {b<..<a}"
    using assms closed_segment_eq_real_ivl open_segment_eq_real_ivl by auto
  hence cont: "continuous_on {b..a} f" and "\<forall>x\<in>{b<..<a}. D f \<mapsto> (f' x) (at x)"
    using assms by auto
  hence "\<exists>x\<in>{b<..<a}. \<parallel>f b - f a\<parallel> \<le> \<parallel>f' x \<bar>a - b\<bar>\<parallel>"
    using mvt_general[OF \<open>b < a\<close> cont, of f'] 
    by (auto simp: Real_Vector_Spaces.real_normed_vector_class.norm_minus_commute)
  thus ?thesis 
    by (subst \<open>{a<--<b} = {b<..<a}\<close>) auto
qed


subsection \<open> Filters \<close>

lemma eventually_at_within_mono:
  assumes "t \<in> interior T" and "T \<subseteq> S"
    and "eventually P (at t within T)"
  shows "eventually P (at t within S)"
  by (meson assms eventually_within_interior interior_mono subsetD)

lemma netlimit_at_within_mono:
  fixes t::"'a::{perfect_space,t2_space}"
  assumes "t \<in> interior T" and "T \<subseteq> S"
  shows "netlimit (at t within S) = t"
  using assms(1) interior_mono[OF \<open>T \<subseteq> S\<close>] netlimit_within_interior by auto

lemma has_derivative_at_within_mono:
  fixes t::"'a::{perfect_space,t2_space,real_normed_vector}"
  assumes "t \<in> interior T" and "T \<subseteq> S"
    and "D f \<mapsto> f' at t within T"
  shows "D f \<mapsto> f' at t within S"
  using assms(3) apply(unfold has_derivative_def tendsto_iff, safe)
  unfolding netlimit_at_within_mono[OF assms(1,2)] netlimit_within_interior[OF assms(1)]
  by (rule eventually_at_within_mono[OF assms(1,2)]) simp

lemma eventually_all_finite2:
  fixes P :: "('a::finite) \<Rightarrow> 'b \<Rightarrow> bool"
  assumes h:"\<forall>i. eventually (P i) F"
  shows "eventually (\<lambda>x. \<forall>i. P i x) F"
proof(unfold eventually_def)
  let ?F = "Rep_filter F"
  have obs: "\<forall>i. ?F (P i)"
    using h by auto
  have "?F (\<lambda>x. \<forall>i \<in> UNIV. P i x)"
    apply(rule finite_induct)
    by(auto intro: eventually_conj simp: obs h)
  thus "?F (\<lambda>x. \<forall>i. P i x)"
    by simp
qed

lemma eventually_all_finite_mono:
  fixes P :: "('a::finite) \<Rightarrow> 'b \<Rightarrow> bool"
  assumes h1: "\<forall>i. eventually (P i) F"
      and h2: "\<forall>x. (\<forall>i. (P i x)) \<longrightarrow> Q x"
  shows "eventually Q F"
proof-
  have "eventually (\<lambda>x. \<forall>i. P i x) F"
    using h1 eventually_all_finite2 by blast
  thus "eventually Q F"
    unfolding eventually_def
    using h2 eventually_mono by auto
qed


subsection \<open> Multivariable derivatives \<close>

lemma has_derivative_vec_nth[derivative_intros]: 
  "D (\<lambda>s. s $ i) \<mapsto> (\<lambda>s. s $ i) (at x within S)"
  by (clarsimp simp: has_derivative_within) standard

lemma bounded_linear_coordinate:
  "(bounded_linear f) \<longleftrightarrow> (\<forall>i. bounded_linear (\<lambda>x. (f x) $ i))" (is "?lhs = ?rhs")
proof
  assume ?lhs 
  thus ?rhs
    apply(clarsimp, rule_tac f="(\<lambda>x. x $ i)" in bounded_linear_compose)
     apply(simp_all add: bounded_linear_def bounded_linear_axioms_def linear_iff)
    by (rule_tac x=1 in exI, clarsimp) (meson Finite_Cartesian_Product.norm_nth_le)
next
  assume ?rhs
  hence "(\<forall>i. \<exists>K. \<forall>x. \<parallel>f x $ i\<parallel> \<le> \<parallel>x\<parallel> * K)" "linear f"
    by (auto simp: bounded_linear_def bounded_linear_axioms_def linear_iff vec_eq_iff)
  then obtain F where F: "\<And>i x. \<parallel>f x $ i\<parallel> \<le> \<parallel>x\<parallel> * F i"
    by metis
  have "\<parallel>f x\<parallel> \<le> \<parallel>x\<parallel> * sum F UNIV" for x
  proof -
    have "norm (f x) \<le> (\<Sum>i\<in>UNIV. \<parallel>f x $ i\<parallel>)"
      by (simp add: L2_set_le_sum norm_vec_def)
    also have "... \<le> (\<Sum>i\<in>UNIV. norm x * F i)"
      by (metis F sum_mono)
    also have "... = norm x * sum F UNIV"
      by (simp add: sum_distrib_left)
    finally show ?thesis .
  qed
  then show ?lhs
    by (force simp: bounded_linear_def bounded_linear_axioms_def \<open>linear f\<close>)
qed

lemma open_preimage_nth:
  "open S \<Longrightarrow> open {s::('a::real_normed_vector^'n::finite). s $ i \<in> S}"
  unfolding open_contains_ball apply clarsimp
  apply(erule_tac x="x$i" in ballE; clarsimp)
  apply(rule_tac x=e in exI; clarsimp simp: dist_norm subset_eq ball_def)
  apply(rename_tac x e y, erule_tac x="y$i" in allE)
  using Finite_Cartesian_Product.norm_nth_le
  by (metis le_less_trans vector_minus_component)

lemma tendsto_nth_iff:
  fixes l::"'a::real_normed_vector^'n::finite"
  defines "m \<equiv> real CARD('n)"
  shows "(f \<longlongrightarrow> l) F \<longleftrightarrow> (\<forall>i. ((\<lambda>x. f x $ i) \<longlongrightarrow> l $ i) F)" (is "?lhs = ?rhs")
proof
  assume ?lhs
  thus ?rhs
    unfolding tendsto_def
    by (clarify, drule_tac x="{s. s $ i \<in> S}" in spec) (auto simp: open_preimage_nth)
next
  assume ?rhs
  thus ?lhs
  proof(unfold tendsto_iff dist_norm, clarify)
    fix \<epsilon>::real assume "0 < \<epsilon>"
    assume evnt_h: "\<forall>i \<epsilon>. 0 < \<epsilon> \<longrightarrow> (\<forall>\<^sub>F x in F. \<parallel>f x $ i - l $ i\<parallel> < \<epsilon>)"
    {fix x assume hyp: "\<forall>i. \<parallel>f x $ i - l $ i\<parallel> < (\<epsilon>/m)"
      have "\<parallel>f x - l\<parallel> \<le> (\<Sum>i\<in>UNIV. \<parallel>f x $ i - l $ i\<parallel>)"
        using triangle_norm_vec_le_sum[of "f x - l"] by auto
      also have "... < (\<Sum>(i::'n)\<in>UNIV. (\<epsilon>/m))"
        apply(rule sum_strict_mono[of UNIV "\<lambda>i. \<parallel>f x $ i - l $ i\<parallel>" "\<lambda>i. \<epsilon>/m"])
        using hyp by auto
      also have "... = m * (\<epsilon>/m)"
        unfolding assms by simp
      finally have "\<parallel>f x - l\<parallel> < \<epsilon>" 
        unfolding assms by simp}
    hence key: "\<And>x. \<forall>i. \<parallel>f x $ i - l $ i\<parallel> < (\<epsilon>/m) \<Longrightarrow> \<parallel>f x - l\<parallel> < \<epsilon>"
      by blast
    have obs: "\<forall>\<^sub>F x in F. \<forall>i. \<parallel>f x $ i - l $ i\<parallel> < (\<epsilon>/m)"
      apply(rule eventually_all_finite)
      using \<open>0 < \<epsilon>\<close> evnt_h unfolding assms by auto
    thus "\<forall>\<^sub>F x in F. \<parallel>f x - l\<parallel> < \<epsilon>"
      by (rule eventually_mono[OF _ key], simp)
  qed
qed

lemma has_derivative_coordinate[simp]:
  "(D f \<mapsto> f' at x within S) \<longleftrightarrow> (\<forall>i. D (\<lambda>s. f s $ i) \<mapsto> (\<lambda>s. f' s $ i) at x within S)"
  by (simp add: has_derivative_within tendsto_nth_iff 
      bounded_linear_coordinate all_conj_distrib)

lemma has_vderiv_on_component[simp]:
  fixes x::"real \<Rightarrow> ('a::banach)^('n::finite)"
  shows "(D x = x' on T) = (\<forall>i. D (\<lambda>t. x t $ i) = (\<lambda>t. x' t $ i) on T)"
  unfolding has_vderiv_on_def has_vector_derivative_def by auto

lemma has_derivative_at_within_iff: "(D f \<mapsto> f' (at x within S)) \<longleftrightarrow> bounded_linear f' \<and> 
  (\<forall>X. open X \<longrightarrow> 0 \<in> X \<longrightarrow> (\<exists>d>0. \<forall>s\<in>S. s \<noteq> x \<and> \<parallel>s - x\<parallel> < d \<longrightarrow> (f s - f x - f' (s - x)) /\<^sub>R \<parallel>s - x\<parallel> \<in> X))"
  unfolding has_derivative_at_within tendsto_def eventually_at dist_norm by simp

lemma has_vderiv_on_iff: 
  "(D f = f' on T) \<longleftrightarrow> (\<forall>x\<in>T. D f \<mapsto> (\<lambda>h. h *\<^sub>R f' x) (at x within T))"
  unfolding has_vderiv_on_def has_vector_derivative_def by simp

(***************** PREVIOUS RESULTS GENERALISED ABOVE **************)

lemma frechet_tendsto_vec_lambda:
  fixes f::"real \<Rightarrow> ('a::banach)^('m::finite)" and x::real and T::"real set"
  defines "x\<^sub>0 \<equiv> netlimit (at x within T)" and "m \<equiv> real CARD('m)"
  assumes "\<forall>i. ((\<lambda>y. (f y $ i - f x\<^sub>0 $ i - (y - x\<^sub>0) *\<^sub>R f' x $ i) /\<^sub>R (\<parallel>y - x\<^sub>0\<parallel>)) \<longlongrightarrow> 0) (at x within T)"
  shows "((\<lambda>y. (f y - f x\<^sub>0 - (y - x\<^sub>0) *\<^sub>R f' x) /\<^sub>R (\<parallel>y - x\<^sub>0\<parallel>)) \<longlongrightarrow> 0) (at x within T)"
  apply(subst tendsto_nth_iff)
  using assms by auto

lemma tendsto_norm_bound:
  "\<forall>x. \<parallel>G x - L\<parallel> \<le> \<parallel>F x - L\<parallel> \<Longrightarrow> (F \<longlongrightarrow> L) net \<Longrightarrow> (G \<longlongrightarrow> L) net"
  apply(unfold tendsto_iff dist_norm, clarsimp)
  apply(rule_tac P="\<lambda>x. \<parallel>F x - L\<parallel> < e" in eventually_mono, simp)
  by (rename_tac e z) (erule_tac x=z in allE, simp)

lemma tendsto_zero_norm_bound:
  "\<forall>x. \<parallel>G x\<parallel> \<le> \<parallel>F x\<parallel> \<Longrightarrow> (F \<longlongrightarrow> 0) net \<Longrightarrow> (G \<longlongrightarrow> 0) net"
  apply(unfold tendsto_iff dist_norm, clarsimp)
  apply(rule_tac P="\<lambda>x. \<parallel>F x\<parallel> < e" in eventually_mono, simp)
  by (rename_tac e z) (erule_tac x=z in allE, simp)

lemma frechet_tendsto_vec_nth:
  fixes f::"real \<Rightarrow> ('a::real_normed_vector)^'m"
  assumes "((\<lambda>x. (f x - f x\<^sub>0 - (x - x\<^sub>0) *\<^sub>R f' t) /\<^sub>R (\<parallel>x - x\<^sub>0\<parallel>)) \<longlongrightarrow> 0) (at t within T)"
  shows "((\<lambda>x. (f x $ i - f x\<^sub>0 $ i - (x - x\<^sub>0) *\<^sub>R f' t $ i) /\<^sub>R (\<parallel>x - x\<^sub>0\<parallel>)) \<longlongrightarrow> 0) (at t within T)"
  apply(rule_tac F="(\<lambda>x. (f x - f x\<^sub>0 - (x - x\<^sub>0) *\<^sub>R f' t) /\<^sub>R (\<parallel>x - x\<^sub>0\<parallel>))" in tendsto_zero_norm_bound)
   apply(clarsimp, rule mult_left_mono)
    apply (metis Finite_Cartesian_Product.norm_nth_le vector_minus_component vector_scaleR_component)
  using assms by simp_all

lemma has_derivative_vec_lambda_old:
  fixes f::"real \<Rightarrow> ('a::banach)^('n::finite)"
  assumes "\<forall>i. D (\<lambda>t. f t $ i) \<mapsto> (\<lambda> h. h *\<^sub>R f' x $ i) (at x within T)"
  shows "D f \<mapsto> (\<lambda>h. h *\<^sub>R f' x) at x within T"
  apply(subst has_derivative_coordinate)
  using assms by auto

lemma has_derivative_vec_nth_old:
  assumes "D f \<mapsto> (\<lambda>h. h *\<^sub>R f' x) at x within T"
  shows "D (\<lambda>t. f t $ i) \<mapsto> (\<lambda>h. h *\<^sub>R f' x $ i) at x within T"
  using  assms 
  by (subst (asm) has_derivative_coordinate, simp)


subsection \<open> Differentiability implies Lipschitz \<close>

(********************************************************************************)
\<comment> \<open> Useful to remember these theorems \<close>
thm filter_eq_iff eventually_at eventually_at_topological \<comment> \<open> filters \<close>
thm at_within_open at_within_open_subset at_within_Icc_at \<comment> \<open> at within \<close>
thm has_derivative_at_within Lim_ident_at \<comment> \<open> derivative at within \<close>
thm has_field_derivative_iff_has_vector_derivative \<comment> \<open> real vs vector derivative \<close>
thm Rolle_deriv mvt mvt_simple mvt_very_simple mvt_general \<comment> \<open> mean value theorem \<close>
thm banach_fix banach_fix_type \<comment> \<open> banach fixpoint theorems \<close>
thm has_derivative_componentwise_within tendsto_componentwise_iff bounded_linear_compose
thm bounded_linear_compose
thm c1_implies_local_lipschitz

thm blinfun_apply
thm local_lipschitz_def lipschitz_on_def
(********************************************************************************)

lemma bounded_iff_subset_ball:
  "bounded S \<longleftrightarrow> (\<exists>e x. S \<subseteq> ball x e \<and> 0 \<le> e)"
  unfolding bounded_def ball_def subset_eq apply (clarsimp, safe)
  apply (metis approximation_preproc_push_neg(1) dual_order.strict_trans2 gt_ex linear)
  using less_eq_real_def by blast

lemmas bounded_continuous_image = compact_imp_bounded[OF compact_continuous_image]

lemmas bdd_above_continuous_image = bounded_continuous_image[THEN bounded_imp_bdd_above]

lemma real_compact_intervalI:
  "is_interval T \<Longrightarrow> compact T \<Longrightarrow> \<exists>a b. T = {a..b}" for T::"real set"
  by (meson connected_compact_interval_1 is_interval_connected)

lemma c1_local_lipschitz: 
  fixes f::"real \<Rightarrow> ('a::{banach,perfect_space}) \<Rightarrow> 'a"
  assumes "open S" and "open T"
    and c1hyp: "\<forall>\<tau> \<in> T. \<forall>s \<in> S. D (f \<tau>) \<mapsto> \<DD> (at s within S)" "continuous_on S \<DD>"
  shows "local_lipschitz T S f"
proof(unfold local_lipschitz_def lipschitz_on_def, clarsimp simp: dist_norm)
  fix s and t assume "s \<in> S" and "t \<in> T"
  then obtain L where bdd: "\<forall>x. \<parallel>\<DD> x\<parallel> \<le> L * \<parallel>x\<parallel>"
    using c1hyp unfolding has_derivative_def bounded_linear_def bounded_linear_axioms_def
    by (metis mult.commute)
  hence "L \<ge> 0"
    by (metis mult.commute mult.left_neutral norm_ge_zero 
        order_trans vector_choose_size zero_le_one)
  then obtain \<epsilon>\<^sub>1 and \<epsilon>\<^sub>2 where "\<epsilon>\<^sub>1 > 0" and "t \<in> cball t \<epsilon>\<^sub>1"  and "cball t \<epsilon>\<^sub>1 \<subseteq> T"
    and "\<epsilon>\<^sub>2 > 0"  and "s \<in> cball s \<epsilon>\<^sub>2" and "cball s \<epsilon>\<^sub>2 \<subseteq> S"
    using \<open>t \<in> T\<close> \<open>s \<in> S\<close> \<open>open T\<close> \<open>open S\<close> open_contains_cball_eq
    by (metis centre_in_cball less_eq_real_def) 
  hence "t \<in> cball t (min \<epsilon>\<^sub>1 \<epsilon>\<^sub>2) \<inter> T" (is "t \<in> ?B1 \<inter> T")
    and "s \<in> cball s (min \<epsilon>\<^sub>1 \<epsilon>\<^sub>2) \<inter> S" (is "s \<in> ?B2 \<inter> S")
    and "cball s (min \<epsilon>\<^sub>1 \<epsilon>\<^sub>2) \<subseteq> S"
    by auto
  {fix \<tau> assume tau_hyp: "\<tau> \<in> ?B1 \<inter> T"
    {fix x and y assume x_hyp: "x \<in> ?B2 \<inter> S" and y_hyp: "y \<in> ?B2 \<inter> S"
      define \<sigma> and \<sigma>' where sigma_def: "\<sigma> = (\<lambda>\<tau>. x + \<tau> *\<^sub>R (y - x))"
        and dsigma_def: "\<sigma>' = (\<lambda>\<tau>. \<tau> *\<^sub>R (y - x))"
      let ?g = "(f \<tau>) \<circ> \<sigma>"
      have deriv: "D \<sigma> = (\<lambda>t. y - x) on {0..1}"
        unfolding sigma_def has_vderiv_on_def
        by (auto intro!: derivative_eq_intros)
      have "\<sigma> ` {0..1} = closed_segment x y"
        apply(clarsimp simp: closed_segment_def set_eq_iff sigma_def, safe)
         apply(rename_tac r, rule_tac x="r" in exI, force simp: algebra_simps sigma_def)
        by (auto simp: algebra_simps sigma_def)
      hence sigma_img: "\<sigma> ` {0..1} \<subseteq> ?B2"
        using convex_cball[of s "min \<epsilon>\<^sub>1 \<epsilon>\<^sub>2"] convex_contains_segment[of ?B2]
          \<open>?B2 \<subseteq> S\<close> x_hyp y_hyp by blast
      hence "\<forall>r\<in>{0..1}. D f \<tau> \<mapsto> \<DD> at (\<sigma> r) within \<sigma> ` {0..1}"
        using \<open>?B2 \<subseteq> S\<close> c1hyp
        apply(clarify, rule_tac s=S in has_derivative_subset)
        using tau_hyp by blast force
      hence "\<And>r. r \<in> {0..1} \<Longrightarrow> (f \<tau> \<circ> \<sigma> has_vector_derivative \<DD> (y - x)) (at r within {0..1})"
        using vector_derivative_diff_chain_within[of \<sigma> "y - x" _ "{0..1}" "f \<tau>" \<DD>] deriv
        unfolding has_vderiv_on_def by blast
      note fundamental_theorem_of_calculus[OF zero_le_one this] 
      hence key: "((\<lambda>t::real. \<DD> (y - x)) has_integral (f \<tau> \<circ> \<sigma>) 1 - (f \<tau> \<circ> \<sigma>) 0) {0..1}"
        by (clarsimp simp: sigma_def)
      thm has_integral_iff
      have "f \<tau> y - f \<tau> x = ?g 1 - ?g 0"
        by (simp add: sigma_def)
      also have "... = integral {0..1} (\<lambda>t::real. \<DD> (y - x))"
        by (rule sym, rule integral_unique[OF key])
      also have "... = \<DD> (y - x)"
        by (subst integral_const_real, subst content_real, simp_all)
      finally have "\<parallel>f \<tau> y - f \<tau> x\<parallel> = \<parallel>\<DD> (y - x)\<parallel>"
        by simp
      hence "\<parallel>f \<tau> y - f \<tau> x\<parallel> \<le> L * \<parallel>y - x\<parallel>"
        using bdd by auto}
    hence "0 \<le> L \<and> (\<forall>x \<in> ?B2 \<inter> S. \<forall>y \<in> ?B2 \<inter> S. \<parallel>f \<tau> x - f \<tau> y\<parallel> \<le> L * \<parallel>x - y\<parallel>)"
      using \<open>0 \<le> L\<close> by blast}
  thus "\<exists>\<epsilon>>0. \<exists>L. \<forall>\<tau>\<in>cball t \<epsilon> \<inter> T. 0 \<le> L \<and>
    (\<forall>x\<in>cball s \<epsilon> \<inter> S. \<forall>y\<in>cball s \<epsilon> \<inter> S. \<parallel>f \<tau> x - f \<tau> y\<parallel> \<le> L * \<parallel>x - y\<parallel>)"
    using \<open>\<epsilon>\<^sub>1 > 0\<close> \<open>\<epsilon>\<^sub>2 > 0\<close> by (metis Int_commute min_less_iff_conj) 
qed

lemma continuous_derivative_local_lipschitz: (* This should be generalised *)
  fixes f :: "real \<Rightarrow> 'a::real_inner"
  assumes "\<exists>f'. (D f = f' on UNIV) \<and> (continuous_on UNIV f')"
  shows "local_lipschitz UNIV UNIV (\<lambda>t::real. f)"
proof(unfold local_lipschitz_def lipschitz_on_def, clarsimp simp: dist_norm)
  fix x and t
  obtain f' where h1: "D f = f' on UNIV" and h2: "continuous_on UNIV f'"
    using assms by blast
  hence deriv_f1: "\<And>a b. a < b \<Longrightarrow> D f = f' on {a..b}"
    using has_vderiv_on_subset[OF h1] by auto
  hence cont_f: "\<And>a b. a < b \<Longrightarrow> continuous_on {a..b} f"
    using vderiv_on_continuous_on by blast
  have deriv_f2: "\<And>a b x. a < x \<Longrightarrow> x < b \<Longrightarrow> D f \<mapsto> (\<lambda>t. t *\<^sub>R f' x) (at x)"
    using h1 unfolding has_vderiv_on_def has_vector_derivative_def by simp
  have cont_f': "continuous_on UNIV (\<lambda>z. \<parallel>f' z\<parallel>)"
    apply(subst comp_def[symmetric, where f=norm])
    apply(rule continuous_on_compose[OF h2])
    using continuous_on_norm_id by blast
  {fix a b::real assume "a < b"
    hence f1: "(\<And>x. a < x \<Longrightarrow> x < b \<Longrightarrow> D f \<mapsto> (\<lambda>t. t *\<^sub>R f' x) (at x))"
      using deriv_f2 unfolding has_vderiv_on_def has_vector_derivative_def by simp
    thm mvt_general[of a b]
    hence "\<exists>x\<in>{a<..<b}. \<parallel>f b - f a\<parallel> \<le> \<bar>b - a\<bar> * \<parallel>f' x\<parallel>"
      using mvt_general[OF \<open>a < b\<close> cont_f[OF \<open>a < b\<close>] f1] by auto}
  hence key: "\<And>a b. a < b \<Longrightarrow> \<exists>x\<in>{a<..<b}. \<parallel>f b - f a\<parallel> \<le> \<parallel>f' x\<parallel> * \<bar>b - a\<bar>"
    by (metis mult.commute)
  {fix \<epsilon>::real assume "\<epsilon> > 0"
    let ?L = "Sup ((\<lambda>z. \<parallel>f' z\<parallel>) ` cball x \<epsilon>)"
    have "?L \<ge> 0"
      apply(rule_tac x=x in conditionally_complete_lattice_class.cSUP_upper2)
        apply(rule bdd_above_continuous_image; clarsimp?)
        apply(rule continuous_on_subset[OF cont_f'])
      using \<open>\<epsilon> > 0\<close> by auto
    {fix a b assume "a \<in> cball x \<epsilon>" and "b \<in> cball x \<epsilon>"
      hence "\<exists>x\<in>{a--b}. \<parallel>f b - f a\<parallel> \<le> \<parallel>f' x\<parallel> * \<bar>b - a\<bar>"
        using key apply(cases "a = b", clarsimp) 
        apply(cases "a < b"; clarsimp)
         apply (metis ODE_Auxiliarities.closed_segment_eq_real_ivl atLeastAtMost_iff 
            greaterThanLessThan_iff less_eq_real_def)
        by (metis ODE_Auxiliarities.closed_segment_eq_real_ivl atLeastAtMost_iff 
            dist_commute dist_norm greaterThanLessThan_iff less_eq_real_def not_le)
      then obtain z where "z\<in>{a--b}" and z_hyp: "\<parallel>f b - f a\<parallel> \<le> \<parallel>f' z\<parallel> * \<bar>b - a\<bar>"
        by blast
      hence "{a--b} \<subseteq> cball x \<epsilon>" and "z \<in> cball x \<epsilon>"
        by (meson \<open>a \<in> cball x \<epsilon>\<close> \<open>b \<in> cball x \<epsilon>\<close> closed_segment_subset convex_cball subset_eq)+
      hence "\<parallel>f' z\<parallel> \<le> ?L"
        by (metis bdd_above_continuous_image cSUP_upper compact_cball cont_f' 
            continuous_on_subset top.extremum)
      hence "\<parallel>f b - f a\<parallel> \<le> ?L * \<bar>b - a\<bar>"
        using z_hyp by (smt (verit, best) mult_right_mono)}
    hence "(\<exists>ta. \<bar>t - ta\<bar> \<le> \<epsilon>) \<longrightarrow> (\<exists>L\<ge>0. \<forall>xa\<in>cball x \<epsilon>. \<forall>y\<in>cball x \<epsilon>. \<parallel>f xa - f y\<parallel> \<le> L * \<bar>xa - y\<bar>)"
      using \<open>?L \<ge> 0\<close> by auto}
  thus "\<exists>u>0. (\<exists>ta. \<bar>t - ta\<bar> \<le> u) \<longrightarrow>
    (\<exists>L\<ge>0. \<forall>xa\<in>cball x u. \<forall>y\<in>cball x u. \<parallel>f xa - f y\<parallel> \<le> L * \<bar>xa - y\<bar>)"
    by (rule_tac x=1 in exI, auto)
qed

end