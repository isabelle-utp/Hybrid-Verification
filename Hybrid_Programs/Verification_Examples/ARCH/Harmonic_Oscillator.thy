theory Harmonic_Oscillator
  imports "Hybrid-Verification.Hybrid_Verification"

begin


subsection \<open> Harmonic oscillator \<close>

lemma hosc_arith:
  assumes "b\<^sup>2 + 4 * a > 0" and "a < 0" and "b \<le> 0" and "t \<ge> 0" and "k > 0"
  shows "k * (b - sqrt (b\<^sup>2 + 4 * a)) * exp (t * (b + sqrt (b\<^sup>2 + 4 * a)) / 2) / (2 * sqrt (b\<^sup>2 + 4 * a))
       \<le> k * (b + sqrt (b\<^sup>2 + 4 * a)) * exp (t * (b - sqrt (b\<^sup>2 + 4 * a)) / 2) / (2 * sqrt (b\<^sup>2 + 4 * a))"
proof-
  have f0: "k / (2 * sqrt (b\<^sup>2 + a * 4)) \<ge> 0"  (is "k/?c3 \<ge> 0")
    using assms(1,5) by simp
  have f1: "(b - sqrt (b\<^sup>2 + 4 * a)) < (b + sqrt (b\<^sup>2 + 4 * a))" (is "?c2 < ?c1") 
    and f2: "(b + sqrt (b\<^sup>2 + 4 * a)) < 0"
    using sqrt_ge_absD[of b "b\<^sup>2 + 4 * a"] assms by (force, linarith)
  hence f3: "exp (t * ?c2 / 2) \<le> exp (t * ?c1 / 2)" (is "exp ?t1 \<le> exp ?t2")
    unfolding exp_le_cancel_iff 
    using assms(4) by (case_tac "t=0", simp_all)
  hence "?c2 * exp ?t2 \<le> ?c2 * exp ?t1"
    using f1 f2 mult_le_cancel_left_pos[of "-?c2" "exp ?t1" "exp ?t2"] by linarith 
  also have "... < ?c1 * exp ?t1"
    using f1 by auto
  also have"... \<le> ?c1 * exp ?t1"
    using f1 f2 by auto
  ultimately have "?c2 * exp ?t2 \<le> ?c1 * exp ?t1"
    using f1 assms(5) by auto
  hence "(?c2 * exp ?t2) * (k / ?c3) \<le> (?c1 * exp ?t1) * (k / ?c3)"
    using f0 mult_right_mono by blast
  thus ?thesis
    by (auto simp: field_simps)
qed

dataspace harmonic_osc =
  constants
    a :: real
    b :: real
  variables 
    x :: real 
    y :: real 

context harmonic_osc
begin

abbreviation mtx_hosc :: "2 sq_mtx" ("A")
  where "A \<equiv> mtx  
   ([0, 1] # 
    [a, b] # [])"

lemma mtx_hosc_nths:
  "A $$ 1 = (\<chi> i. if i=1 then 0 else 1)"
  "A $$ 2 = (\<chi> i. if i=1 then a else b)"
  "A $$ 1 $ 1 = 0" "A $$ 1 $ 2 = 1"
  "A $$ 2 $ 1 = a" "A $$ 2 $ 2 = b"
  using exhaust_2
  by (auto simp: vec_eq_iff)

lemma A_vec_mult_eq: "A *\<^sub>V s = vector [s$2, a * s$1 + b * s$2]"
  using exhaust_2
  by (clarsimp simp: vec_eq_iff vector_nth_eq 
      sq_mtx_vec_mult_eq UNIV_2)

definition "discr \<equiv> sqrt (b\<^sup>2 + 4 * a)"

lemma discr_alt: "discr = sqrt (b\<^sup>2 + a * 4)"
  by (clarsimp simp: discr_def)

definition  iota1 :: "real" ("\<iota>\<^sub>1")
  where "\<iota>\<^sub>1 \<equiv> (b - discr)/2"

definition iota2 :: "real" ("\<iota>\<^sub>2")
  where "\<iota>\<^sub>2 \<equiv> (b + discr)/2"

abbreviation "x_sol t x1 y1 \<equiv> 
    (1/discr) * x1 * \<iota>\<^sub>2 * exp (t * \<iota>\<^sub>1) - (1/discr) * x1 * \<iota>\<^sub>1 * exp (t * \<iota>\<^sub>2)
  + (1/discr) * y1 * exp (t * \<iota>\<^sub>2) - (1/discr) * y1 * exp (t * \<iota>\<^sub>1)"

abbreviation "y_sol t x1 y1 \<equiv> 
    (1/discr) * x1 * a * exp (t * \<iota>\<^sub>2) - (1/discr) * x1 * a * exp (t * \<iota>\<^sub>1)
  + (1/discr) * y1 * \<iota>\<^sub>2 * exp (t * \<iota>\<^sub>2) - (1/discr) * y1 * \<iota>\<^sub>1 * exp (t * \<iota>\<^sub>1)"

abbreviation "\<Phi> t \<equiv> mtx (
   [\<iota>\<^sub>2*exp(t*\<iota>\<^sub>1) - \<iota>\<^sub>1*exp(t*\<iota>\<^sub>2),     exp(t*\<iota>\<^sub>2)-exp(t*\<iota>\<^sub>1)]#
   [a*exp(t*\<iota>\<^sub>2) - a*exp(t*\<iota>\<^sub>1), \<iota>\<^sub>2*exp(t*\<iota>\<^sub>2)-\<iota>\<^sub>1*exp(t*\<iota>\<^sub>1)]#[])"

lemma x_sol_eq: "x_sol t x1 y1 = (((1/discr) *\<^sub>R \<Phi> t) *\<^sub>V (vector [x1,y1])) $ (1::2)"
  apply (clarsimp simp: sq_mtx_vec_mult_eq UNIV_2)
  by distribute (simp add: mult.commute diff_divide_distrib)

lemma y_sol_eq: "y_sol t x1 y1 = (((1/discr) *\<^sub>R \<Phi> t) *\<^sub>V (vector [x1,y1])) $ (2::2)"
  apply (clarsimp simp: sq_mtx_vec_mult_eq UNIV_2)
  by distribute (simp add: mult.commute mult.left_commute diff_divide_distrib)

abbreviation chB_hosc :: "real \<Rightarrow> real \<Rightarrow> 2 sq_mtx" ("P")
  where "P a1 a2 \<equiv> mtx
   ([a1, a2] # 
    [1, 1] # [])"

lemma inv_mtx_chB_hosc: 
  "a1 \<noteq> a2 \<Longrightarrow> (P a1 a2)\<^sup>-\<^sup>1 = (1/(a1 - a2)) *\<^sub>R mtx 
   ([ 1, -a2] # 
    [-1,  a1] # [])"
  apply(rule sq_mtx_inv_unique, unfold scaleR_mtx2 times_mtx2)
  by (simp add: diff_divide_distrib[symmetric] one_mtx2)+

lemma invertible_mtx_chB_hosc: "a1 \<noteq> a2 \<Longrightarrow> mtx_invertible (P a1 a2)"
  apply(rule mtx_invertibleI[of _ "(P a1 a2)\<^sup>-\<^sup>1"])
   apply(unfold inv_mtx_chB_hosc scaleR_mtx2 times_mtx2 one_mtx2)
  by (subst sq_mtx_eq_iff, simp add: vector_def frac_diff_eq1)+

lemma mtx_hosc_diagonalizable:
  assumes "b\<^sup>2 + a * 4 > 0" and "a \<noteq> 0"
  shows "A = P (-\<iota>\<^sub>2/a) (-\<iota>\<^sub>1/a) * (\<d>\<i>\<a>\<g> i. if i = 1 then \<iota>\<^sub>1 else \<iota>\<^sub>2) * (P (-\<iota>\<^sub>2/a) (-\<iota>\<^sub>1/a))\<^sup>-\<^sup>1"
  unfolding assms apply(subst inv_mtx_chB_hosc)
  using assms apply(simp_all add: diag2_eq[symmetric])
  apply (simp add: iota1_def discr_def iota2_def)
  unfolding sq_mtx_times_eq sq_mtx_scaleR_eq UNIV_2 apply(subst sq_mtx_eq_iff)
  using exhaust_2 assms 
  by (auto simp: field_simps) 
    (auto simp: iota1_def iota2_def discr_def field_simps)

lemma mtx_hosc_solution_eq:
  assumes "b\<^sup>2 + a * 4 > 0" and "a \<noteq> 0"
  shows "P (-\<iota>\<^sub>2/a) (-\<iota>\<^sub>1/a) * (\<d>\<i>\<a>\<g> i. exp (t * (if i=1 then \<iota>\<^sub>1 else \<iota>\<^sub>2))) * (P (-\<iota>\<^sub>2/a) (-\<iota>\<^sub>1/a))\<^sup>-\<^sup>1 
  = (1/discr) *\<^sub>R (\<Phi> t)"
  unfolding assms apply(subst inv_mtx_chB_hosc)
  using assms apply (simp add: iota1_def discr_def iota2_def)
  using assms apply(simp_all add: mtx_times_scaleR_commute, subst sq_mtx_eq_iff)
  unfolding UNIV_2 sq_mtx_times_eq sq_mtx_scaleR_eq sq_mtx_uminus_eq apply(simp_all add: axis_def)
  by (auto simp: field_simps) 
    (auto simp: iota1_def iota2_def discr_def field_simps)

lemma "c \<noteq> 0 \<Longrightarrow> c * u = c * v \<Longrightarrow> u = v" for c::real
  by (auto simp: field_simps)

lemma my_subst: "[x \<leadsto> y, y \<leadsto> a * x + b * y] = 
  (\<lambda>\<s>. put\<^bsub>y\<^esub> (put\<^bsub>x\<^esub> \<s> ((A *\<^sub>V (vector [$x, $y])) $ 1)) ((A *\<^sub>V (vector [$x, $y])) $ 2))"
  by (expr_auto add: A_vec_mult_eq)

lemma local_lipschitz_hosc: 
  "local_lipschitz UNIV UNIV (tsubst2vecf (x +\<^sub>L y) (\<lambda>t::real. [x \<leadsto> y, y \<leadsto> a * x + b * y]) s)"
  by c1_lipschitz

lemma sols_to_Phi: "(x1 * \<iota>\<^sub>2 * exp (t * \<iota>\<^sub>1) / discr - x1 * \<iota>\<^sub>1 * exp (t * \<iota>\<^sub>2) / discr 
      + y1 * exp (t * \<iota>\<^sub>2) / discr - y1 * exp (t * \<iota>\<^sub>1) / discr,
        x1 * a * exp (t * \<iota>\<^sub>2) / discr - x1 * a * exp (t * \<iota>\<^sub>1) / discr 
      + y1 * \<iota>\<^sub>2 * exp (t * \<iota>\<^sub>2) / discr - y1 * \<iota>\<^sub>1 * exp (t * \<iota>\<^sub>1) / discr) = 
  (((1/discr) *\<^sub>R \<Phi> t) *\<^sub>V (vector [x1,y1]) $ (1::2), 
  ((1/discr) *\<^sub>R \<Phi> t) *\<^sub>V (vector [x1,y1]) $ (2::2))"
  apply (clarsimp simp: sq_mtx_vec_mult_eq UNIV_2)
  apply distribute
  by (clarsimp simp: add_divide_distrib diff_divide_distrib mult.commute)
    (simp add: mult.left_commute)

lemma vecf_to_A: "(
    x1 * a * exp (t * \<iota>\<^sub>2) / discr - x1 * a * exp (t * \<iota>\<^sub>1) / discr 
      + y1 * \<iota>\<^sub>2 * exp (t * \<iota>\<^sub>2) / discr - y1 * \<iota>\<^sub>1 * exp (t * \<iota>\<^sub>1) / discr,
    a * (x1 * \<iota>\<^sub>2 * exp (t * \<iota>\<^sub>1) / discr - x1 * \<iota>\<^sub>1 * exp (t * \<iota>\<^sub>2) / discr 
      + y1 * exp (t * \<iota>\<^sub>2) / discr - y1 * exp (t * \<iota>\<^sub>1) / discr) 
      + b * (x1 * a * exp (t * \<iota>\<^sub>2) / discr - x1 * a * exp (t * \<iota>\<^sub>1) / discr 
      + y1 * \<iota>\<^sub>2 * exp (t * \<iota>\<^sub>2) / discr - y1 * \<iota>\<^sub>1 * exp (t * \<iota>\<^sub>1) / discr)) 
    = (
     (A *\<^sub>V (((1/discr) *\<^sub>R \<Phi> t) *\<^sub>V (vector [x1,y1]))) $ (1::2), 
     (A *\<^sub>V (((1/discr) *\<^sub>R \<Phi> t) *\<^sub>V (vector [x1,y1]))) $ (2::2))"
  apply (clarsimp simp: sq_mtx_vec_mult_eq UNIV_2)
  apply distribute
  apply (clarsimp simp: add_divide_distrib diff_divide_distrib mult.commute)
  apply (simp add: mult.left_commute)
  apply distribute
  by (clarsimp simp: add_divide_distrib diff_divide_distrib mult.commute)

lemma local_flow_mtx_hosc:
  assumes "b\<^sup>2 + a * 4 > 0" and "a \<noteq> 0"
  shows "local_flow ((*\<^sub>V) A) UNIV UNIV (\<lambda>t. (*\<^sub>V) ((1/discr) *\<^sub>R \<Phi> t))"
  unfolding assms using local_flow_sq_mtx_linear[of "A"] assms
  apply(subst (asm) exp_scaleR_diagonal2[OF invertible_mtx_chB_hosc mtx_hosc_diagonalizable])
     apply(simp add: iota1_def iota2_def discr_def, simp, simp)
  by (subst (asm) mtx_hosc_solution_eq) assumption

lemma has_vderiv_Phi_A: "0 < b\<^sup>2 + a * 4 \<Longrightarrow> a \<noteq> 0 
  \<Longrightarrow> ((\<lambda>t. ((1 / discr) *\<^sub>R \<Phi> t) *\<^sub>V s) has_vderiv_on (\<lambda>t. A *\<^sub>V (((1 / discr) *\<^sub>R \<Phi> t) *\<^sub>V s))) {0--t}"
  using conjunct1[OF conjunct2[OF local_flow_mtx_hosc[unfolded local_flow_def local_flow_axioms_def]]] 
  by clarsimp

lemmas vderiv_vec_nthI = iffD1[OF has_vderiv_on_component, rule_format]

lemma local_flow_hosc: "a \<noteq> 0 \<Longrightarrow> b\<^sup>2 + 4 * a > 0
  \<Longrightarrow> local_flow_on [x \<leadsto> y, y \<leadsto> a * x + b * y] (x +\<^sub>L y) UNIV UNIV
  (\<lambda>t. [x \<leadsto> x_sol t x y, y \<leadsto> y_sol t x y])"
  apply (((clarsimp simp: local_flow_on_def)?, unfold_locales; clarsimp?), c1_lipschitz)
   apply (expr_simp add: x_sol_eq y_sol_eq)
  apply (subst sols_to_Phi, subst vecf_to_A)
   apply (vderiv_single intro: vderiv_vec_nthI has_vderiv_Phi_A)
  apply (expr_simp add: iota1_def iota2_def)
  by distribute 
    (clarsimp simp: add_divide_distrib diff_divide_distrib discr_def)


lemma "a < 0 \<Longrightarrow> b \<le> 0 \<Longrightarrow> b\<^sup>2 + 4 * a > 0 \<Longrightarrow>
  H{x=0} 
  LOOP (
    (x ::= ?);(y ::= 0); \<questiondown>x>0?;
    {x` = y, y` = a * x + b * y}
  ) INV (x\<ge>0)
  {x\<ge>0}"
  apply (rule hoare_loopI)
    prefer 3 apply expr_simp
   prefer 2 apply expr_simp
  using hosc_arith[of b a]
  by (wlp_full local_flow: local_flow_hosc)
    (clarsimp simp: iota1_def iota2_def discr_def)


end


end