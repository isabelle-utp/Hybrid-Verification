theory Obstacle_Avoidance
  imports "Hybrid-Verification.Hybrid_Verification"
begin

notation norm ("\<parallel>_\<parallel>")
notation infnorm ("\<parallel>_\<parallel>\<^sub>\<infinity>")

abbreviation (input) e1 :: "real^2" where "e1 \<equiv> axis 1 1"
abbreviation (input) e2 :: "real^2" where "e2 \<equiv> axis 2 1"

definition right_angle_rotation :: "real^2 \<Rightarrow> real^2" where
  "right_angle_rotation v = (inner v e1) *\<^sub>R e2 - (inner v e2) *\<^sub>R e1"

lemma linear_right_angle_rotation: "linear right_angle_rotation"
  unfolding right_angle_rotation_def
  by (simp add: inner_left_distrib linearI scaleR_right_diff_distrib vector_space_assms(2))

dataspace obstacle_avoidance =
  constants
    A :: real
    b :: real
    \<epsilon> :: real
    V :: real
    \<Omega> :: real
  assumes
    A_min: "A \<ge> 0" and
    b_min: "b > 0" and
    eps_min: "\<epsilon> > 0" and
    V_min: "V \<ge> 0" and
    \<Omega>_min: "\<Omega> \<ge> 0" 
  variables
    t :: real
    p :: "real ^ 2"
    s :: real
    a :: real
    \<omega> :: real
    d :: "real ^ 2"
    c :: "real ^ 2"
    r :: real
    ob :: "real ^ 2"
    v :: "real ^ 2"
    oldp :: "real ^ 2"
    olds :: "real"

context obstacle_avoidance
begin

definition ctrl :: "'st prog \<Rightarrow> ('st \<Rightarrow> bool) \<Rightarrow> 'st prog" where
  "ctrl drive safe = 
    (a := -b
     \<sqinter> \<questiondown>s = 0? ; a := 0 ; \<omega> := 0
     \<sqinter> drive ; \<omega> := ? ; \<questiondown>-\<Omega> \<le> \<omega> \<and> \<omega> \<le> \<Omega>? ; r := ? ; \<questiondown>r \<noteq> 0 \<and> r * \<omega> = s \<and> @safe?) ;
    t := 0 ; oldp := p ; olds := s"

expression safe is "\<parallel>p - ob\<parallel>\<^sub>\<infinity> > (s\<^sup>2 / (2*b)) + (A/b + 1) * (A/2 * \<epsilon>\<^sup>2 + \<epsilon> * s)"

definition 
 "\<Psi> opc obc ac osc =
  (oldp = opc \<and> ob = obc \<and> a = ac \<and> olds = osc
    \<and> 0 \<le> s \<and> 0 \<le> t \<and> t \<le> \<epsilon> \<and> \<parallel>d\<parallel> = 1 \<and> s = olds + a * t
    \<and> \<parallel>p - oldp\<parallel>\<^sub>\<infinity> \<le> t * (s - a * t/2))\<^sup>e"

expr_constructor \<Psi>

expression safety_condition is "0 < \<parallel>p - ob\<parallel>"

notation safety_condition ("\<psi>")

expression loop_invariant is "s^2/(2*b) < \<parallel>p - ob\<parallel>\<^sub>\<infinity> \<and> 0 \<le> s \<and> \<parallel>d\<parallel> = 1"

notation loop_invariant ("\<phi>")

expression initial_condition is "s = 0 \<and> \<parallel>p - ob\<parallel>\<^sub>\<infinity> > 0 \<and> r \<noteq> 0 \<and> \<parallel>d\<parallel> = 1"

notation initial_condition ("\<Phi>")

definition dyn :: "'st prog" where
"dyn = {t` = 1, p` = s *\<^sub>R d, s` = a, d` = \<omega> *\<^sub>R right_angle_rotation d, \<omega>` = a / r | s \<ge> 0 \<and> t \<le> \<epsilon>}"

definition "model1 = (ctrl (a := A) safe ; dyn)\<^sup>*"

lemma dyn_inv: "H{\<Psi> opc obc ac osc} dyn {\<Psi> opc obc ac osc}"
  apply (unfold dyn_def \<Psi>_def)
  apply (dCut "\<parallel>d\<parallel> = 1")
   apply (invariant "d \<bullet> d = 1")
     apply dInduct_auto
     apply (smt (verit, ccfv_threshold) cross3_simps(36) inner_commute inner_real_def inner_scaleR_left right_angle_rotation_def)
    apply (simp add: norm_eq_1)
  apply (simp add: norm_eq_1)
  apply (dInduct_mega)
  apply (invariant "- t * (s - a * t/2) \<le> (p - oldp) $ 0 \<and> (p - oldp) $ 0 \<le> t * (s - a * t/2) \<and> - t * (s - a * t/2) \<le> (p - oldp) $ 1 \<and> (p - oldp) $1 \<le> t * (s - a * t/2)")
    apply (dInduct_mega)
  apply expr_simp
     apply (smt (verit) Finite_Cartesian_Product.norm_nth_le more_arith_simps(8) mult_left_le real_norm_def)
  apply dInduct_mega
  apply expr_simp
     apply (smt (verit) Finite_Cartesian_Product.norm_nth_le more_arith_simps(8) mult_left_le real_norm_def)
  apply dInduct_mega
  apply expr_simp
     apply (smt (verit) Finite_Cartesian_Product.norm_nth_le more_arith_simps(8) mult_left_le real_norm_def)
  apply dInduct_mega
  apply expr_simp
     apply (smt (verit) Finite_Cartesian_Product.norm_nth_le more_arith_simps(8) mult_left_le real_norm_def)
  apply expr_simp
   apply (smt (verit, best) exhaust_2 infnorm_2 vector_minus_component)
  apply expr_simp
  apply (smt (verit, best) arith_extra_simps(7) arith_special(23) diff_numeral_special(9) exhaust_2 infnorm_2 vector_minus_component)
  done

lemma ctrl_inv: "H{\<phi>} ctrl (a := A) safe {\<phi> \<and> t = 0}"
  apply (simp add: ctrl_def safe_def loop_invariant_def \<Psi>_def)
  apply wlp_simp
  done

theorem static_safety: "H{\<Phi>} model1 {\<psi>}"
  apply (unfold model1_def)
  apply (kstar "loop_invariant")
    apply (rule hoare_kcomp_inv)
     defer
     defer
     apply expr_simp
  apply expr_simp
  apply (metis arith_simps(62) b_min divide_less_eq infnorm_eq_0 norm_le_zero_iff norm_pths(1)
      power2_less_0 rel_simps(51) zero_compare_simps(6))
  oops

end

end