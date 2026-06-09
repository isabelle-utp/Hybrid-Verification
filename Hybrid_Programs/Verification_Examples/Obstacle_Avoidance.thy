theory Obstacle_Avoidance
  imports "Hybrid-Verification.Hybrid_Verification" (* "Explorer.Explorer" *)
begin

(* setup Explorer_Lib.switch_to_quotes *)

unbundle Hybrid_Program_Syntax

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
    sp :: real
    a :: real
    \<omega> :: real
    d :: "real ^ 2"
    c :: "real ^ 2"
    r :: real
    ob :: "real ^ 2"
    v :: "real ^ 2"

context obstacle_avoidance
begin

definition ctrl :: "'st prog \<Rightarrow> ('st \<Rightarrow> bool) \<Rightarrow> 'st prog" where
  "ctrl drive safe = 
    (a := -b
     \<sqinter> \<questiondown>sp = 0? ; a := 0 ; \<omega> := 0
     \<sqinter> drive ; \<omega> := ? ; \<questiondown>-\<Omega> \<le> \<omega> \<and> \<omega> \<le> \<Omega>? ; r := ? ; \<questiondown>r \<noteq> 0 \<and> r * \<omega> = sp \<and> @safe?) ;
    t := 0"

expression safe is "\<parallel>p - ob\<parallel>\<^sub>\<infinity> > (sp\<^sup>2 / (2*b)) + (A/b + 1) * (A/2 * \<epsilon>\<^sup>2 + \<epsilon> * sp)"

definition 
 "\<Psi> = (\<lambda> (opc, obc, ac, osc).
  (ob = obc \<and> a = ac
    \<and> 0 \<le> sp \<and> 0 \<le> t \<and> t \<le> \<epsilon> \<and> \<parallel>d\<parallel> = 1 \<and> sp = osc + a * t
    \<and> \<parallel>p - opc\<parallel>\<^sub>\<infinity> \<le> t * (sp - a * t/2))\<^sup>e)"

expr_constructor \<Psi>

expression safety_condition is "0 < \<parallel>p - ob\<parallel>"

notation safety_condition ("\<psi>")

expression loop_invariant is "sp^2/(2*b) < \<parallel>p - ob\<parallel>\<^sub>\<infinity> \<and> 0 \<le> sp \<and> \<parallel>d\<parallel> = 1"

notation loop_invariant ("\<phi>")

expression initial_condition is "sp = 0 \<and> \<parallel>p - ob\<parallel>\<^sub>\<infinity> > 0 \<and> r \<noteq> 0 \<and> \<parallel>d\<parallel> = 1"

notation initial_condition ("\<Phi>")

definition dyn :: "'st prog" where
"dyn = {t` = 1, p` = sp *\<^sub>R d, sp` = a, d` = \<omega> *\<^sub>R right_angle_rotation d, \<omega>` = a / r | sp \<ge> 0 \<and> t \<le> \<epsilon>}"

definition "model1 = (ctrl (a := A) safe ; dyn)\<^sup>*"

lemma dyn_inv: "H{\<Psi> (opc, obc, ac, osc)} dyn {\<Psi> (opc, obc, ac, osc)}"
  apply (unfold dyn_def \<Psi>_def)
  apply (dCut "\<parallel>d\<parallel> = 1")
   apply (invariant "d \<bullet> d = 1")
     apply dInduct_auto
     apply (smt (verit, ccfv_threshold) cross3_simps(36) inner_commute inner_real_def inner_scaleR_left right_angle_rotation_def)
    apply (simp add: norm_eq_1)
   apply (simp add: norm_eq_1)
  apply simp
  apply (dInduct_mega)
  apply (invariant "- t * (sp - a * t/2) \<le> (p - opc) $ 0 \<and> (p - opc) $ 0 \<le> t * (sp - a * t/2) \<and> - t * (sp - a * t/2) \<le> (p - opc) $ 1 \<and> (p - opc) $ 1 \<le> t * (sp - a * t/2)")
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
proof (unfold model1_def, kstar "loop_invariant", simp add: ctrl_def loop_invariant_def safe_def, symbolic_exec, simp_all)
  show "H{t = 0 \<and> \<omega> = 0 \<and> a = 0 \<and> sp\<^sup>2 / (2 * b) < \<parallel>p - ob\<parallel>\<^sub>\<infinity> \<and> 0 \<le> sp \<and> \<parallel>d\<parallel> = 1 \<and> sp = 0} 
          dyn 
         {sp\<^sup>2 / (2 * b) < \<parallel>p - ob\<parallel>\<^sub>\<infinity> \<and> 0 \<le> sp \<and> \<parallel>d\<parallel> = 1}"

  \<comment> \<open> For each Hoare triple, we need to drop down into point-wise reasoning, so we can explicitly characterise state changes. \<close>
  proof (rule hoare_fboxI, clarsimp)
    fix s
    assume t_0: "t<s> = 0" and \<omega>_0: "\<omega><s> = 0" and a_0: "a<s> = 0" and sep: "0 < \<parallel>p<s> - ob<s>\<parallel>\<^sub>\<infinity>" and d1: "\<parallel>d<s>\<parallel> = 1" and sp_0: "sp<s> = 0"
    \<comment> \<open> We can show that the dynamics invariant holds initially \<close>
    with eps_min have "\<Psi> (p<s>, ob<s>, a<s>, sp<s>) s"
      by (simp add: \<Psi>_def infnorm_0)
    show "( |dyn] (sp\<^sup>2 / (2 * b) < \<parallel>p - ob\<parallel>\<^sub>\<infinity> \<and> 0 \<le> sp \<and> \<parallel>d\<parallel> = 1)) s"
    proof (intro fboxI, simp, safe)
      fix s'
      assume "s' \<in> dyn s"
      have \<Psi>_s': "\<Psi> (p<s>, ob<s>, a<s>, sp<s>) s'"
        by (smt (verit, best) SEXP_def \<open>\<Psi> (p<s>, ob<s>, a<s>, sp<s>) s\<close> \<open>s' \<in> dyn s\<close> dyn_inv
            fbox_def predicate1D)
      thus "(sp<s'>)\<^sup>2 / (2 * b) < \<parallel>p<s'> - ob<s'>\<parallel>\<^sub>\<infinity>"
        by (simp add: \<Psi>_def, clarify)
           (metis \<open>0 < \<parallel>p<s> - ob<s>\<parallel>\<^sub>\<infinity>\<close> \<open>a<s> = 0\<close> \<open>sp<s> = 0\<close> arith_simps(62,63) div_0
            infnorm_pos_lt less_le_not_le nat_arith.rule0 power_zero_numeral
            right_minus_eq)
      from \<Psi>_s' sp_0 a_0 show "0 \<le> sp<s'>"
        by (simp add: \<Psi>_def)
      from \<Psi>_s' show "\<parallel>d<s'>\<parallel> = 1" by (simp add: \<Psi>_def)
      have \<Psi>_s': "\<Psi> (p<s>, ob<s>, a<s>, sp<s>) s'"
        by (smt (verit, best) SEXP_def \<open>\<Psi> (p<s>, ob<s>, a<s>, sp<s>) s\<close> \<open>s' \<in> dyn s\<close> dyn_inv
            fbox_def predicate1D)
    qed
  qed
next
  show "H{t = 0 \<and> a = - b \<and> sp\<^sup>2 / (2 * b) < \<parallel>p - ob\<parallel>\<^sub>\<infinity> \<and> 0 \<le> sp \<and> \<parallel>d\<parallel> = 1} dyn
         {sp\<^sup>2 / (2 * b) < \<parallel>p - ob\<parallel>\<^sub>\<infinity> \<and> 0 \<le> sp \<and> \<parallel>d\<parallel> = 1}"
  proof (rule hoare_fboxI, clarsimp)
    fix s
    assume t_0: "t<s> = 0" and a_b: "a<s> = - b" and sep: "(sp<s>)\<^sup>2 / (2 * b) < \<parallel>p<s> - ob<s>\<parallel>\<^sub>\<infinity>" and sp_pos: "0 \<le> sp<s>"
           and d1: "\<parallel>d<s>\<parallel> = 1"
    with eps_min have \<Psi>_s: "\<Psi> (p<s>, ob<s>, a<s>, sp<s>) s"
      by (simp add: \<Psi>_def infnorm_0)
    show "( |dyn] (sp\<^sup>2 / (2 * b) < \<parallel>p - ob\<parallel>\<^sub>\<infinity> \<and> 0 \<le> sp \<and> \<parallel>d\<parallel> = 1)) s"
    proof (intro fboxI, simp, safe)
      fix s'
      assume "s' \<in> dyn s"
      have \<Psi>_s': "\<Psi> (p<s>, ob<s>, a<s>, sp<s>) s'"
        by (smt (verit, best) SEXP_def \<Psi>_s \<open>s' \<in> dyn s\<close> dyn_inv fbox_def predicate1D)
      have hold: "sp<s> ^ 2 / (2 * b) < infnorm (p<s> - ob<s>)"
        using sep by force
      have hmove: "infnorm (p<s'> - p<s>) \<le> t<s'> * (sp<s> + -(b * t<s'>) - -(b * t<s'>) / 2)"
      proof -
        have hsp_eq: "sp<s'> = sp<s> + -(b * t<s'>)"
          using \<Psi>_def \<Psi>_s' a_b minus_mult_right mult.commute prod.simps(2) by auto
        show ?thesis
          by (smt (verit) \<Psi>_def \<Psi>_s' hsp_eq prod.simps(2))
      qed
      have hgoal: "(sp<s> + -(b * t<s'>)) ^ 2 / (2 * b) < infnorm (p<s'> - ob<s>)"
      proof -
        have "infnorm (p<s> - ob<s>) \<le> infnorm (p<s> - p<s'>) + infnorm (p<s'> - ob<s>)"
          by (metis (no_types, lifting) add_diff_cancel_right diff_add_cancel infnorm_triangle)
        also have "... = infnorm (p<s'> - p<s>) + infnorm (p<s'> - ob<s>)"
          by (simp add: infnorm_sub)
        finally have "sp<s> ^ 2 / (2 * b) < infnorm (p<s'> - p<s>) + infnorm (p<s'> - ob<s>)"
          using hold by linarith
        moreover have "infnorm (p<s'> - p<s>) \<le> t<s'> * sp<s> - b * (t<s'> ^ 2) / 2"
          using hmove by (simp add: field_simps power2_eq_square)
        moreover have "sp<s> ^ 2 / (2 * b) - (t<s'> * sp<s> - b * (t<s'> ^ 2) / 2) = (sp<s> - b * t<s'>) ^ 2 / (2 * b)"
          using b_min by (simp add: field_simps power2_eq_square)
        ultimately show ?thesis
          by simp 
      qed
      thus "(sp<s'>)\<^sup>2 / (2 * b) < \<parallel>p<s'> - ob<s'>\<parallel>\<^sub>\<infinity>"
        using \<Psi>_s' a_b by (auto simp add: \<Psi>_def)
      show "0 \<le> sp<s'>"
        using \<Psi>_s' by (auto simp add: \<Psi>_def)
      show "\<parallel>d<s'>\<parallel> = 1"
        using \<Psi>_s' by (auto simp add: \<Psi>_def)
    qed
  qed
next
  fix \<omega>\<^sub>0 :: real and r\<^sub>0 :: real

  show "H{t = 0 \<and> a = A \<and> sp\<^sup>2 / (2 * b) < \<parallel>p - ob\<parallel>\<^sub>\<infinity> \<and> 0 \<le> sp \<and> \<parallel>d\<parallel> = 1 
         \<and> \<omega> = \<omega>\<^sub>0 \<and> - \<Omega> \<le> \<omega> \<and> \<omega> \<le> \<Omega> \<and> r = r\<^sub>0 \<and> r \<noteq> 0 \<and> r * \<omega> = sp 
         \<and> sp\<^sup>2 / (2 * b) + (A / b + 1) * (A * \<epsilon>\<^sup>2 / 2 + \<epsilon> * sp) < \<parallel>p - ob\<parallel>\<^sub>\<infinity>} 
         dyn 
       {sp\<^sup>2 / (2 * b) < \<parallel>p - ob\<parallel>\<^sub>\<infinity> \<and> 0 \<le> sp \<and> \<parallel>d\<parallel> = 1}"
  proof (rule hoare_fboxI, clarsimp)
    fix s
    assume "t<s> = 0" "A = a<s>" "0 \<le> sp<s>" "\<parallel>d<s>\<parallel> = 1"
       and safe_infl: "sp<s>^2 / (2 * b) + (a<s> / b + 1) * (a<s> * \<epsilon>\<^sup>2 / 2 + \<epsilon> * sp<s>) < \<parallel>p<s> - ob<s>\<parallel>\<^sub>\<infinity>"
    hence \<Psi>_s: "\<Psi> (p<s>, ob<s>, a<s>, sp<s>) s"
      by (simp add: \<Psi>_def eps_min infnorm_0 less_eq_real_def)
    show "( |dyn] (sp\<^sup>2 / (2 * b) < \<parallel>p - ob\<parallel>\<^sub>\<infinity> \<and> 0 \<le> sp \<and> \<parallel>d\<parallel> = 1)) s"
    proof (intro fboxI, simp, safe)
      fix s'
      assume s': "s' \<in> dyn s"
      hence \<Psi>_s': "\<Psi> (p<s>, ob<s>, a<s>, sp<s>) s'"
        by (smt (verit, best) SEXP_def \<Psi>_s s' dyn_inv fbox_def predicate1D)
      hence t_bnd: "t<s'> \<le> \<epsilon>" and sp_s': "sp<s'> = sp<s> + A * t<s'>"
        using \<open>A = a<s>\<close> by (auto simp add: \<Psi>_def)
      have "infnorm (p<s> - ob<s>) \<le> infnorm (p<s> - p<s'>) + infnorm (p<s'> - ob<s>)"
        by (smt (verit, best) add_diff_add add_diff_cancel_left' diff_diff_eq2 infnorm_triangle)
      also have "... = infnorm (p<s'> - p<s>) + infnorm (p<s'> - ob<s>)"
        using infnorm_sub by auto
      finally have dist_ineq: "infnorm (p<s> - ob<s>) - infnorm (p<s'> - p<s>) \<le> infnorm (p<s'> - ob<s>)" 
        by linarith
      have "infnorm (p<s'> - p<s>) \<le> t<s'> * sp<s> + A * (t<s'> ^ 2) / 2"
        using \<Psi>_s' \<open>A = a<s>\<close> by (auto simp add: \<Psi>_def field_simps)
      have "infnorm (p<s'> - p<s>) \<le> t<s'> * sp<s> + A * (t<s'> ^ 2) / 2"
        using \<Psi>_s' \<open>A = a<s>\<close> by (auto simp add: \<Psi>_def field_simps)
      also have "... \<le> \<epsilon> * sp<s> + A * (\<epsilon> ^ 2) / 2"
      proof -
        have term1: "t<s'> * sp<s> \<le> \<epsilon> * sp<s>"
          using t_bnd \<open>0 \<le> sp<s>\<close> by (simp add: mult_right_mono)
        
        have t_pos: "0 \<le> t<s'>" 
          using \<Psi>_s' by (auto simp add: \<Psi>_def)
        have t_sq: "t<s'> ^ 2 \<le> \<epsilon> ^ 2"
          by (simp add: power_mono t_bnd t_pos)
        have term2: "A * (t<s'> ^ 2) / 2 \<le> A * (\<epsilon> ^ 2) / 2"
          using t_sq A_min by (simp add: divide_right_mono mult_left_mono)          
        from term1 term2 show ?thesis by linarith
      qed
      finally have "infnorm (p<s'> - p<s>) \<le> \<epsilon> * sp<s> + A * (\<epsilon> ^ 2) / 2" .

      have h_bound: "infnorm (p<s'> - p<s>) \<le> (A * (\<epsilon> \<^sup>2) / 2 + \<epsilon> * sp<s>)"
        using \<open>infnorm (p<s'> - p<s>) \<le> \<epsilon> * sp<s> + A * (\<epsilon> ^ 2) / 2\<close> by (simp add: field_simps)

      from A_min b_min have key_algebraic_bound: "(sp<s> + A * t<s'>)^2 / (2*b) \<le> (sp<s>)^2 / (2*b) + (A/b) * (A * \<epsilon>^2 / 2 + \<epsilon> * sp<s>)"
      proof -
        have "(sp<s> + A * t<s'>)^2 = (sp<s>)^2 + 2 * A * t<s'> * sp<s> + A^2 * (t<s'>)^2"
          by (simp add: algebra_simps power2_eq_square)
        also have "... \<le> (sp<s>)^2 + 2 * A * \<epsilon> * sp<s> + A^2 * \<epsilon>^2"
        proof (intro add_mono)
          show "(sp<s>)\<^sup>2 \<le> (sp<s>)\<^sup>2" by simp
        next
          show "2 * A * t<s'> * sp<s> \<le> 2 * A * \<epsilon> * sp<s>"
            by (simp add: A_min \<open>0 \<le> sp<s>\<close> landau_o.R_mult_right_mono landau_omega.R_mult_left_mono t_bnd)
        next
          have "(t<s'>)^2 \<le> \<epsilon>^2"
            using \<Psi>_def \<Psi>_s' by auto 
          thus "A^2 * (t<s'>)^2 \<le> A^2 * \<epsilon>^2"
            using A_min by (simp add: mult_left_mono power2_eq_square)
        qed
        finally have "(sp<s> + A * t<s'>)^2 \<le> (sp<s>)^2 + 2 * A * \<epsilon> * sp<s> + A^2 * \<epsilon>^2" .
        hence "(sp<s> + A * t<s'>)^2 / (2*b) \<le> ((sp<s>)^2 + 2 * A * \<epsilon> * sp<s> + A^2 * \<epsilon>^2) / (2*b)"
          using b_min by (simp add: divide_right_mono)
        also from b_min have "... = (sp<s>)^2 / (2*b) + (A/b) * (A * \<epsilon>^2 / 2 + \<epsilon> * sp<s>)"
          by (simp add: field_simps)
        finally show ?thesis .
      qed

      show "(sp<s'>)\<^sup>2 / (2 * b) < \<parallel>p<s'> - ob<s'>\<parallel>\<^sub>\<infinity>"
      proof -
        have "ob<s'> = ob<s>" using \<Psi>_s' by (simp add: \<Psi>_def)
        have "(sp<s'>)^2 / (2*b) \<le> (sp<s>)^2 / (2*b) + (A/b) * (A * \<epsilon>^2 / 2 + \<epsilon> * sp<s>)"
          using sp_s' key_algebraic_bound by simp
        also have "... = (sp<s>)^2 / (2*b) + (A/b + 1) * (A * \<epsilon>^2 / 2 + \<epsilon> * sp<s>) - (A * \<epsilon>^2 / 2 + \<epsilon> * sp<s>)"
          by (simp add: algebra_simps)
        also have "... < infnorm (p<s> - ob<s>) - infnorm (p<s'> - p<s>)"
          using \<open>A = a<s>\<close> h_bound safe_infl by auto
        also have "... \<le> infnorm (p<s'> - ob<s>)"
          using dist_ineq by linarith
        finally show ?thesis using `ob<s'> = ob<s>` by simp
      qed

      show "0 \<le> sp<s'>" using \<Psi>_s' by (auto simp add: \<Psi>_def)
      show "\<parallel>d<s'>\<parallel> = 1" using \<Psi>_s' by (auto simp add: \<Psi>_def)
    qed
  qed
next
  show "`\<Phi> \<longrightarrow> \<phi>`"
    by expr_simp
next
  show "`\<phi> \<longrightarrow> \<psi>`"
    by expr_simp (metis arith_simps(62) b_min divide_less_eq infnorm_0 power2_less_0 rel_simps(51) verit_minus_simplify(1) zero_compare_simps(6))
qed
  
end

end