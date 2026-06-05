theory Obstacle_Avoidance
  imports "Hybrid-Verification.Hybrid_Verification" (* "Explorer.Explorer" *)
begin

(* setup Explorer_Lib.switch_to_quotes *)

unbundle Hybrid_Program_Syntax

declare [[literal_variables=false]]

lemma fbox_kstarI:
  assumes "I s" "\<And> s\<^sub>0. I s\<^sub>0 \<Longrightarrow> fbox C I s\<^sub>0" "\<And> s\<^sub>0. I s\<^sub>0 \<Longrightarrow> Q s\<^sub>0" 
  shows "fbox (C\<^sup>*) Q s"
  by (metis (mono_tags, opaque_lifting) SEXP_def assms(1,2,3) fbox_iso fbox_kstar_inv
      le_bool_def le_funD predicate1I)


lemma hl_pre_ghost: 
  assumes "\<And> x. H{\<guillemotleft>x\<guillemotright> = e \<and> P} C {Q}"
  shows "H{P} C {Q}"
  using assms by fastforce

lemma hl_middle_state:
  assumes "\<And> x. H{P} C\<^sub>1 {\<guillemotleft>x\<guillemotright> = e \<longrightarrow> @(I x)}" "\<And> x. H{\<guillemotleft>x\<guillemotright> = e \<and> @(I x)} C\<^sub>2 {Q}"
  shows "H{P} C\<^sub>1 ; C\<^sub>2 {Q}"
  using assms 
  apply (simp add: fbox_kcomp)
  apply (auto simp add: fbox_def SEXP_def)
  using le_bool_def le_funD by fastforce

declare [[literal_variables]]

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

lemma safety_from_Psi:
  assumes "opc \<noteq> obc" "\<Psi> (opc, obc, 0, 0) s'"
  shows "\<psi> s'"
proof -
  have "\<parallel>p<s'> - opc\<parallel>\<^sub>\<infinity> \<le> 0"
    using assms by (auto simp add: \<Psi>_def safety_condition_def)
  hence "\<parallel>p<s'> - opc\<parallel>\<^sub>\<infinity> = 0"
    using infnorm_pos_le verit_la_disequality by blast
  hence "p<s'> = opc"
    by (meson eq_iff_diff_eq_0 infnorm_eq_0)
  with assms have sep_eq:"\<parallel>p<s'> - ob<s'>\<parallel> = \<parallel>opc - obc\<parallel>"
    by (simp add: \<Psi>_def)
  from assms have old_sep: "0 < \<parallel>opc - obc\<parallel>"
    by (simp add: \<Psi>_def)
  show ?thesis
    apply (simp add: safety_condition_def)
    using old_sep sep_eq by force
qed

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

lemma fbox_choiceI:
  assumes "fbox C\<^sub>1 P s" "fbox C\<^sub>2 P s"
  shows "fbox (C\<^sub>1 \<sqinter> C\<^sub>2) P s"
  by (metis (lifting) SEXP_def assms(1,2) fbox_choice)

declare [[literal_variables=false]]

lemma hl_fboxI: 
  assumes "\<And> s. (P)\<^sub>e s \<Longrightarrow> fbox C (Q)\<^sub>e s"
  shows "H{P} C {Q}"
  using assms by blast

lemma fboxI:
  assumes "\<And> s'. \<lbrakk> s' \<in> C s \<rbrakk> \<Longrightarrow> P s'"
  shows "fbox C P s"
  by (simp add: assms fbox_def)

lemma exec_assign: 
  assumes "vwb_lens x" "\<And> s' x\<^sub>0. \<lbrakk> (get\<^bsub>x\<^esub> s' = e s); s = put\<^bsub>x\<^esub> s' x\<^sub>0 \<rbrakk> \<Longrightarrow> fbox C P s'" 
  shows "fbox (x := e ; C) P s"
  using assms 
  by (simp add: fbox_def prog_defs expr_defs)
     (metis mwb_lens_weak vwb_lens.put_eq vwb_lens_mwb weak_lens.put_get)

declare [[literal_variables]]

theorem static_safety: "H{\<Phi>} model1 {\<psi>}"
proof (unfold model1_def, kstar "loop_invariant", simp add: ctrl_def loop_invariant_def safe_def, symbolic_exec, simp_all)
  show "H{t = 0 \<and> \<omega> = 0 \<and> a = 0 \<and> sp\<^sup>2 / (2 * b) < \<parallel>p - ob\<parallel>\<^sub>\<infinity> \<and> 0 \<le> sp \<and> \<parallel>d\<parallel> = 1 \<and> sp = 0} 
          dyn 
         {sp\<^sup>2 / (2 * b) < \<parallel>p - ob\<parallel>\<^sub>\<infinity> \<and> 0 \<le> sp \<and> \<parallel>d\<parallel> = 1}"
  proof (rule hl_fboxI, clarsimp)
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
  proof (rule hl_fboxI, clarsimp)
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
      have hgoal : "(sp<s> + -(b * t<s'>)) ^ 2 / (2 * b) < infnorm (p<s'> - ob<s>)"
        sorry
      thus "(sp<s'>)\<^sup>2 / (2 * b) < \<parallel>p<s'> - ob<s'>\<parallel>\<^sub>\<infinity>"
      sorry
(*
    apply (rule hl_middle_state[where e="((p, ob, a, s))\<^sup>e" and I="\<Psi>"])
     apply (simp add: ctrl_def safe_def loop_invariant_def \<Psi>_def)
     apply wlp_simp
     apply (smt (verit, del_insts) eps_min infnorm_0)
  subgoal for vs
    apply (case_tac vs)
    subgoal for opc obc ac osc
      apply (rule hoare_invI[where I="\<Psi> vs"])
      apply simp
      using dyn_inv apply auto[1]
      apply simp
    apply expr_auto
     apply (simp add: ctrl_def safe_def loop_invariant_def \<Psi>_def)
    apply expr_simp
    apply auto[1]
  oops
*)
  

end

end