theory Dynamics_Difficult
  imports "Hybrid-Verification.Hybrid_Verification"
begin


dataspace basic_programs = 
  variables 
    w :: real
    x :: real
    y :: real
    z :: real

subsubsection \<open> 26. Dynamics: Open cases \<close>

lemma current_vderiv_ge_always_ge:
  fixes c::real
  assumes init: "c < x t\<^sub>0" and ode: "D x = x' on {t\<^sub>0..}" 
    and dhyp: "x' = (\<lambda>t. g (x t))" "\<forall>x\<ge>c. g x \<ge> 0"
  shows "\<forall>t\<ge>t\<^sub>0. x t > c"
  using first_derivative_test(1)[OF _ ode, unfolded dhyp, simplified]
proof-
  have cont: "continuous_on {t\<^sub>0..} x"
    using vderiv_on_continuous_on[OF ode] .
  {assume "\<exists>t\<ge>t\<^sub>0. x t \<le> c"
    hence inf: "{t. t > t\<^sub>0 \<and> x t \<le> c} \<noteq> {}" "bdd_below {t. t > t\<^sub>0 \<and> x t \<le> c}"
      using init less_eq_real_def unfolding bdd_below_def by force (rule_tac x=t\<^sub>0 in exI, simp)
    define t\<^sub>1 where t1_hyp: "t\<^sub>1 = Inf {t. t > t\<^sub>0 \<and> x t \<le> c}"
    hence "t\<^sub>0 \<le> t\<^sub>1"  
      using le_cInf_iff[OF inf, of t\<^sub>0] by auto
    have "x t\<^sub>1 \<ge> c"
    proof-
      {assume "x t\<^sub>1 < c"
        hence obs: "x t\<^sub>1 \<le> c" "x t\<^sub>0 \<ge> c" "t\<^sub>1 \<noteq> t\<^sub>0"
          using init by auto
        hence "t\<^sub>1 > t\<^sub>0"
          using \<open>t\<^sub>0 \<le> t\<^sub>1\<close> by auto
        then obtain k where k2_hyp: "k \<ge> t\<^sub>0 \<and> k \<le> t\<^sub>1 \<and> x k = c"
          using IVT2'[of "\<lambda>t. x t", OF obs(1,2) _ continuous_on_subset[OF cont]] by auto
        hence "t\<^sub>0 < k" "k < t\<^sub>1"
          using \<open>x t\<^sub>1 < c\<close> less_eq_real_def init by auto
        also have "t\<^sub>1 \<le> k"
          using cInf_lower[OF _ inf(2)] k2_hyp calculation unfolding t1_hyp by auto
        ultimately have False
          by simp}
      thus "x t\<^sub>1 \<ge> c"
        by fastforce
    qed
    hence obs: "\<forall>t\<in>{t\<^sub>0..<t\<^sub>1}. x t > c"
    proof-
      {assume "\<exists>t\<in>{t\<^sub>0..<t\<^sub>1}. x t \<le> c"
        then obtain k where k2_hyp: "k \<ge> t\<^sub>0 \<and> k < t\<^sub>1 \<and> x k \<le> c"
          by auto
        hence "k > t\<^sub>0"
          using \<open>x t\<^sub>0 > c\<close> less_eq_real_def by auto
        hence "t\<^sub>1 \<le> k"
          using cInf_lower[OF _ inf(2)] k2_hyp unfolding t1_hyp by auto
        hence "False"
          using k2_hyp by auto}
      thus "\<forall>t\<in>{t\<^sub>0..<t\<^sub>1}. x t > c"
        by force
    qed
    hence "\<forall>t\<in>{t\<^sub>0..t\<^sub>1}. x' t \<ge> 0"
      using \<open>x t\<^sub>1 \<ge> c\<close> dhyp(2) less_eq_real_def 
      unfolding dhyp by (metis atLeastAtMost_iff atLeastLessThan_iff) 
    hence "x t\<^sub>0 \<le> x t\<^sub>1"
      apply(rule_tac f="\<lambda>t. x t" and T="{t\<^sub>0..t\<^sub>1}" in has_vderiv_mono_test(1); clarsimp)
      using has_vderiv_on_subset[OF ode] apply force
      using \<open>t\<^sub>0  \<le> t\<^sub>1\<close>  by (auto simp: less_eq_real_def)
    hence "c < x t\<^sub>1"
      using \<open>x t\<^sub>1 \<ge> c\<close> init by auto
    then obtain \<epsilon> where eps_hyp: "\<epsilon> > 0 \<and> (\<forall>t\<in>ball t\<^sub>1 \<epsilon> \<inter> {t\<^sub>0..}. c < x t)"
      using continuous_on_Ex_ball_less'[of _ "\<lambda>t. x t", OF cont _ \<open>c < x t\<^sub>1\<close>] \<open>t\<^sub>0  \<le> t\<^sub>1\<close> by auto
    hence "\<forall>t\<in>{t\<^sub>0..<t\<^sub>1+\<epsilon>}. c < x t"
      using obs \<open>t\<^sub>0 \<le> t\<^sub>1\<close> ball_eq_greaterThanLessThan by auto
    hence "\<forall>t\<in>{t. t > t\<^sub>0 \<and> x t \<le> c}. t\<^sub>1+\<epsilon> \<le> t"
      by (metis (mono_tags, lifting) atLeastLessThan_iff less_eq_real_def mem_Collect_eq not_le)
    hence "t\<^sub>1+\<epsilon> \<le> t\<^sub>1"
      using le_cInf_iff[OF inf] unfolding t1_hyp by simp
    hence False
      using eps_hyp by auto}
  thus "\<forall>t\<ge>t\<^sub>0. c < x t"
    by fastforce
qed

lemma Collect_ge_ivl: "Collect ((\<le>) 0) = {(0::real)..}"
  by auto

context basic_programs
begin

lemma "0 \<le> N \<Longrightarrow> H{N < x} {x` = x} {N < x}"
  apply (clarsimp simp only: fbox_diff_inv_on diff_inv_on_eq)
  apply (expr_simp add: Collect_ge_ivl ivp_sols_def)
  using current_vderiv_ge_always_ge[of N _ 0 _ id]
  by auto

(* x^3>5 & y>2 -> [{x'=x^3+x^4, y'=5*y+y^2}](x^3>5 & y>2) *)
lemma "(x\<^sup>3 > 5 \<and> y > 2)\<^sub>e \<le> |{x` = x\<^sup>3 + x\<^sup>4, y` = 5*y + y\<^sup>2}] (x\<^sup>3 > 5 \<and> y > 2)"
  apply (intro hoare_invs)
  apply (expr_simp)
  apply (clarsimp simp only: fbox_diff_inv_on diff_inv_on_eq ivp_sols_def)
   apply (expr_simp add: Collect_ge_ivl)
  subgoal for s X t
    apply(rule current_vderiv_ge_always_ge[of 5 "\<lambda>t. (fst (X t))\<^sup>3" 0 
        "\<lambda>t. 3 * (fst (X t))\<^sup>2 * ((fst (X t))\<^sup>3 + (fst (X t))\<^sup>4)", 
        where g="\<lambda>t. 3 * t\<^sup>2 + 3 * (root 3 t)\<^sup>5", rule_format])
    by (auto intro!: vderiv_intros simp: odd_real_root_power_cancel split: if_splits) 
      (clarsimp simp: fun_eq_iff, ferrack)
  apply (clarsimp simp only: fbox_diff_inv_on diff_inv_on_eq ivp_sols_def)
   apply (expr_simp add: Collect_ge_ivl)
  by (rule current_vderiv_ge_always_ge[rule_format, of 2 "\<lambda>t. (snd (_ t))", 
        where g="\<lambda>t. 5 * t + t\<^sup>2"])
    (auto intro!: vderiv_intros simp: odd_real_root_power_cancel split: if_splits)


subsubsection \<open> 27. Dynamics: Closed cases \<close>

(* x>=1 & y=10 & z=-2 -> [{x'=y, y'=z+y^2-y & y>=0}](x>=1 & y>=0) *)
lemma "(x \<ge> 1 \<and> y = 10 \<and> z = - 2)\<^sub>e \<le> |{x` = y, y` =$z + y\<^sup>2 - y | y \<ge> 0}] (x \<ge> 1 \<and> y \<ge> 0)"
  apply (rule fbox_diff_invI[where I="(x \<ge> 1 \<and> y \<ge> 0)\<^sup>e"]; force?)
    apply (rule fbox_invs(1))
     apply expr_simp
    apply (simp only: expr_defs hoare_diff_inv_on fbox_diff_inv_on)
   apply (diff_inv_on_single_ineq_intro "(0)\<^sup>e" "(y)\<^sup>e"; expr_simp)
  apply (metis indeps(7) lens_plus_def plus_vwb_lens vwbs(2,3))
  by (force intro!: vderiv_intros)
    (expr_simp add: hoare_diff_inv_on fbox_diff_inv_on diff_inv_on_eq)

end


subsubsection \<open> 28. Dynamics: Conserved quantity \<close>

dataspace conserved_quantity =
  constants c::real
  variables x1::real x2::real

context conserved_quantity
begin

(* x1^4*x2^2+x1^2*x2^4-3*x1^2*x2^2+1 <= c ->
    [{x1'=2*x1^4*x2+4*x1^2*x2^3-6*x1^2*x2, x2'=-4*x1^3*x2^2-2*x1*x2^4+6*x1*x2^2}] 
   x1^4*x2^2+x1^2*x2^4-3*x1^2*x2^2+1 <= c *)
lemma "(x1\<^sup>4*x2\<^sup>2 + x1\<^sup>2*x2\<^sup>4 - 3*x1\<^sup>2*x2\<^sup>2 + 1 \<le> c)\<^sub>e \<le>
  |{x1` = 2*x1\<^sup>4*x2 + 4*x1\<^sup>2*x2\<^sup>3 - 6*x1\<^sup>2*x2, x2` = -4*x1\<^sup>3*x2\<^sup>2 - 2*x1*x2\<^sup>4 + 6*x1*x2\<^sup>2}]
  (x1\<^sup>4*x2\<^sup>2 + x1\<^sup>2*x2\<^sup>4 - 3*x1\<^sup>2*x2\<^sup>2 + 1 \<le> c)"
  by dInduct_auto

(* x1^4*x2^2+x1^2*x2^4-3*x1^2*x2^2+1 <= c ->
    [{x1'=2*x1^4*x2+4*x1^2*x2^3-6*x1^2*x2, x2'=-4*x1^3*x2^2-2*x1*x2^4+6*x1*x2^2}] 
   x1^4*x2^2+x1^2*x2^4-3*x1^2*x2^2+1 <= c *)
lemma "(x1\<^sup>4*x2\<^sup>2 + x1\<^sup>2*x2\<^sup>4 - 3*x1\<^sup>2*x2\<^sup>2 + 1 \<le> c)\<^sub>e \<le>
  |{x1` = 2*x1\<^sup>4*x2 + 4*x1\<^sup>2*x2\<^sup>3 - 6*x1\<^sup>2*x2, x2` = -4*x1\<^sup>3*x2\<^sup>2 - 2*x1*x2\<^sup>4 + 6*x1*x2\<^sup>2}]
  (x1\<^sup>4*x2\<^sup>2 + x1\<^sup>2*x2\<^sup>4 - 3*x1\<^sup>2*x2\<^sup>2 + 1 \<le> c)"
  apply (simp only: expr_defs hoare_diff_inv_on fbox_diff_inv_on)
  apply (diff_inv_on_single_ineq_intro "(0)\<^sup>e" "(0)\<^sup>e"; expr_simp)
  apply (intro vderiv_intros; (assumption)?, (rule vderiv_intros)?)
                      apply force+
  by (clarsimp simp: field_simps)

end


subsubsection \<open> 29. Dynamics: Darboux equality \<close>

lemma mult_abs_right_mono: "a < b \<Longrightarrow> a * \<bar>c\<bar> \<le> b * \<bar>c\<bar>" for c::real
  by (simp add: mult_right_mono)

lemma local_lipschitz_first_order_linear:
  fixes c::"real \<Rightarrow> real"
  assumes "continuous_on T c"
  shows "local_lipschitz T UNIV (\<lambda>t. (*) (c t))"
proof(unfold local_lipschitz_def lipschitz_on_def, clarsimp simp: dist_norm)
  fix x t::real assume "t \<in> T"
  then obtain \<delta> where d_hyp: "\<delta> > 0 \<and> (\<forall>\<tau>\<in>T. \<bar>\<tau> - t\<bar> < \<delta> \<longrightarrow> \<bar>c \<tau> - c t\<bar> < max 1 \<bar>c t\<bar>)"
    using assms unfolding continuous_on_iff 
    apply(erule_tac x=t in ballE, erule_tac x="max 1 (\<bar>c t\<bar>)" in allE; clarsimp)
    by (metis dist_norm less_max_iff_disj real_norm_def zero_less_one)
  {fix \<tau> x\<^sub>1 x\<^sub>2 
    assume "\<tau> \<in> cball t (\<delta>/2) \<inter> T" "x\<^sub>1 \<in> cball x (\<delta>/2)" "x\<^sub>2 \<in> cball x (\<delta>/2)" 
    hence "\<bar>\<tau> - t\<bar> < \<delta>" "\<tau> \<in> T"
      by (auto simp: dist_norm, smt d_hyp)
    hence "\<bar>c \<tau> - c t\<bar> < max 1 \<bar>c t\<bar>"
      using d_hyp by auto
    hence "- (max 1 \<bar>c t\<bar> + \<bar>c t\<bar>) < c \<tau> \<and> c \<tau> < max 1 \<bar>c t\<bar> + \<bar>c t\<bar>"
      by (auto simp: abs_le_eq)
    hence obs: "\<bar>c \<tau>\<bar> < max 1 \<bar>c t\<bar> + \<bar>c t\<bar>"
      by (simp add: abs_le_eq)
    have "\<bar>c \<tau> * x\<^sub>1 - c \<tau> * x\<^sub>2\<bar> = \<bar>c \<tau>\<bar> * \<bar>x\<^sub>1 - x\<^sub>2\<bar>"
      by (metis abs_mult left_diff_distrib mult.commute)
    also have "... \<le> (max 1 \<bar>c t\<bar> + \<bar>c t\<bar>) * \<bar>x\<^sub>1 - x\<^sub>2\<bar>"
      using mult_abs_right_mono[OF obs] by blast
    finally have "\<bar>c \<tau> * x\<^sub>1 - c \<tau> * x\<^sub>2\<bar> \<le> (max 1 \<bar>c t\<bar> + \<bar>c t\<bar>) * \<bar>x\<^sub>1 - x\<^sub>2\<bar>" .}
  hence "\<exists>L. \<forall>t\<in>cball t (\<delta>/2) \<inter> T. 0 \<le> L \<and>
    (\<forall>x\<^sub>1\<in>cball x (\<delta>/2). \<forall>x\<^sub>2\<in>cball x (\<delta>/2). \<bar>c t * x\<^sub>1 - c t * x\<^sub>2\<bar> \<le> L * \<bar>x\<^sub>1 - x\<^sub>2\<bar>)"
    by (rule_tac x="max 1 \<bar>c t\<bar> + \<bar>c t\<bar>" in exI, clarsimp simp: dist_norm)
  thus "\<exists>u>0. \<exists>L. \<forall>t\<in>cball t u \<inter> T. 0 \<le> L \<and> 
    (\<forall>xa\<in>cball x u. \<forall>y\<in>cball x u. \<bar>c t * xa - c t * y\<bar> \<le> L * \<bar>xa - y\<bar>)"
    apply(rule_tac x="\<delta>/2" in exI) 
    using d_hyp by auto
qed

lemma picard_lindeloef_first_order_linear: "t\<^sub>0 \<in> T \<Longrightarrow> open T \<Longrightarrow> is_interval T \<Longrightarrow> 
  continuous_on T c \<Longrightarrow> picard_lindeloef (\<lambda>t x::real. c t * x) T UNIV t\<^sub>0"
  apply(unfold_locales; clarsimp?)
   apply(intro continuous_intros, assumption)
  by (rule local_lipschitz_first_order_linear)

dataspace darboux =
  constants A::real B::real
  variables x::real y::real z::real w1::real w2::real

lemma darboux_arith: 
  (* x' + z' = A*x^2 + B*x + A*z*x + B*z = (A*x+B)*x + (A*x+B)*z = (A * x + B) * (x + z) *)
  "A * x\<^sup>2 + B * x + (A * z * x + B * z) = (A * x + B) * (x + z)" for x::real
  by (auto simp: field_simps)

context darboux
begin

(* x+z=0 -> [{x'=(A*x^2+B()*x), z' = A*z*x+B()*z}] 0=-x-z *)
lemma "(x + z = 0)\<^sub>e \<le> |{x` = A*x\<^sup>2 + \<guillemotleft>B\<guillemotright>*x, z` = A*z*x+B*z | G on UNIV UNIV @ 0}] (0= -x - z)"
  apply (subgoal_tac "(0= -x - z)\<^sup>e = (x + z = 0)\<^sup>e"; force?)
  apply (erule ssubst)
  apply (simp only: expr_defs hoare_diff_inv_on fbox_diff_inv_on fbox_diff_inv_on')
  apply (expr_simp add: diff_inv_on_eq ivp_sols_def, clarsimp)
  subgoal for s X t
    apply (rule picard_lindeloef.ivp_unique_solution[of "(\<lambda>t r. r * (A * (fst (X t)) + B))" 
          UNIV UNIV 0 "get\<^bsub>x\<^esub> s + get\<^bsub>z\<^esub> s" "\<lambda>s. UNIV" t 
          _ "\<lambda>t. 0"]; (clarsimp simp: ivp_sols_def)?)
      prefer 2 apply (intro vderiv_intros, force, force, force, force)
      apply (distribute, mon_pow_simp)
     prefer 2 apply (force intro!: vderiv_intros)
    apply (unfold_locales; clarsimp?)
     apply (force intro!: vderiv_on_continuous_on vderiv_intros)
    apply distribute
    apply (rule_tac f'="\<lambda>(t, r). Blinfun (\<lambda>r. r * (A * fst (X t)) + r * B) " 
        in c1_implies_local_lipschitz; clarsimp?)
    apply (rule has_derivative_Blinfun)
     apply (auto intro!: derivative_eq_intros vderiv_on_continuous_on split: prod.splits)[1]
    apply (rule continuous_on_blinfun_componentwise)
    apply (simp add: prod.case_eq_if)
    apply (subst bounded_linear_Blinfun_apply)
    subgoal for i w
      apply (rule_tac f="(\<lambda>r. r * (A * fst (X (fst w))) + r * B)" in has_derivative_bounded_linear)
      by (auto intro!: derivative_eq_intros)
    by (auto intro!: continuity_intros vderiv_on_continuous_on
        continuous_on_compose[of UNIV fst X, unfolded comp_def] )
  done

lemma "B \<noteq> 0 \<Longrightarrow> (x + z = 0)\<^sub>e \<le> |{x` = A*x\<^sup>2 + \<guillemotleft>B\<guillemotright>*x, z` = A*z*x+B*z}] (0= -x - z)"
  apply (subgoal_tac "(0= -x - z)\<^sup>e = (x + z = 0)\<^sup>e"; force?)
  apply (erule ssubst)
  apply (rule darboux_eq[where a="x +\<^sub>L z" and y=w1 and z=w2 and g="A * get\<^bsub>x\<^esub> _ + B"]; simp?)
  subgoal by expr_simp (metis indeps(15) indeps(6) lens_indep.lens_put_comm)
       apply expr_simp
  subgoal by expr_auto (metis vwb_lens.axioms(1) vwbs(4) wb_lens.axioms(1) weak_lens.put_get)
  subgoal by expr_auto 
      (smt (verit, ccfv_threshold) indeps(17) indeps(19) indeps(8) lens_indep.lens_put_comm)
    apply expr_simp
  prefer 2 subgoal
    by (intro ldifferentiable; simp?)
    apply (subst framed_derivs; simp?)
      apply (rule ldifferentiable; simp?)
    apply (rule ldifferentiable; simp?)
  apply (subst framed_derivs; simp?)
  apply (subst framed_derivs; simp?)
       apply expr_simp
    apply (subst darboux_arith)
    oops

lemma "B \<noteq> 0 \<Longrightarrow> (x + z = 0)\<^sub>e \<le> |{x` = A*x\<^sup>2 + \<guillemotleft>B\<guillemotright>*x, z` = A*z*x+B*z}] (0= -x - z)"
  (* find_local_flow *)
  apply (subst fbox_solve[where \<phi>="\<lambda>t. [
    x \<leadsto> - 1 * B * exp (B * t + B * $x) * (1 / (- 1 + A * exp (B * t + B * $x))), 
    z \<leadsto> exp (- 1 * B * (- 1 * (1 / B) * ln (exp (B * (t + $x))) + 
      1 / B * ln (- 1 + A * exp (B * (t + $x))))) * $z]"]; expr_simp?)
  subgoal
    apply (((clarsimp simp: local_flow_on_def)?, unfold_locales; clarsimp?))
    subgoal for s
      apply (expr_simp)
      apply (rule c1_local_lipschitz; clarsimp)
      apply (intro derivative_eq_intros)
                        (* apply auto *)
      sorry
    sorry
  apply (auto simp: field_simps le_fun_def)
  oops

end


subsubsection \<open> 30. Dynamics: Fractional Darboux equality \<close> (*N 30 *)

context darboux
begin

(* x+z=0 -> [{x'=(A*y+B()*x)/z^2, z' = (A*x+B())/z & y = x^2 & z^2 > 0}] x+z=0 *)
lemma "(x + z = 0)\<^sub>e \<le> |{x` = (A*y + B*x)/z\<^sup>2, z` = (A*x+B)/z | (y = x\<^sup>2 \<and> z\<^sup>2 > 0)}] (x + z = 0)"
  apply (rule diff_ghost_rule_very_simple[where y="w1" 
        and k="-(A*$x+B)/($z)\<^sup>2" and J="(x*w1 + z*w1 = 0 \<and> w1 \<noteq> 0)\<^sup>e"])
  defer
       apply expr_simp
  apply expr_simp
  using lens_indep_comm[of w1 z] lens_indep_comm[of w1 x] indeps  apply expr_auto
    apply expr_simp
   apply expr_auto
  apply(subst cross3_simps(23)[symmetric, of "get\<^bsub>x\<^esub> _" "get\<^bsub>w1\<^esub> _" "get\<^bsub>z\<^esub> _"])
    apply (auto simp: field_simps)[1]
    apply (metis (full_types) bgauge_existence_lemma get_put_put_indep indeps(11) 
      mem_Collect_eq verit_comp_simplify1(1) vwbs(4))
   apply (clarsimp simp: field_simps, simp add: factorR(1))
  oops
(* apply (dGhost "y" "(x*y\<^sup>2 = 1 \<or> x=0)\<^sub>e" "1/2") *)

(* x+z=0 -> [{x'=(A*y+B()*x)/z^2, z' = (A*x+B())/z & y = x^2 & z^2 > 0}] x+z=0 *)
lemma "(x + z = 0)\<^sub>e \<le> |{x` = (A*y + B*x)/z\<^sup>2, z` = (A*x+B)/z | (y = x\<^sup>2 \<and> z\<^sup>2 > 0)}] (x + z = 0)"
  apply (simp only: expr_defs hoare_diff_inv_on fbox_diff_inv_on fbox_diff_inv_on')
  apply (expr_simp add: diff_inv_on_eq ivp_sols_def, clarsimp)
  subgoal for s X t
    apply (rule picard_lindeloef.ivp_unique_solution[of "(\<lambda>t r. r * (A * (fst (X t)) + B)/(snd (X t))\<^sup>2)" 
          "(Collect ((\<le>) 0))" UNIV 0 "get\<^bsub>x\<^esub> s + get\<^bsub>z\<^esub> s" "\<lambda>s. {0--t}" t 
          _ "\<lambda>t. 0"]; (clarsimp simp: ivp_sols_def closed_segment_eq_real_ivl)?)
      prefer 3 subgoal
      apply (frule has_vderiv_on_subset[where T="{0..t}"]; clarsimp?)
      by (force intro!: vderiv_intros)
    prefer 2 subgoal
      apply (frule has_vderiv_on_subset[where T="{0..t}"]; clarsimp?)
      by (auto simp: field_simps intro!: vderiv_intros)
    apply (unfold_locales; clarsimp?) \<comment> \<open> set is not open \<close>
    oops

(* x+z=0 -> [{x'=(A*y+B()*x)/z^2, z' = (A*x+B())/z & y = x^2 & z^2 > 0}] x+z=0 *)
lemma "(x + z = 0)\<^sub>e \<le> |{x` = (A*y + B*x)/z\<^sup>2, z` = (A*x+B)/z | (y = x\<^sup>2 \<and> z\<^sup>2 > 0)}] (x + z = 0)"
  apply (rule darboux_eq[where a="x +\<^sub>L z" and y=w1 and z=w2]; simp?)
  subgoal by expr_simp (metis indeps(15) indeps(6) lens_indep.lens_put_comm)
       apply expr_simp
  subgoal by expr_auto (metis (full_types) exp_gt_zero linorder_not_le order.refl vwb_lens.axioms(1) 
        vwbs(4) wb_lens.axioms(1) weak_lens.put_get)
  subgoal by expr_auto (smt (verit, best) indeps(18) indeps(19) indeps(7) lens_indep.lens_put_comm)
  apply expr_auto
  prefer 2 subgoal
    by (intro ldifferentiable; simp?)
  apply (subst framed_derivs; simp?)
      apply (rule ldifferentiable; simp?)
    apply (rule ldifferentiable; simp?)
    apply (subst framed_derivs; simp?)
  apply (subst framed_derivs; simp?)
  apply expr_simp
  apply clarsimp
    oops
(* need to generalise darboux rules, otherwise requires picard-lindeloef for closed intervals *)

end


subsubsection \<open> 31. Dynamics: Darboux inequality \<close> (*N 31 *)

lemma darboux_ineq_arith:
  assumes "0 \<le> s\<^sub>1 + s\<^sub>2" and "0 \<le> (t::real)" and "t * s\<^sub>1 < 1"
  shows "0 \<le> s\<^sub>1 / (1 - t * s\<^sub>1) + (s\<^sub>2 - s\<^sub>1 * ln (1 - t * s\<^sub>1)) / (1 - t * s\<^sub>1)"
proof-
  have "s\<^sub>1 * ln (1 - t * s\<^sub>1) \<le> 0"
  proof(cases "s\<^sub>1 \<le> 0")
    case True
    hence "1 - t * s\<^sub>1 \<ge> 1"
      using \<open>0 \<le> t\<close> by (simp add: mult_le_0_iff)
    thus ?thesis
      using True ln_ge_zero mult_nonneg_nonpos2 by blast
  next
    case False
    hence "1 - t * s\<^sub>1 \<le> 1"
      using \<open>0 \<le> t\<close> by auto
    thus ?thesis
      by (metis False assms(3) diff_gt_0_iff_gt ln_le_zero_iff mult_le_0_iff nle_le)
  qed
  hence "s\<^sub>1 + s\<^sub>2 - s\<^sub>1 * ln (1 - t * s\<^sub>1) \<ge> s\<^sub>1 + s\<^sub>2"
    by linarith
  hence "(s\<^sub>1 + s\<^sub>2 - s\<^sub>1 * ln (1 - t * s\<^sub>1))/(1 - t * s\<^sub>1) \<ge> (s\<^sub>1 + s\<^sub>2)/(1 - t * s\<^sub>1)"
    using \<open>t * s\<^sub>1 < 1\<close> by (simp add: \<open>0 \<le> s\<^sub>1 + s\<^sub>2\<close> divide_right_mono)
  also have "(s\<^sub>1 + s\<^sub>2)/(1 - t * s\<^sub>1) \<ge> 0"
    using \<open>t * s\<^sub>1 < 1\<close> by (simp add: \<open>0 \<le> s\<^sub>1 + s\<^sub>2\<close>)
  ultimately show ?thesis
    by (metis (full_types) add_diff_eq add_divide_distrib order_trans)
qed

(* directly annotating the dynamics *)
locale darboux_ineq =
  fixes x::"real \<Longrightarrow> real^2"
    and y::real
    and z::"real \<Longrightarrow> real^2"
  assumes var_defs:
    "x \<equiv> vec_lens 1"
    "z \<equiv> vec_lens 2"
begin

lemma indeps: "x \<bowtie> z"
  unfolding var_defs
  by expr_auto+

lemma induct_2: "P 1 \<Longrightarrow> P 2 \<Longrightarrow> P (i::2)"
  using exhaust_2[of i]
  by auto

(* x+z>=0 -> [{x'=x^2, z' = z*x+y & y = x^2}] x+z>=0 *)
abbreviation (input) darboux_ineq_f2 :: "real ^ 2 \<Rightarrow> real ^ 2" ("f")
  where "f \<equiv> [x \<leadsto> x\<^sup>2, z \<leadsto> z*x + x\<^sup>2]"

abbreviation darboux_ineq_flow2 :: "real \<Rightarrow> real ^ 2 \<Rightarrow> real ^ 2" ("\<phi>")
  where "\<phi> t \<equiv> [x \<leadsto> x / (1 - t * x), z \<leadsto> (z - x * ln(1 - t * x))/(1 - t * x)]"

lemma darboux_flow_ivp: "(\<lambda>t. \<phi> t s) \<in> Sols ({t. 0 \<le> t \<and> t * x < 1})\<^sub>e UNIV (\<lambda>t. f) 0 s"
  apply (rule ivp_solsI; expr_auto add: var_defs)
  subgoal for i
  using var_defs exhaust_2[of i]
  by (cases "i=2"; cases "i=1")
    (auto simp: expr_simps lens_defs vec_upd_def fun_eq_iff
      add_divide_distrib power2_eq_square
      intro!: vderiv_intros split: if_splits)
  done

(* x+z>=0 -> [{x'=x^2, z' = z*x+y & y = x^2}] x+z>=0 *)
lemma "(x + z \<ge> 0)\<^sub>e \<le> |EVOL \<phi> (y = x\<^sup>2)\<^sub>e ({t. 0 \<le> t \<and> t * x < 1})\<^sub>e] (x + z \<ge> 0)"
  apply (subst fbox_g_evol)
  using var_defs darboux_ineq_arith
  by (clarsimp simp: expr_simps expr_defs)

no_notation darboux_ineq_f2 ("f") 
  and darboux_ineq_flow2 ("\<phi>")

end

context basic_programs
begin

(* attempt by providing solutions *)
(* x+z>=0 -> [{x'=x^2, z' = z*x+y & y = x^2}] x+z>=0 *)
lemma "(x + z \<ge> 0)\<^sub>e \<le> |{x` = x\<^sup>2, z` = z*x + y | y = x\<^sup>2}] (x + z \<ge> 0)"
  apply (subst fbox_g_ode_frame_flow[where 
        \<phi>="\<lambda>t. [x \<leadsto> x / (1 - t * x), z \<leadsto> (z - x * ln(1 - t * x))/(1 - t * x)]"])
  subgoal 
    apply (unfold local_flow_on_def, clarsimp)
    apply (unfold_locales; expr_simp)
    prefer 5 apply (auto simp: intro!: vderiv_intros)[1]
  oops (* local_flow's interval parameter should be a function *)

end


subsubsection \<open> 32. Dynamics: Bifurcation \<close>

lemma picard_lindeloef_dyn_bif: "continuous_on T (g::real \<Rightarrow> real) \<Longrightarrow> t\<^sub>0 \<in> T 
  \<Longrightarrow> is_interval T \<Longrightarrow> open T \<Longrightarrow> picard_lindeloef (\<lambda>t \<tau>::real. r + \<tau>^2) T UNIV t\<^sub>0"
proof(unfold_locales; clarsimp simp: dist_norm local_lipschitz_def lipschitz_on_def)
  fix x t::real
  {fix x1 and x2
    assume "x1 \<in>cball x 1" and "x2 \<in>cball x 1"
    hence leq: "\<bar>x - x1\<bar> \<le> 1" "\<bar>x - x2\<bar> \<le> 1"
      by (auto simp: dist_norm)
    have "\<bar>x1 + x2\<bar> = \<bar>x1 - x + x2 - x + 2 * x\<bar>"
      by simp
    also have "... \<le> \<bar>x1 - x\<bar> + \<bar>x2 - x\<bar> + 2 * \<bar>x\<bar>"
      using abs_triangle_ineq by auto
    also have "... \<le> 2 * (1 + \<bar>x\<bar>)"
      using leq by auto
    finally have obs: "\<bar>x1 + x2\<bar> \<le> 2 * (1 + \<bar>x\<bar>)" .
    also have "\<bar>x1\<^sup>2 - x2\<^sup>2\<bar> = \<bar>x1 + x2\<bar>*\<bar>x1 - x2\<bar>"
      by (metis abs_mult square_diff_square_factored power2_eq_square)
    ultimately have "\<bar>x1\<^sup>2 - x2\<^sup>2\<bar> \<le> (2 * (1 + \<bar>x\<bar>)) * \<bar>x1 - x2\<bar>"
      by (metis abs_ge_zero mult_right_mono)}
  thus "\<exists>u>0. (\<exists>\<tau>. \<bar>t - \<tau>\<bar> \<le> u \<and> \<tau> \<in> T) \<longrightarrow> 
  (\<exists>L\<ge>0. \<forall>xa\<in>cball x u. \<forall>y\<in>cball x u. \<bar>xa\<^sup>2 - y\<^sup>2\<bar> \<le> L * \<bar>xa - y\<bar>)"
    by (rule_tac x=1 in exI, clarsimp, rule_tac x="2 * (1 + \<bar>x\<bar>)" in exI, auto)
qed

context basic_programs
begin

(* r <= 0 -> \exists f (x=f -> [{x'=r+x^2}]x=f) *)
lemma "`\<guillemotleft>r\<guillemotright> \<le> 0` \<longrightarrow> (\<exists>f. (x=f)\<^sub>e \<le> |{x` = \<guillemotleft>r\<guillemotright> + x^2| True on UNIV UNIV @ 0}] (x=f))"
proof(clarsimp, rule_tac x="sqrt \<bar>r\<bar>" in exI, 
    clarsimp simp: hoare_diff_inv_on diff_inv_on_eq ivp_sols_def tsubst2vecf_eq)
  fix X::"real\<Rightarrow>real" and t::real and s::'st
  assume init: "X 0 = sqrt \<bar>r\<bar>" and "`r \<le> 0`"
     and D1: "D X = (\<lambda>t. get\<^bsub>x\<^esub> ([x \<leadsto> \<guillemotleft>r\<guillemotright> + ($x)\<^sup>2] (put\<^bsub>x\<^esub> s (X t)))) on UNIV"
  have "D X = (\<lambda>t. get\<^bsub>x\<^esub> ([x \<leadsto> \<guillemotleft>r\<guillemotright> + ($x)\<^sup>2] (put\<^bsub>x\<^esub> s (X t)))) on {0--t}"
    apply(rule has_vderiv_on_subset[OF D1])
    by (auto simp: closed_segment_eq_real_ivl)
  moreover have "continuous_on UNIV X"
    apply(rule vderiv_on_continuous_on)
    using D1 by assumption
  moreover have key: "D (\<lambda>t. sqrt (- r)) = (\<lambda>t. r + (sqrt (- r))\<^sup>2) on {0--t}"
    apply(subgoal_tac "(\<lambda>t. r + (sqrt (- r))\<^sup>2) = (\<lambda>t. 0)")
     apply(erule ssubst, rule vderiv_intros)
    using \<open>`r \<le> 0`\<close> by expr_auto
  moreover note picard_lindeloef.ivp_unique_solution[OF 
      picard_lindeloef_dyn_bif[OF calculation(2) UNIV_I is_interval_univ open_UNIV] 
      UNIV_I is_interval_closed_segment_1 subset_UNIV _ 
      ivp_solsI[of "X" _ "\<lambda>s. {0--t}" "sqrt (- r)" 0]
      ivp_solsI[of "\<lambda>t. sqrt (- r)" _], of t r]
  ultimately show "X t = sqrt \<bar>r\<bar>"
    using \<open>`r \<le> 0`\<close> init
    by expr_auto
qed

end



subsubsection \<open> 33. Dynamics: Parametric switching between two different damped oscillators \<close> (*N 33 *)

lemma dyn_param_switch_arith1:
  assumes hyp: "w\<^sup>2 * (y * a)\<^sup>2 + y\<^sup>2 \<le> c" 
    and w_hyp: "0 \<le> (w::real)" 
    and a_hyp: "- 2 \<le> a" "a \<le> 2" 
  shows "4 * w\<^sup>2 * (y * a)\<^sup>2 + y\<^sup>2 \<le> c * (16 * w\<^sup>2 + 1) / (4 * w\<^sup>2 + 1)" (is "?lhs \<le> ?rhs / ?factor")
  using assms apply -
  apply (subgoal_tac "?lhs \<le> ?rhs / ?factor \<longleftrightarrow> ?lhs * ?factor \<le> ?rhs")
   prefer 2
  subgoal by (smt (verit, best) pos_le_divide_eq realpow_square_minus_le)
  apply (erule ssubst)
  apply powers_simp
  apply ferrack
  apply clarsimp
  apply (subgoal_tac "16 * (w\<^sup>4 * (a\<^sup>2 * y\<^sup>2)) + (4 * (w\<^sup>2 * (a\<^sup>2 * y\<^sup>2)) + (4 * (w\<^sup>2 * y\<^sup>2) + (y\<^sup>2 - c - 16 * (c * w\<^sup>2)))) \<le> 0
  \<longleftrightarrow> 4 * (w\<^sup>4 * (a\<^sup>2 * y\<^sup>2)) + w\<^sup>2 * (a\<^sup>2 * y\<^sup>2) + (w\<^sup>2 * y\<^sup>2) - 4 * (c * w\<^sup>2) \<le> (c - y\<^sup>2) / 4")
   prefer 2 subgoal by powers_simp
  apply (erule ssubst)
  sorry

lemma dyn_param_switch_arith2: "w\<^sup>2 * (y * b)\<^sup>2 + y\<^sup>2 \<le> (c::real) \<Longrightarrow>
          0 \<le> w \<Longrightarrow>
          1 \<le> b\<^sup>2 * 3 \<Longrightarrow>
          (w / 2)\<^sup>2 * (y * b)\<^sup>2 + y\<^sup>2 \<le> c * ((w / 2)\<^sup>2 + 1) / (2 * (w / 2)\<^sup>2 + 1)"
  apply powers_simp
  apply ferrack
  sorry (* verified with the help of a CAS *)

dataspace dyn_param_switch =
  variables 
    x :: real 
    y :: real 
    w :: real
    c :: real
    d :: real

context dyn_param_switch
begin

(*     w>=0 & d>=0
  & -2<=a&a<=2
  & b^2>=1/3
  & w^2*x^2+y^2 <= c
->
  [{
    {x'=y, y'=-w^2*x-2*d*w*y};
    {  { ?(x=y*a); w:=2*w; d:=d/2; c := c * ((2*w)^2+1^2) / (w^2+1^2); }
    ++ { ?(x=y*b); w:=w/2; d:=2*d; c := c * (w^2+1^2) / ((2*w^2)+1^2); }
    ++ { ?true; } }
   }*@invariant(w^2*x^2+y^2<=c&d>=0&w>=0)
  ] w^2*x^2+y^2 <= c *)
lemma "(w \<ge> 0 \<and> d \<ge> 0 \<and> -2 \<le> a \<and> a \<le> 2 \<and> b\<^sup>2 \<ge> 1/3 \<and> w\<^sup>2*x\<^sup>2+y\<^sup>2 \<le> c)\<^sub>e \<le>
  |LOOP 
    {x` = y, y` = -w\<^sup>2*x-2*d*w*y}; 
    ((\<questiondown>x=y*a?; w ::=2*w; d::=d/2; c ::= c * ((2*w)\<^sup>2+1\<^sup>2) / (w\<^sup>2+1\<^sup>2))
    \<sqinter> (\<questiondown>x=y*b?; w ::=w/2; d::=2*d; c ::= c * (w\<^sup>2+1\<^sup>2) / ((2*w\<^sup>2)+1\<^sup>2)) 
    \<sqinter> \<questiondown>True?) 
  INV (w\<^sup>2*x\<^sup>2+y\<^sup>2 \<le> c \<and> d \<ge>0 \<and> w\<ge>0)
  ] (w\<^sup>2*x\<^sup>2+y\<^sup>2 \<le> c)"
  apply (subst change_loopI[where I="(w\<^sup>2*x\<^sup>2+y\<^sup>2 \<le> c \<and> d \<ge>0 \<and> w\<ge>0 \<and> -2 \<le> a \<and> a \<le> 2 \<and> b\<^sup>2 \<ge> 1/3)\<^sup>e"])
  apply (rule hoare_loopI)
    prefer 3 apply expr_simp
   prefer 2 apply expr_simp
  apply (rule_tac hoare_kcomp[where R="(w\<^sup>2*x\<^sup>2+y\<^sup>2 \<le> c \<and> 0 \<le> d \<and> 0 \<le> w \<and> -2 \<le> a \<and> a \<le> 2 \<and> b\<^sup>2 \<ge> 1/3)\<^sup>e"])
  prefer 2 using dyn_param_switch_arith1 dyn_param_switch_arith2
   apply (simp add: wlp; expr_auto)[1]
    apply (rule diff_cut_on_rule[where C="(0 \<le> d \<and> 0 \<le> w \<and> -2 \<le> a \<and> a \<le> 2 \<and> b\<^sup>2 \<ge> 1/3)\<^sup>e"])
         apply (rule hoare_invI[where I="(0 \<le> d \<and> 0 \<le> w \<and> -2 \<le> a \<and> a \<le> 2 \<and> b\<^sup>2 \<ge> 1/3)\<^sup>e"])
    apply (simp only: expr_defs hoare_diff_inv_on fbox_diff_inv_on)?
    apply (intro diff_inv_on_raw_conjI; (diff_inv_on_ineq "(0)\<^sup>e" "(0)\<^sup>e")?)
    apply (expr_simp add: le_fun_def)
  apply (expr_simp add: le_fun_def)
  apply (rule_tac I="(w\<^sup>2*x\<^sup>2+y\<^sup>2 \<le> c)\<^sup>e" in fbox_diff_invI)
    prefer 3 apply expr_simp
   prefer 2 apply (expr_simp add: le_fun_def)
  apply (simp only: expr_defs hoare_diff_inv_on fbox_diff_inv_on)?
  apply (diff_inv_on_single_ineq_intro "(2*w\<^sup>2*x*y+2*y*(-w\<^sup>2*x-2*d*w*y))\<^sup>e" "(0)\<^sup>e")
      apply (simp, simp)
    apply (auto simp: field_simps)[1]
  apply (auto simp: field_simps)[1]
  apply expr_simp
  by (auto intro!: vderiv_intros)

end


subsubsection \<open> 34. Dynamics: Nonlinear 1 \<close>

dataspace dyn_nonlinear = 
  constants a :: real
  variables x1::real x2::real

context dyn_nonlinear
begin
(* x^3 >= -1 -> [{x'=(x-3)^4+a & a>=0}] x^3>=-1 *)
lemma "(x1\<^sup>3 \<ge> -1)\<^sub>e \<le> |{x1` = (x1-3)\<^sup>4 + a | (a\<ge>0)}] (x1\<^sup>3 \<ge> -1)"
  by (diff_inv_on_ineq "(0)\<^sup>e" "(3*x1\<^sup>2*((x1-3)\<^sup>4 + a))\<^sup>e")

end


subsubsection \<open> 35. Dynamics: Nonlinear 2 \<close>

context dyn_nonlinear
begin

(* x1+x2^2/2=a -> [{x1'=x1*x2,x2'=-x1}]x1+x2^2/2=a *)
lemma "(x1 + x2\<^sup>2/2 = a)\<^sub>e \<le> |{x1` = x1 * x2, x2` = -x1}] (x1 + x2\<^sup>2/2 = a)"
  by (diff_inv_on_eq)

lemma "(x1 + x2\<^sup>2/2 = a)\<^sub>e \<le> |{x1` = x1 * x2, x2` = -x1}] (x1 + x2\<^sup>2/2 = a)"
  (* find_local_flow *)
  apply (subst fbox_solve[where \<phi>="\<lambda>t. [
    x1 \<leadsto> $x1 + - 1 * $x1 * (tanh (1 / 2 * (- 1 * 2 powr (1 / 2) * t * $x1 powr (1 / 2) + - 1 * $x1 powr (1 / 2) * $x2)))\<^sup>2,
    x2 \<leadsto> 2 powr (1 / 2) * ($x1 * (tanh (1 / 2 * (- 1 * 2 powr (1 / 2) * t * $x1 powr (1 / 2) + 
      - 1 * $x1 powr (1 / 2) * $x2)))\<^sup>2) powr (1 / 2)]"])
     apply (((clarsimp simp: local_flow_on_def)?, unfold_locales; clarsimp?); expr_auto)
  subgoal
    apply c1_lipschitz
    sorry
      apply (expr_auto add: )
  apply (auto intro!: vderiv_intros)
  apply (auto simp: fun_eq_iff)
  oops

end


subsubsection \<open> 36. Dynamics: Nonlinear 4 \<close>

context dyn_nonlinear
begin

(* x1^2/2-x2^2/2>=a -> [{x1'=x2+x1*x2^2, x2'=-x1+x1^2*x2 & x1>=0 & x2>=0}]x1^2/2-x2^2/2>=a *)
lemma "(x1\<^sup>2/2 - x2\<^sup>2/2 \<ge> a)\<^sub>e \<le> 
  |{x1` = x2 + x1*x2\<^sup>2, x2` = -x1 + x1\<^sup>2 * x2| (x1 \<ge> 0 \<and> x2 \<ge> 0)}] 
  (x1\<^sup>2/2 - x2\<^sup>2/2 \<ge> a)"
  apply (simp only: expr_defs hoare_diff_inv_on fbox_diff_inv_on)
  apply (diff_inv_on_single_ineq_intro "(0)\<^sup>e" "(x1 * (x2 + x1*x2\<^sup>2) - x2 * (-x1 + x1\<^sup>2 * x2))\<^sup>e"; expr_simp)
  by (auto simp: field_simps fun_eq_iff intro!: vderiv_intros split: if_splits)

end


subsubsection \<open> 37. Dynamics: Nonlinear 5 \<close>

context dyn_nonlinear
begin

(* -x1*x2>=a -> [{x1'=x1-x2+x1*x2, x2'=-x2-x2^2}]-x1*x2>=a *)
lemma "(-x1*x2 \<ge> a)\<^sub>e \<le> |{x1` = x1 - x2 + x1*x2, x2` = -x2 - x2\<^sup>2}] (-x1*x2 \<ge> a)"
  apply (simp only: expr_defs hoare_diff_inv_on fbox_diff_inv_on)
  by (diff_inv_on_single_ineq_intro "(0)\<^sup>e" "((- x1 + x2 - x1*x2)*x2 - x1 * (-x2 - x2\<^sup>2))\<^sup>e"; expr_simp)
    (auto simp: field_simps fun_eq_iff intro!: vderiv_intros split: if_splits)

lemma "(-x1*x2 \<ge> a)\<^sub>e \<le> |{x1` = x1 - x2 + x1*x2, x2` = -x2 - x2\<^sup>2}] (-x1*x2 \<ge> a)"
  (* find_local_flow *)
  apply (subst fbox_solve[where \<phi>="\<lambda>t. [
    x1 \<leadsto> (- 1 * exp t + exp ($x1)) * $x2 
      + exp (- 1 * $x1) * (- 1 * exp t + exp ($x1)) * (exp ($x1) * (1 / (- 1 * exp t + exp ($x1))) 
        + ln (exp t) + - 1 * ln (- 1 * exp t + exp ($x1))),
    x2 \<leadsto> - 1 * exp ($x1) * (1 / (- 1 * exp t + exp ($x1)))]"]; expr_simp?)
   apply (((clarsimp simp: local_flow_on_def)?, unfold_locales; clarsimp?))
  subgoal
    apply expr_simp
    apply (rule c1_local_lipschitz; clarsimp)
    sorry
  subgoal for s t a b
    apply (expr_simp)
    apply (auto intro!: vderiv_intros)
    sorry
  subgoal for s a b
    apply (expr_auto add: field_simps)
    sorry
  apply expr_auto
  oops

end


subsubsection \<open> 38. Dynamics: Riccati \<close>

context basic_programs
begin

(* 2*x^3 >= 1/4 -> [{x'=x^2+x^4}] 2*x^3>=1/4 *)
lemma "(2*x\<^sup>3 \<ge> 1/4)\<^sub>e \<le> |{x` = x\<^sup>2 + x^4}] (2*x\<^sup>3 \<ge> 1/4)"
  by (diff_inv_on_ineq "(0)\<^sup>e" "(6*x\<^sup>2*(x\<^sup>2 + x^4))\<^sup>e")

end


subsubsection \<open> 39. Dynamics: Nonlinear differential cut \<close>

context basic_programs
begin

(* apply (subst fbox_solve[where \<phi>="\<lambda>t. [x \<leadsto> x * exp t]"]; clarsimp?) *)
term "\<lambda>t. [y \<leadsto> y/(1 - y * t)]"
term "(x\<^sup>4 - 12 * x\<^sup>3 + 54 * x\<^sup>2 - 108 * x + 81)\<^sub>e"

(* x^3 >= -1 & y^5 >= 0 -> [{x'=(x-3)^4+y^5, y'=y^2}] (x^3 >= -1 & y^5 >= 0) *)
lemma "(x\<^sup>3 \<ge> -1 \<and> y\<^sup>5 \<ge> 0)\<^sub>e \<le> |{x` = (x-3)\<^sup>4+y\<^sup>5, y` = y\<^sup>2}] (x\<^sup>3 \<ge> -1 \<and> y\<^sup>5 \<ge> 0)"
  apply (diff_cut_ineq "(0 \<le> y\<^sup>5)\<^sup>e" "(0)\<^sup>e" "(5*y\<^sup>4*y\<^sup>2)\<^sup>e")
  apply (diff_cut_ineq "(-1 \<le> x\<^sup>3)\<^sup>e" "(0)\<^sup>e" "(3*x\<^sup>2*((x-3)\<^sup>4+y\<^sup>5))\<^sup>e")
  by (rule diff_weak_on_rule, expr_auto)

end


end