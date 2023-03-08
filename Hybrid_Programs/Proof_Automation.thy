(**)
section \<open> Tactics \<close>

text \<open> We provide some tactics for easier interaction with proofs about real arithmetic.\<close>

theory Proof_Automation
  imports 
    Diff_Dyn_Logic
    "HOL-Eisbach.Eisbach"

begin

method hol_intros = (intro allI conjI impI iffI)

method hol_clarsimp uses simp = (hol_intros; (clarsimp simp: simp)?)


subsection \<open> Monomial simplification \<close>

method move_left for x::"'a::{ab_semigroup_mult,power}" = (
    (simp only: mult.assoc[symmetric])?, (* prepare for main loop *)
    (
      (simp only: mult.commute[where b="x^_"] mult.commute[where b="x"])?,
      (simp only: mult.assoc)
      )+
    ), (simp only: mult.assoc[symmetric])? (* clean after main loop *)

method move_right for x::"'a::{ab_semigroup_mult,power}" = (
    (simp only: mult.assoc)?,
    (
      (simp only: mult.commute[where a="x^_"] mult.commute[where a="x"])?,
      (simp only: mult.assoc[symmetric])+
      )+
    ), (simp only: mult.assoc[symmetric])?


named_theorems mon_pow_simps "simplification rules for powers in monomials "

declare semiring_normalization_rules(27) [mon_pow_simps] (* x * x ^ q = x ^ Suc q *)
    and semiring_normalization_rules(28) [mon_pow_simps] (* x ^ q * x = x ^ Suc q *)
    and semiring_normalization_rules(29) [mon_pow_simps] (* x * x = ?x\<^sup>2 *)

method mon_pow_simp = (
    (simp add: mon_pow_simps del: power_Suc)?,
    (simp only: mult.assoc)?,
    (simp add: mon_pow_simps del: power_Suc)?
    ) \<comment> \<open> simplifies powers in monomials \<close>

lemma "x * x * x * (y ^ Suc n * x * z * (y * x * z) * z * z) * z * z 
  = x ^ 5 * y ^ Suc (Suc n) * z ^ 6" for x::real
  apply (move_left z)
  apply (move_left y)
  apply (move_left x)
  apply mon_pow_simp
  done

lemma "x * x * x * (y\<^sup>2 * x * z * (y * x * z) * z * z) * z * z 
  = x ^ 5 * y ^ 3 * z ^ 6" for x::real
  apply (move_right x)
  apply (move_right y)
  apply (move_right z)
  apply mon_pow_simp
  done

method mon_simp_vars for x y::"'a::{ab_semigroup_mult,power}" = (
    (move_right x)?, (move_right y)?, mon_pow_simp?
    (* second argument should not be the right-most argument in a monomial *)
    )

lemma "x * x * (x:: real) * (y^2 * x * z * (y * x * z) * z * z) * z * z 
  = x^5 * y^3 * z^6"
  by (mon_simp_vars x y)

lemma "y  * x * x * (x:: real) * (w * y^2 * x * z * (y * x * z) * z * w^4 * z) * z * z 
  = x^5 * y^4 * z^6 * w^5"
  by (mon_simp_vars x y) (mon_simp_vars z w) 

lemma "x * x * (x:: real) * (y^(Suc n) * x * z * (y * x * z) * z * z) * z * z 
  = x^5 * y^(Suc (Suc n)) * z^6"
  by (mon_simp_vars x y)

method bin_unfold = (simp add: power2_diff power2_sum power_mult_distrib)


subsection \<open> Distribution of multiplication over addition \<close>

lemma sign_distrib_laws: 
  shows "- (a + b) = - a - (b::'a::ab_group_add)"
  and "- (a - b) = - a + b"
  and "- (- a + b) = a - b"
  and "- (- a - b) = a + b"
  and "a - (b + c) = a - b - c"
  and "a - (b - c) = a - b + c"
  and "a - (- b + c) = a + b - c"
  and "a - (- b - c) = a + b + c"
  by simp_all

method distribute = (
    ((subst sign_distrib_laws)+)?,
    ((subst (asm) sign_distrib_laws)+)?,
    ((subst minus_mult_left)+)?, (* - (a * b) = - a * b *)
    ((subst (asm) minus_mult_left)+)?,
    ((subst ring_distribs)+)?,
    ((subst (asm) ring_distribs)+)?
    )

method distributes = (distribute, simp) \<comment> \<open> can be iterated \<close>

(* work left to do in methods below *)

lemma factorR: 
  fixes a::real
  shows "a * b + a * c = (b + c) * a"
    and "b * a + a * c = (b + c) * a"
    and "a * b + c * a = (b + c) * a"
    and "b * a + c * a = (b + c) * a"
  by distributes+

lemma factorL: 
  fixes a::real
  shows "a * b + a * c = a * (b + c)"
    and "b * a + a * c = a * (b + c)"
    and "a * b + c * a = a * (b + c)"
    and "b * a + c * a = a * (b + c)"
  by distributes+

lemma factor_fracR: 
  fixes a::real
  assumes "c > 0"
  shows "a / c + b = (a + c * b) * (1 / c)"
    and "a + b / c = (c * a + b) * (1 / c)"
    and "a / c - b = (a - c * b) * (1 / c)"
    and "a - b / c = (c * a - b) * (1 / c)"
    and "- a / c + b = (- a + c * b) * (1 / c)"
    and "- a + b / c = (- c * a + b) * (1 / c)"
    and "- a / c - b = (a + c * b) * (- (1 / c))"
    and "- a - b / c = (c * a + b) * (- (1 / c))"
  using assms by distributes+

lemma "(36::real) * (x1\<^sup>2 * (x1 * x2 ^ 3)) - (- (24 * (x1\<^sup>2 * x2) * x1 ^ 3 * x2\<^sup>2) 
  - 12 * (x1\<^sup>2 * x2) * x1 * x2 ^ 4) - 36 * (x1\<^sup>2 * (x2 * x1)) * x2\<^sup>2 - 12 * (x1\<^sup>2 * (x1 * x2 ^ 5)) 
  = 24 * (x1 ^ 5 * x2 ^ 3)" (is "?t1 - (- ?t2 - ?t3) - ?t4 - ?t5 = ?t6")
  apply distribute
  apply (move_right x1)
  apply (move_right x2)
  apply mon_pow_simp
  done

lemma "0 \<le> A \<Longrightarrow> 0 < b \<Longrightarrow> x2\<^sup>2 \<le> 2 * b * (m - x1) \<Longrightarrow> 0 \<le> (t::real) 
  \<Longrightarrow> \<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> b * \<tau> \<le> x2 \<and> \<tau> \<le> \<epsilon> 
  \<Longrightarrow> (x2 - b * t)\<^sup>2 \<le> 2 * b * (m - (x2 * t - b * t\<^sup>2 / 2 + x1))"
  apply bin_unfold
  apply distributes
  apply (mon_simp_vars b t)
  done

lemma "a * (b / c) = (a * b) / c" for a::real
  oops

lemma STTexample6_arith:
  assumes "0 < A" "0 < B" "0 < \<epsilon>" "0 \<le> x2" "0 \<le> (t::real)" "- B \<le> k" "k \<le> A"
    and key: "x1 + x2\<^sup>2 / (2 * B) + (A * (A * \<epsilon>\<^sup>2 / 2 + \<epsilon> * x2) / B + (A * \<epsilon>\<^sup>2 / 2 + \<epsilon> * x2)) \<le> S" (is "?k3 \<le> S")
    and ghyp: "\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> 0 \<le> k * \<tau> + x2 \<and> \<tau> \<le> \<epsilon>"
  shows "k * t\<^sup>2 / 2 + x2 * t + x1 + (k * t + x2)\<^sup>2 / (2 * B) \<le> S" (is "?k0 \<le> S")
  using assms
  apply -
  apply distribute
  apply (subst factor_fracR[where c="2 * B"], simp?)
  apply (subst (asm) factor_fracR[where c="2 * B"], simp?)
  apply (mon_simp_vars A B)
  apply (subst (asm) factor_fracR[where c="2"], simp?)
  apply mon_pow_simp
  apply (subst (asm) factor_fracR[where c="2"], simp?)
  apply mon_pow_simp
  apply (subst (asm) factor_fracR[where c="2 * B"], simp?)
  apply mon_pow_simp
  apply (subst (asm) factor_fracR[where c="2 * B"], simp?)
  apply mon_pow_simp
  apply (subst (asm) factor_fracR[where c="2"], simp?)
  apply mon_pow_simp
  apply (move_right A)
  apply mon_pow_simp
  apply distribute
  apply bin_unfold
  apply mon_pow_simp
  oops


subsection \<open> Hoare Logic \<close>

text \<open> A simple tactic for Hoare logic that uses weakest liberal precondition calculations \<close>

(* Formally, this is not Hoare logic, rename? *)
method hoare_wp_simp uses local_flow = ((rule_tac hoare_loopI)?; simp add: unrest_ssubst 
    var_alpha_combine wp usubst usubst_eval 
    refine_iff_implies fbox_g_dL_easiest[OF local_flow])

method hoare_wp_auto uses local_flow = (hoare_wp_simp local_flow: local_flow; expr_auto)


subsection \<open> Derivative certification \<close>

method vderiv = ((expr_simp)?; force intro!: vderiv_intros simp: vec_eq_iff field_simps)


subsection \<open> Differential invariance \<close>

method diff_inv_on_single_eq_intro = 
  (rule diff_inv_on_eqI
  | rule diff_inv_on_raw_eqI
  ) \<comment> \<open> applies @{term diff_inv_on}-rule \<close>

method diff_inv_on_eq = (
    (simp only: expr_defs hoare_diff_inv_on fbox_diff_inv_on)?, 
    (diff_inv_on_single_eq_intro; expr_auto),
    (force simp: power2_eq_square intro!: vderiv_intros)?)

method diff_inv_on_single_ineq_intro for dnu dmu::"'a \<Rightarrow> real" = 
  (rule diff_inv_on_leqI[where \<mu>'=dmu and \<nu>'=dnu]
  | rule diff_inv_on_lessI[where \<mu>'=dmu and \<nu>'=dnu]
  | rule diff_inv_on_raw_leqI[where \<mu>'=dmu and \<nu>'=dnu]
  | rule diff_inv_on_raw_lessI[where \<mu>'=dmu and \<nu>'=dnu]
  ) \<comment> \<open> applies @{term diff_inv_on}-rule \<close>

method diff_inv_on_ineq for dnu dmu::"'a \<Rightarrow> real" = (
    (simp only: expr_defs hoare_diff_inv_on fbox_diff_inv_on)?, 
    diff_inv_on_single_ineq_intro dnu dmu;
    (force intro!: vderiv_intros)?)

method diff_inv_on_weaken_ineq for I::"'a \<Rightarrow> bool" 
  and dLeq dGeg::"'a \<Rightarrow> real" = (
    (rule fbox_inv[where I=I]),
    (expr_simp add: le_fun_def),
    (diff_inv_on_ineq dLeq dGeg),
    vderiv,
    (expr_simp add: le_fun_def)
    )

method diff_cut_ineq for I::"'a \<Rightarrow> bool" (* create tactic move to guard where nmods... *)
  and dLeq dGeg::"'a \<Rightarrow> real" = (
    (rule diff_cut_on_rule[where C=I]),
    (diff_inv_on_weaken_ineq I dLeq dGeg)
    )

text \<open> A first attempt at a high-level automated proof strategy using differential induction.
  A sequence of commands is tried as alternatives, one by one, and the method then iterates. \<close>

method dDiscr = (rule_tac nmods_invariant[OF nmods_g_orbital_on_discrete']; unrest)

method dInduct = (subst dInduct_hoare_diff_inv_on fbox_diff_inv_on; 
    rule_tac lderiv_rules; 
    simp add: framed_derivs ldifferentiable closure usubst unrest_ssubst unrest usubst_eval)

method dInduct_auto = (dInduct; expr_simp; auto simp add: field_simps)

method dWeaken = (rule_tac diff_weak_on_rule; expr_simp; auto simp add: field_simps)

method dInduct_mega uses facts = 
  ( fact facts \<comment> \<open> (1) Try any facts we have provided \<close>
  | (dWeaken ; force) \<comment> \<open> (2) Try differential weakening \<close>
  | rule_tac diff_cut_on_split' | rule_tac diff_cut_on_split \<comment> \<open> (4) Try differential cut (two options) \<close>
  | rule_tac hoare_if_then_else_inv
  | (dInduct_auto) \<comment> \<open> (5) Try differential induction \<close>
  )+

method dInduct_mega' uses facts = 
  ( fact facts \<comment> \<open> (1) Try any facts we have provided \<close>
  | (dWeaken ; force) \<comment> \<open> (2) Try differential weakening \<close>
  | rule_tac diff_cut_on_split' | rule_tac diff_cut_on_split \<comment> \<open> (4) Try differential cut (two options) \<close>
  | rule_tac hoare_if_then_else_inv
  | (dDiscr ; force) \<comment> \<open> (3) Try proving as a discrete invariant \<close>
  | (dInduct_auto) \<comment> \<open> (5) Try differential induction \<close>
  )+


subsection \<open> Differential ghosts \<close>

method dGhost for y :: "real \<Longrightarrow> 's" and J :: "'s \<Rightarrow> bool" and k :: real 
  = (rule diff_ghost_rule_very_simple[where y="y" and J="J" and k="k"]
    ,simp_all add: unrest usubst usubst_eval unrest_ssubst liberate_as_subst)


subsection \<open> Certification of existence and uniqueness \<close>

thm fbox_g_ode_frame_flow fbox_solve fbox_g_dL_easiest
(* most used solution theorems in arch2022:
  * fbox_g_ode_frame_flow
  * fbox_solve (which is essentially the one above)
  * fbox_g_dL_easiest (which transforms g_dl_ode_frames into g_evol_ons)
*)

method lipschitz for L :: real = 
  (unfold local_lipschitz_on_def local_lipschitz_def lipschitz_on_def dist_norm, clarify, 
    rule exI[where x="L"], expr_auto, (rule exI[where x="L"], auto)?)

method lens_c1_lipschitz for df uses typeI =
 ((rule_tac \<DD>=df in c1_local_lipschitz; expr_auto), fastforce intro: typeI intro!: derivative_intros, 
   fastforce intro: typeI continuous_intros)

method local_flow for L :: real =
  ((auto simp add: local_flow_on_def)?, (unfold_locales, auto), (lipschitz L, vderiv, expr_auto))

method local_flow_auto =
  (local_flow "1/4" | local_flow "1/2" | local_flow "1" | local_flow "2")


subsection \<open> Full proof automation \<close>

text \<open> First attempt at a system level prover \<close>

method dProve = (rule_tac hoare_loop_seqI, hoare_wp_auto, dInduct_mega', (expr_auto)+)


end
(**)