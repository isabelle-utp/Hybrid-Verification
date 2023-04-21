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


subsection \<open> Derivative certification \<close>

method vderiv_single uses simp intro 
  = (auto intro!: vderiv_intros intro simp: field_simps simp)[1]

method vderiv uses simp intro 
  = ((expr_simp)?; 
    force intro!: vderiv_intros intro simp: vec_eq_iff field_simps simp)


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

method dDiscr = (rule_tac nmods_invariant; auto intro!: closure)

(* hoare_diff_inv_on' *)
method dInduct = ((intro hoare_invs)?; subst fbox_diff_inv_on; 
    intro lderiv_rules; 
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
  = (rule diff_ghost_rule_very_simple[where y="y" and J="J" and k="k"],
    simp_all add: unrest usubst usubst_eval unrest_ssubst liberate_as_subst)


subsection \<open> Continuity \<close>

named_theorems continuity_intros "optimised compilation of continuity rules."

declare continuous_on_const [continuity_intros]
    and continuous_on_id [continuity_intros]
    and continuous_on_add [continuity_intros]
    and continuous_on_diff [continuity_intros]
    and continuous_on_mult [continuity_intros]
    and continuous_on_ln [continuity_intros]
    and continuous_on_minus [continuity_intros]
    and continuous_on_power [continuity_intros]
    and continuous_on_divide [continuity_intros]
    and continuous_on_cos [continuity_intros]
    and continuous_on_sin [continuity_intros]
    and continuous_on_exp [continuity_intros]
    and continuous_on_Pair [continuity_intros]
    and continuous_on_fst [continuity_intros]
    and continuous_on_snd [continuity_intros]
    and continuous_on_scaleR [continuity_intros]
    and continuous_on_inverse [continuity_intros]

lemma continuous_on_divideR: "continuous_on T f \<Longrightarrow> continuous_on T g 
  \<Longrightarrow> \<forall>t\<in>T. g t \<noteq> 0 \<Longrightarrow> continuous_on T (\<lambda>t. f t /\<^sub>R g t)" 
  for f::"'a::topological_space \<Rightarrow> 'b::real_normed_div_algebra"
  by (auto intro!: continuity_intros)


subsection \<open> Certification of uniqueness \<close>

method lipschitz_const for L :: real = 
  (unfold local_lipschitz_on_def local_lipschitz_def lipschitz_on_def dist_norm, clarify, 
    rule exI[where x="L"], expr_auto, (rule exI[where x="L"], auto)?)

method c1_lipschitz =
  (expr_simp; (auto intro!: c1_local_lipschitz derivative_eq_intros continuity_intros)?)

method c1_lipschitzI for df uses derivsI =
  (expr_simp, (rule_tac \<DD>=df in c1_local_lipschitz; expr_auto)?; 
    (auto intro!: c1_local_lipschitz derivative_eq_intros continuity_intros derivsI)?)

lemma "vwb_lens (x::real \<Longrightarrow> 's) \<Longrightarrow> local_lipschitz UNIV UNIV (\<lambda>t::real. [x \<leadsto> 2] \<down>\<^sub>S\<^sub>u\<^sub>b\<^sub>s\<^sub>t\<^bsub>x\<^esub> s)"
  by c1_lipschitz

lemma "vwb_lens (x::real \<Longrightarrow> 's) \<Longrightarrow> local_lipschitz UNIV UNIV (\<lambda>t::real. [x \<leadsto> - $x] \<down>\<^sub>S\<^sub>u\<^sub>b\<^sub>s\<^sub>t\<^bsub>x\<^esub> s)"
  by c1_lipschitz

lemma "vwb_lens (x::real \<Longrightarrow> 's) \<Longrightarrow> x \<bowtie> y \<Longrightarrow> y \<bowtie> x 
  \<Longrightarrow> local_lipschitz UNIV UNIV (\<lambda>t::real. [x \<leadsto> $y] \<down>\<^sub>S\<^sub>u\<^sub>b\<^sub>s\<^sub>t\<^bsub>x\<^esub> s)"
  by c1_lipschitz

lemma "vwb_lens (x::real \<Longrightarrow> 's) \<Longrightarrow> vwb_lens (y::real \<Longrightarrow> 's) \<Longrightarrow> vwb_lens (z::real \<Longrightarrow> 's) 
  \<Longrightarrow> x \<bowtie> y \<Longrightarrow> y \<bowtie> x \<Longrightarrow> x \<bowtie> z \<Longrightarrow> z \<bowtie> x \<Longrightarrow> z \<bowtie> y \<Longrightarrow> y \<bowtie> z
  \<Longrightarrow> local_lipschitz UNIV UNIV (\<lambda>t::real. [x \<leadsto> $y, y \<leadsto> $z] \<down>\<^sub>S\<^sub>u\<^sub>b\<^sub>s\<^sub>t\<^bsub>x +\<^sub>L y\<^esub> s)"
  by c1_lipschitz

lemma "vwb_lens (x::real \<Longrightarrow> 's) \<Longrightarrow> local_lipschitz UNIV UNIV (\<lambda>t::real. [x \<leadsto> 1 - $x] \<down>\<^sub>S\<^sub>u\<^sub>b\<^sub>s\<^sub>t\<^bsub>x\<^esub> s)"
  by c1_lipschitz

lemma "vwb_lens (x::real \<Longrightarrow> 's) \<Longrightarrow> x \<bowtie> y \<Longrightarrow> y \<bowtie> x 
  \<Longrightarrow> local_lipschitz UNIV UNIV (\<lambda>t::real. [x \<leadsto> - ($y * $x)] \<down>\<^sub>S\<^sub>u\<^sub>b\<^sub>s\<^sub>t\<^bsub>x\<^esub> s)"
  by c1_lipschitz

lemma "vwb_lens (x::real \<Longrightarrow> 's) \<Longrightarrow> vwb_lens (y::real \<Longrightarrow> 's) \<Longrightarrow> x \<bowtie> y \<Longrightarrow> y \<bowtie> x 
  \<Longrightarrow> local_lipschitz UNIV UNIV (\<lambda>t::real. [x \<leadsto> - $y, y \<leadsto> $x] \<down>\<^sub>S\<^sub>u\<^sub>b\<^sub>s\<^sub>t\<^bsub>x +\<^sub>L y\<^esub> s)"
  by c1_lipschitz

lemma trivial_prod_subst: "(\<lambda>x. case x of (t, a) \<Rightarrow> f t a) = (\<lambda>(t,a). f t a)"
  by simp

(* fails on nonlinear inputs *)
lemma "vwb_lens (x::real \<Longrightarrow> 's) 
  \<Longrightarrow> local_lipschitz UNIV UNIV (\<lambda>t::real. [x \<leadsto> 1 - ($x)\<^sup>2] \<down>\<^sub>S\<^sub>u\<^sub>b\<^sub>s\<^sub>t\<^bsub>x\<^esub> s)"
  apply expr_simp
  thm c1_implies_local_lipschitz
  apply (rule_tac f'="\<lambda>(t,a). Blinfun (\<lambda>c. - (2 * c * a))" in c1_implies_local_lipschitz; clarsimp?)
   apply (auto intro!: derivative_eq_intros)                          
   apply (subst Blinfun_inverse; clarsimp)
  using bounded_linear_minus bounded_linear_mult_const bounded_linear_mult_right apply blast
  apply (subst trivial_prod_subst)
  apply (subst comp_def[symmetric, of Blinfun])
  apply (auto intro: continuity_intros split: prod.splits)
  find_theorems "_ \<Longrightarrow> continuous_on _ _" name: comp
  thm blinfun_apply_inverse Blinfun_inverse term Blinfun
  oops

(* but we can make it linear *)
lemma "vwb_lens (x::real \<Longrightarrow> 's) \<Longrightarrow> vwb_lens (y::real \<Longrightarrow> 's) \<Longrightarrow> x \<bowtie> y \<Longrightarrow> y \<bowtie> x 
  \<Longrightarrow> local_lipschitz UNIV UNIV (\<lambda>t::real. [x \<leadsto> 1 - $y, y \<leadsto> 2 * $x] \<down>\<^sub>S\<^sub>u\<^sub>b\<^sub>s\<^sub>t\<^bsub>x\<^esub> s)"
  by c1_lipschitz

(* fails on nonlinear inputs *)
lemma "vwb_lens (x::real \<Longrightarrow> 's) 
  \<Longrightarrow> local_lipschitz UNIV UNIV (\<lambda>t::real. [x \<leadsto> 1 - exp ($x)] \<down>\<^sub>S\<^sub>u\<^sub>b\<^sub>s\<^sub>t\<^bsub>x\<^esub> s)"
  oops

(* but we can make it linear *)
lemma "vwb_lens (x::real \<Longrightarrow> 's) \<Longrightarrow> vwb_lens (y::real \<Longrightarrow> 's) \<Longrightarrow> x \<bowtie> y \<Longrightarrow> y \<bowtie> x 
  \<Longrightarrow> local_lipschitz UNIV UNIV (\<lambda>t::real. [x \<leadsto> 1 - $y, y \<leadsto> $y] \<down>\<^sub>S\<^sub>u\<^sub>b\<^sub>s\<^sub>t\<^bsub>x\<^esub> s)"
  by c1_lipschitz


subsection \<open> Certification of solutions \<close>

method local_flow for L :: real =
  ((auto simp add: local_flow_on_def)?, 
    (unfold_locales, auto), 
    (lipschitz_const L, vderiv, expr_auto))

method local_flow_Lconst =
  (local_flow "1/4" | local_flow "1/2" | local_flow "1" | local_flow "2")

method local_flow_on_auto =
  (((clarsimp simp: local_flow_on_def)?, unfold_locales; clarsimp?), c1_lipschitz, vderiv+)

lemma "vwb_lens x \<Longrightarrow> local_flow_on [x \<leadsto> 2] x UNIV UNIV (\<lambda>t. [x \<leadsto> 2 * \<guillemotleft>t\<guillemotright> + $x])"
  by local_flow_on_auto

lemma "vwb_lens (x::real \<Longrightarrow> 's) 
  \<Longrightarrow> local_flow_on [x \<leadsto> - $x] x UNIV UNIV (\<lambda>t. [x \<leadsto> $x * exp (- \<guillemotleft>t\<guillemotright>)])"
  by local_flow_on_auto

lemma "vwb_lens (x::real \<Longrightarrow> 's) \<Longrightarrow> x \<bowtie> y \<Longrightarrow> y \<bowtie> x 
  \<Longrightarrow> local_flow_on [x \<leadsto> $y] x UNIV UNIV (\<lambda>t. [x \<leadsto> $y * \<guillemotleft>t\<guillemotright> + $x])"
  by local_flow_on_auto

lemma "vwb_lens (x::real \<Longrightarrow> 's) \<Longrightarrow> vwb_lens (y::real \<Longrightarrow> 's) \<Longrightarrow> vwb_lens (z::real \<Longrightarrow> 's) 
  \<Longrightarrow> x \<bowtie> y \<Longrightarrow> y \<bowtie> x \<Longrightarrow> x \<bowtie> z \<Longrightarrow> z \<bowtie> x \<Longrightarrow> z \<bowtie> y \<Longrightarrow> y \<bowtie> z
  \<Longrightarrow> local_flow_on [x \<leadsto> $y, y \<leadsto> $z] (x +\<^sub>L y) UNIV UNIV 
  (\<lambda>t. [x \<leadsto> $z * \<guillemotleft>t\<guillemotright>\<^sup>2 / 2 + $y * \<guillemotleft>t\<guillemotright> + $x, y \<leadsto> $z * \<guillemotleft>t\<guillemotright> + $y])"
  by local_flow_on_auto

lemma "vwb_lens (x::real \<Longrightarrow> 's) \<Longrightarrow> x \<bowtie> y \<Longrightarrow> y \<bowtie> x 
  \<Longrightarrow> local_flow_on [x \<leadsto> - $x + 1] x UNIV UNIV (\<lambda>t. [x \<leadsto> 1 - exp (- \<guillemotleft>t\<guillemotright>) + $x * exp (- \<guillemotleft>t\<guillemotright>)])"
  by local_flow_on_auto

lemma "vwb_lens (x::real \<Longrightarrow> 's) \<Longrightarrow> x \<bowtie> y \<Longrightarrow> y \<bowtie> x 
  \<Longrightarrow> local_flow_on [x \<leadsto> - $y * $x] x UNIV UNIV (\<lambda>t. [x \<leadsto> $x * exp (- \<guillemotleft>t\<guillemotright> * $y)])"
  by local_flow_on_auto

lemma "vwb_lens (x::real \<Longrightarrow> 's) \<Longrightarrow> vwb_lens y \<Longrightarrow> x \<bowtie> y \<Longrightarrow> y \<bowtie> x 
  \<Longrightarrow> local_flow_on [x \<leadsto> - $y, y \<leadsto> $x] (x +\<^sub>L y) UNIV UNIV 
  (\<lambda>t. [x \<leadsto> $x * cos \<guillemotleft>t\<guillemotright> + - 1 * $y * sin \<guillemotleft>t\<guillemotright>, y \<leadsto> $y * cos \<guillemotleft>t\<guillemotright> + $x * sin \<guillemotleft>t\<guillemotright>])"
  by local_flow_on_auto


subsection \<open> Hoare Logic \<close>

text \<open> A simple tactic for Hoare logic that uses weakest liberal precondition calculations \<close>

(* Formally, this is not Hoare logic, rename? *)
method hoare_wp_simp uses local_flow 
  = (((rule_tac hoare_loopI) | (rule hoare_loopI_break))?; 
    simp add: unrest_ssubst var_alpha_combine wlp usubst usubst_eval 
    refine_iff_implies fbox_solve[OF local_flow[simplified]])

method hoare_wp_auto uses local_flow = (hoare_wp_simp local_flow: local_flow; expr_auto)

text \<open> First attempt at a system level prover \<close>

method dProve = (rule_tac hoare_loop_seqI, hoare_wp_auto, dInduct_mega', (expr_auto)+)


subsection \<open> Weakest liberal preconditions \<close>

(* most used solution theorems in arch2022:
  * fbox_g_ode_frame_flow
  * fbox_solve (which is essentially the one above)
  * fbox_g_dL_easiest (which transforms g_dl_ode_frames into g_evol_ons)
*)
method intro_loops = (rule hoare_loopI hoare_whileI hoare_loopI_break hoare_whileI_break)

method wlp_simp uses simp = (intro_loops?; (simp add: wlp simp)?)

method wlp_flow uses simp local_flow = (wlp_simp simp: simp fbox_solve[OF local_flow]) 

method wlp_full uses simp local_flow = ((wlp_flow simp: simp local_flow: local_flow)?; expr_auto)

method wlp_solve_one for \<phi>::"real \<Rightarrow> 'a \<Rightarrow> 'a" = (subst fbox_solve[where \<phi>=\<phi>], local_flow_on_auto?)

method wlp_solve for \<phi>::"real \<Rightarrow> 'a \<Rightarrow> 'a" uses simp 
  = ((wlp_simp simp: simp)?, (wlp_solve_one \<phi>)+)

method wlp_expr_solve for \<phi>::"real \<Rightarrow> 'a \<Rightarrow> 'a" uses simp 
  = ((wlp_solve \<phi> simp: simp); expr_auto?)

dataspace testing_wp_tactic =
  constants A::real B::real S::real V::real \<epsilon>::real
  variables x::real v::real a::real c::real d::real

lit_vars
no_notation (ASCII) disj (infixr "|" 30)

context testing_wp_tactic
begin

lemma "(v \<ge> 0 \<and> A > 0 \<and> B > 0 \<and> x + v\<^sup>2/(2 * B) \<le> S \<and> \<epsilon> > 0)\<^sub>e \<le>
  |LOOP 
    ((\<questiondown>x + v\<^sup>2/(2*B) + (A/B + 1)*(A/2*\<epsilon>\<^sup>2 + \<epsilon> * v) \<le> S?; a ::= A) 
      \<sqinter> (\<questiondown>v=0?; a ::= 0) 
      \<sqinter> (a ::= - B; d ::= ?)
    );(
      (c ::= 0); 
      {x` = v, v` = a, c` = 1 | (v \<ge> 0 \<and> x + v\<^sup>2/(2*B) \<le> S)}
    )
   INV (v \<ge> 0 \<and> x + v\<^sup>2/(2 * B) \<le> S)
  ] (x \<le> S)"
  apply (subst change_loopI[where I="(v \<ge> 0 \<and> A > 0 \<and> B > 0 \<and> x + v\<^sup>2/(2*B) \<le> S \<and> \<epsilon> > 0)\<^sup>e"])
  apply (wlp_expr_solve "(\<lambda>t. [c \<leadsto> t + c, x \<leadsto> $a * t\<^sup>2 / 2 + $v * t + $x, v \<leadsto> $a * t + $v])")
  by (smt (verit) divide_nonneg_nonneg zero_le_power)

lemma local_flow_test: "local_flow_on [c \<leadsto> 1, v \<leadsto> $a, x \<leadsto> $v] (x +\<^sub>L v +\<^sub>L c) UNIV UNIV
  (\<lambda>t. [c \<leadsto> t + c, x \<leadsto> $a * t\<^sup>2 / 2 + $v * t + $x, v \<leadsto> $a * t + $v])"
  by local_flow_on_auto

lemma "(v \<ge> 0 \<and> A > 0 \<and> B > 0 \<and> x + v\<^sup>2/(2 * B) \<le> S \<and> \<epsilon> > 0)\<^sub>e \<le>
  |LOOP 
    ((\<questiondown>x + v\<^sup>2/(2*B) + (A/B + 1)*(A/2*\<epsilon>\<^sup>2 + \<epsilon> * v) \<le> S?; a ::= A) 
      \<sqinter> (\<questiondown>v=0?; a ::= 0) 
      \<sqinter> (a ::= - B; d ::= ?)
    );(
      (c ::= 0); 
      {x` = v, v` = a, c` = 1 | (v \<ge> 0 \<and> x + v\<^sup>2/(2*B) \<le> S)}
    )
   INV (v \<ge> 0 \<and> x + v\<^sup>2/(2 * B) \<le> S)
  ] (x \<le> S)"
  apply (subst change_loopI[where I="(v \<ge> 0 \<and> A > 0 \<and> B > 0 \<and> x + v\<^sup>2/(2*B) \<le> S \<and> \<epsilon> > 0)\<^sup>e"])
  by (wlp_full local_flow: local_flow_test)
    (smt (verit) divide_nonneg_nonneg zero_le_power)

end


end
(**)