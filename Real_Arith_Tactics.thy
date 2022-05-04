(* Maintainer:  jonathan.munive@di.ku.dk
*)

section \<open> Tactics \<close>

text \<open> We provide some tactics for easier interaction with proofs about real arithmetic.\<close>

theory Real_Arith_Tactics
  imports "HOL-Analysis.Analysis"
  "HOL-Eisbach.Eisbach"

begin


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

lemma "(36::real) * (x1\<^sup>2 * (x1 * x2 ^ 3)) - (- (24 * (x1\<^sup>2 * x2) * x1 ^ 3 * x2\<^sup>2) 
  - 12 * (x1\<^sup>2 * x2) * x1 * x2 ^ 4) - 36 * (x1\<^sup>2 * (x2 * x1)) * x2\<^sup>2 - 12 * (x1\<^sup>2 * (x1 * x2 ^ 5)) 
  = 24 * (x1 ^ 5 * x2 ^ 3)" (is "?t1 - (- ?t2 - ?t3) - ?t4 - ?t5 = ?t6")
  apply distribute
  apply (move_right x1)
  apply (move_right x2)
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

lemma "0 \<le> A \<Longrightarrow> 0 < b \<Longrightarrow> x2\<^sup>2 \<le> 2 * b * (m - x1) \<Longrightarrow> 0 \<le> (t::real) 
  \<Longrightarrow> \<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> b * \<tau> \<le> x2 \<and> \<tau> \<le> \<epsilon> 
  \<Longrightarrow> (x2 - b * t)\<^sup>2 \<le> 2 * b * (m - (x2 * t - b * t\<^sup>2 / 2 + x1))"
  apply bin_unfold
  apply distributes
  apply (mon_simp_vars b t)
  done

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



end