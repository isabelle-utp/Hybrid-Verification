theory Nonlinear
imports Basic_Programs

begin

subsection \<open> Nonlinear \<close>


subsubsection \<open> Benchmarks/Nonlinear/Ahmadi Parrilo Krstic \<close>


lemma exp_ghost_arith2: "0 \<le> y \<longleftrightarrow> (\<exists>z. 0 < z \<and> 0 \<le> z * y)" for y::real
  apply (intro iffI; clarsimp?)
  by (rule_tac x=1 in exI; clarsimp)
    (simp add: zero_le_mult_iff)

lemma exp_ghost_arith2':
  fixes y z :: "real \<Longrightarrow> 's"
  shows "vwb_lens z \<Longrightarrow> y \<bowtie> z \<Longrightarrow> (0 \<le> get\<^bsub>y\<^esub> s) = (\<exists>s'. 0 < get\<^bsub>z\<^esub> s' \<and> 0 \<le> get\<^bsub>z\<^esub> s' * get\<^bsub>y\<^esub> s)"
  apply (intro iffI; clarsimp?)
  by (rule_tac x="put\<^bsub>z\<^esub> s 1" in exI, clarsimp)
    (simp add: zero_le_mult_iff)

context basic_programs
begin

(* 0.5<=x & x<=0.7 & 0<=y & y<=0.3
  ->
  [
    {x'=-x+x*y , y'=-y}@invariant(y>=0)
  ] !(-0.8>=x & x>=-1 & -0.7>=y & y>=-1) *)
lemma "H{0.5 \<le> x & x \<le> 0.7 & 0 \<le> y & y \<le> 0.3}
    {x` = -x + x* y , y` = - y} INV (y \<ge> 0)
  { \<not> (-0.8 \<ge> x \<and> x \<ge> -1 & -0.7 \<ge> y \<and> y \<ge> -1)}"
  unfolding invar_def
  apply (dCut "y \<ge> 0")
   apply postcondition_invariant
    apply (dGhost "z" "z > 0 \<and> z * y \<ge> 0" "1")
     apply split_invariant
      apply (dGhost "w" "z * w\<^sup>2 = 1" "-1/2")
       apply dInduct
       apply (expr_simp add: power2_eq_square)
  using exp_ghost_arith apply metis
     apply dInduct
    apply expr_simp
  apply (metis mult_less_0_iff not_less rel_simps(68))
   apply expr_simp
  by (rule diff_weak_on_rule)
    simp

end


subsubsection \<open> Benchmarks/Nonlinear/Arrowsmith Place Fig\_3\_11 page 83 \<close>


lemma lget_ge0_exI: "vwb_lens z \<Longrightarrow> \<exists>s'. 0 < get\<^bsub>z\<^esub> s'" for z :: "real \<Longrightarrow> 's"
  by (metis class_dense_linordered_field.gt_ex vwb_lens.axioms(1) 
      wb_lens.axioms(1) weak_lens.put_get)

context basic_programs
begin

(* x=1 & y=1/8
  ->
  [
    {x'=x-y^2, y'=y*(x-y^2)}@invariant(y^2 < x)
  ] !(x<0) *)
lemma "(x=1 & y=1/8)\<^sub>e
  \<le> |{x` = $x - $y^2, y` = $y * ($x - $y^2)} INV (y^2 < x)
  ] (\<not> (x<0))"
  unfolding invar_def
  apply (dCut "y\<^sup>2 < x")
   apply (rule_tac I="(0 < x - y^2)\<^sup>e" in fbox_diff_invI) 
     prefer 2
  subgoal 
    by expr_auto
      (smt (verit, del_insts) four_x_squared one_power2)
    apply (rule darboux_ge[of "x +\<^sub>L y" z w _ _ "($x - ($y)\<^sup>2)\<^sup>e"]; simp?)
  subgoal 
    by expr_auto
      (metis indeps(11,9) lens_indep.lens_put_comm)
  subgoal 
    by expr_simp
  subgoal 
    using lget_ge0_exI[of z] 
    by expr_auto
  subgoal
    by expr_auto 
      (smt (verit, best) indeps(1,4,6) lens_indep.lens_put_comm)
  subgoal
    by expr_simp
  subgoal
     apply (subst framed_derivs)
       apply (rule ldifferentiable; simp?)+
     apply (subst framed_derivs, simp)
      apply (rule ldifferentiable; simp?)+
     apply (subst framed_derivs, simp, simp, simp)
     apply (subst framed_derivs, simp, simp, simp)
    apply (expr_auto add: le_fun_def)
    sorry
  subgoal by (intro ldifferentiable; simp?)
  subgoal by expr_auto
  subgoal
    apply (rule diff_weak_on_rule)
    by expr_auto (smt (verit) power2_less_0)
  oops

end

(*N

% Report/summary of unsolved problems
% 1. Dynamics: Fractional Darboux equality: 
      Requires darboux rule
% 2. Dynamics: Parametric switching between two different damped oscillators: 
      verified with the help of a CAS
% 3. STTT Tutorial: Example 9b:
      verified with the help of a CAS
% 4. LICS: Example 4b progress of time-triggered car: 
      not solved yet (existential)
% 5. LICS: Example 6 MPC Acceleration Equivalence:
      verified with the help of a CAS
% 6. LICS: Example 7 Model-Predictive Control Design Car:
      verified with the help of a CAS
% 7. ETCS: Proposition 4 (Reactivity):
      not solved yet (not dedicated enough time)
% 8. Benchmarks/Nonlinear/Arrowsmith Place Fig_3_11 page 83:
      Requires darboux rule
*)

end