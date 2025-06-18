theory Dynamics_Easy
  imports Basic_Programs
begin

context basic_programs
begin


subsubsection \<open> 10. Dynamics: Cascaded \<close>

(* proof with solutions *)
(* x>0 -> [{x'=5};{x'=2};{x'=x}]x>0 *)
lemma "(x > 0)\<^sub>e \<le> |{x` = 5}; {x` = 2};{x` = x}] (x > 0)"
  apply wlp_simp
  apply (wlp_solve_one "\<lambda>t. [x \<leadsto> 5 * t + x]")
  by (wlp_solve_one "\<lambda>t. [x \<leadsto> 2 * t + x]")
    (wlp_solve_one "\<lambda>t. [x \<leadsto> x * exp t]")

(* proof with darboux rule *)
(* x>0 -> [{x'=5};{x'=2};{x'=x}]x>0 *)
lemma "(x > 0)\<^sub>e \<le> |{x` = 5}; {x` = 2};{x` = x}] (x > 0)"
  apply (sequence "x > 0")+
    apply dInduct
   apply dInduct
  apply (rule darboux_ge[of x y z _ _ _ 1]; expr_simp?)
  subgoal 
    by expr_auto 
      (rule_tac x="put\<^bsub>y\<^esub> _ 1" in exI, simp)
  subgoal by (subst lens_indep_comm; expr_simp)
  subgoal by (simp add: frechet_derivative_fst)
  using bounded_linear_fst bounded_linear_imp_differentiable by blast


subsubsection \<open> 11. Dynamics: Single integrator time \<close>

(* proof with invariants *)
(* x=0->[{x'=1}]x>=0 *)
lemma "H{x = 0} {x` = 1} {x \<ge> 0}"
  by (rule_tac I="(x\<ge>0)\<^sup>e" in fbox_diff_invI)
    (dInduct | expr_auto)+

(* proof with solutions *)
(* x=0->[{x'=1}]x>=0 *)
lemma "H{x = 0} {x` = 1} {x \<ge> 0}"
  by (wlp_solve "\<lambda>t. [x \<leadsto> t + x]")


subsubsection \<open> 12. Dynamics: Single integrator \<close>

(* proof with solutions *)
(* x>=0 & y>=0 -> [{x'=y}]x>=0 *)
lemma "H{x \<ge> 0 \<and> y \<ge> 0} {x` = y} {x \<ge> 0}"
  by (wlp_solve "\<lambda>t. [x \<leadsto> y * t + x]")

(* proof with invariants *)
(* x>=0 & y>=0 -> [{x'=y}]x>=0 *)
lemma "H{x \<ge> 0 \<and> y \<ge> 0} {x` = y} {x \<ge> 0}"
  apply (rule_tac P="(0 \<le> y \<and> 0 \<le> x)\<^sup>e" and Q="(0 \<le> y \<and> 0 \<le> x)\<^sup>e" in hoare_conseq)
  by dInduct_mega
    expr_auto+

subsubsection \<open> 13. Dynamics: Double integrator \<close>

(* x>=0 & y>=0 & z>=0 -> [{x'=y,y'=z}]x>=0 *)
lemma "(x \<ge> 0 \<and> y \<ge>0 \<and> z \<ge> 0)\<^sub>e \<le> |{x` = y, y` = z}] (x \<ge> 0)"
  by (wlp_solve "\<lambda>t. [x \<leadsto> z * t\<^sup>2 / 2 + y * t + x, y \<leadsto> z * t + y]")


subsubsection \<open> 14. Dynamics: Triple integrator \<close> (**)

(* x>=0 & y>=0 & z>=0 & j>=0 -> [{x'=y,y'=z,z'=j,j'=j\<^sup>2}]x>=0 *)
lemma "(x \<ge> 0 \<and> y \<ge> 0 \<and> z \<ge> 0 \<and> w \<ge> 0)\<^sub>e \<le> |{x` = y, y` = z, z` = w, w` = w\<^sup>2}] (x \<ge>0)"
  apply (rule_tac P="(w \<ge> 0 \<and> z \<ge> 0 \<and> y \<ge> 0 \<and> x \<ge> 0)\<^sup>e" and Q="(w \<ge> 0 \<and> z \<ge> 0 \<and> y \<ge> 0 \<and> x \<ge> 0)\<^sup>e" in hoare_conseq)
  by dInduct_mega
    expr_auto+


subsubsection \<open> 15. Dynamics: Exponential decay (1) \<close>

(* proof with solutions *)
(* x>0 -> [{x'=-x}]x>0 *)
lemma "(x > 0)\<^sub>e \<le> |{x` = -x}] (x > 0)"
  by (wlp_solve "\<lambda>t. [x \<leadsto> x * exp (- t)]")

(* proof with ghosts *)
(* x>0 -> [{x'=-x}]x>0 *)
lemma "(x > 0)\<^sub>e \<le> |{x` = -x}] (x > 0)"
  apply (dGhost "y" "x*y\<^sup>2 = 1" "1/2")
  by (diff_inv_on_eq)
    (expr_auto add: exp_ghost_arith)

(* proof with solutions *)
(* x>0 -> [{x'=-x+1}]x>0 *)
lemma "(x > 0)\<^sub>e \<le> |{x` = -x + 1}] (x > 0)"
  apply (wlp_solve "\<lambda>t. [x \<leadsto> 1 - exp (- t) + x * exp (- t)]")
  by expr_auto (metis add_pos_nonneg diff_gt_0_iff_gt exp_eq_one_iff exp_ge_zero 
      exp_less_one_iff less_eq_real_def mult.commute mult_1 neg_equal_zero 
      real_0_less_add_iff right_minus_eq zero_le_mult_iff)

(* proof with ghosts *)
(* x>0 -> [{x'=-x+1}]x>0 *)
lemma "(x > 0)\<^sub>e \<le> |{x` = -x + 1}] (x > 0)"
  apply (rule_tac a=x and y=y and z=z and g="-1" in darboux_ge; simp?)
  subgoal by expr_auto 
      (meson indeps(7) lens_indep.lens_put_comm)
  subgoal by expr_simp
  subgoal by expr_auto 
      (rule_tac x="put\<^bsub>y\<^esub> _ 1" in exI, simp)
  subgoal by expr_simp
      (metis indeps(10,11) lens_indep.lens_put_comm)
  subgoal by expr_simp
  subgoal by (simp add: framed_derivs, expr_simp add: le_fun_def)
  subgoal by (force simp: ldifferentiable)
  done


subsubsection \<open> 17. Dynamics: Exponential decay (3) \<close> (**)

(* x>0 & y>0->[{x'=-y*x}]x>0 *)
lemma "`y > 0` \<Longrightarrow> (x > 0)\<^sub>e \<le> |{x` = - y * x}] (x > 0)"
  by (wlp_solve "\<lambda>t. [x \<leadsto> x * exp (- t * y)]")


subsubsection \<open> 18. Dynamics: Exponential growth (1) \<close> (**)

(* proof with solutions *)
(* x>=0 -> [{x'=x}]x>=0 *)
lemma "(x \<ge> 0)\<^sub>e \<le> |{x` = x}] (x \<ge> 0)"
  by (wlp_solve "\<lambda>t. [x \<leadsto> x * exp t]")

(* proof with ghosts *)
(* x>=0 -> [{x'=x}]x>=0 *)
lemma "(x \<ge> 0)\<^sub>e \<le> |{x` = x}] (x \<ge> 0)"
  apply (dGhost "y" "y > 0 \<and> x * y \<ge> 0" "-1")
   apply (dGhost "z" "y * z\<^sup>2 = 1 \<and> x * y \<ge> 0" "1/2")
    apply (rule fbox_invs)
     apply (diff_inv_on_eq)
    apply (diff_inv_on_ineq "(0)\<^sup>e" "(x * y - x * y)\<^sup>e")
  apply (vderiv)
  using exp_ghost_arith apply expr_auto
  apply expr_auto
  by (metis mult.right_neutral zero_less_one)
    (simp add: zero_le_mult_iff)


subsubsection \<open> 19. Dynamics: Exponential growth (2) \<close>

(* x>=0 & y>=0 -> [{x'=y, y'=y\<^sup>2}]x>=0 *)
lemma "(x \<ge> 0 \<and> y \<ge> 0)\<^sub>e \<le> |{x` = y, y` = y\<^sup>2}] (x \<ge> 0)"
  apply (rule_tac P="(y \<ge> 0 \<and> x \<ge> 0)\<^sup>e" and Q="(y \<ge> 0 \<and> x \<ge> 0)\<^sup>e" in hoare_conseq)
  by dInduct_mega 
    expr_auto+


subsubsection \<open> 20. Dynamics: Exponential growth (4) \<close> (* sic *)

(* x>0 -> [{x'=x^x}]x>0 *)
lemma "(x > 0)\<^sub>e \<le> |{x` = x powr x}] (x > 0)"
  by dInduct


subsubsection \<open> 21. Dynamics: Exponential growth (5) \<close>

(* x>=1 -> [{x'=x\<^sup>2+2*x^4}]x^3>=x\<^sup>2 *)
lemma "(x \<ge> 1)\<^sub>e \<le> |{x` = x\<^sup>2 + 2 * x\<^sup>4}] (x^3 \<ge> x\<^sup>2)"
  apply (dCut "1 \<le> x", dInduct)
  apply (dCut "x\<^sup>2 \<le> x\<^sup>3")
   apply postcondition_invariant
    apply dInduct
  subgoal
    apply expr_simp
    by powers_simp
      (smt (verit, best) arithmetic_simps(1,4,7) 
      le_add1 numeral_plus_one one_le_power power_increasing)
  subgoal
    by expr_auto
      (smt (verit, best) arithmetic_simps(1,4,7)
        le_add1 numeral_plus_one power_increasing)
  by (rule diff_weak_on_rule)
    expr_auto


subsubsection \<open> 22. Dynamics: Rotational dynamics (1) \<close>

(* proof with invariants *)
(* x\<^sup>2+y\<^sup>2=1 -> [{x'=-y, y'=x}]x\<^sup>2+y\<^sup>2=1 *)
lemma "(x\<^sup>2 + y\<^sup>2 = 1)\<^sub>e \<le> |{x` = -y, y` = x}] (x\<^sup>2 + y\<^sup>2 = 1)"
  by dInduct

(* proof with solutions *)
(* x\<^sup>2+y\<^sup>2=1 -> [{x'=-y, y'=x}]x\<^sup>2+y\<^sup>2=1 *)
lemma "(x\<^sup>2 + y\<^sup>2 = 1)\<^sub>e \<le> |{x` = -y, y` = x}] (x\<^sup>2 + y\<^sup>2 = 1)"
  apply (wlp_solve "\<lambda>t. [x \<leadsto> x * cos t + - 1 * y * sin t, y \<leadsto> y * cos t + x * sin t]")
  by (expr_simp add: abs_minus_commute norm_Pair le_fun_def)
    (smt (verit, ccfv_SIG) norm_rotate_eq(1))


subsubsection \<open> 23. Dynamics: Rotational dynamics (2) \<close> (* prove as a linear system *)

(* proof with invariants *)
(* x\<^sup>2+y\<^sup>2=1 & e=x -> [{x'=-y, y'=e, e'=-y}](x\<^sup>2+y\<^sup>2=1 & e=x) *)
lemma "(x\<^sup>2 + y\<^sup>2 = 1 \<and> z = x)\<^sub>e \<le> |{x` = -y, y` = z, z` = -y}] (x\<^sup>2 + y\<^sup>2 = 1 \<and> z = x)"  
  apply (dCut "z = x")
   apply (postcondition_invariant, dInduct, expr_simp)
  apply (dCut "z\<^sup>2 + y\<^sup>2 = 1")
   apply (postcondition_invariant, dInduct, expr_simp)
  by (rule diff_weak_on_rule, expr_auto)

(* proof with solutions *)
lemma "(x\<^sup>2 + y\<^sup>2 = 1 \<and> z = x)\<^sub>e \<le> |{x` = -y, y` = z, z` = -y}] (x\<^sup>2 + y\<^sup>2 = 1 \<and> z = x)"
  (* find_local_flow *)
  apply (wlp_solve 
      "\<lambda>t. [
        x \<leadsto> $x + $z * (- 1 + cos t) + - 1 * $y * sin t, 
        y \<leadsto> $y * cos t + $z * sin t, 
        z \<leadsto> $z * cos t + - 1 * $y * sin t]" 
      simp: lens_defs expr_defs)
  by powers_simp
    (smt (verit, del_insts) add.right_neutral distrib_left power_0 
        power_add sin_cos_squared_add)

end (* basic_programs *)


subsubsection \<open> 24. Dynamics: Rotational dynamics (3) \<close>

dataspace rotational_dynamics3 =
  constants
    w :: real
    p :: real
  variables 
    x1 :: real 
    x2 :: real 
    d1 :: real
    d2 :: real

context rotational_dynamics3
begin

(* proof with invariants *)
(* d1\<^sup>2+d2\<^sup>2=w\<^sup>2*p\<^sup>2 & d1=-w*x2 & d2=w*x1 -> 
  [{x1'=d1, x2'=d2, d1'=-w*d2, d2'=w*d1}]
  (d1\<^sup>2+d2\<^sup>2=w\<^sup>2*p\<^sup>2 & d1=-w*x2 & d2=w*x1)*)
lemma "(d1\<^sup>2 + d2\<^sup>2 = w\<^sup>2 * p\<^sup>2 \<and> d1 = - w * x2 \<and> d2 = w * x1)\<^sub>e \<le>
  |{x1` = d1, x2` = d2, d1` = - w * d2, d2` = w * d1}] 
  (d1\<^sup>2 + d2\<^sup>2 = w\<^sup>2 * p\<^sup>2 \<and> d1 = - w * x2 \<and> d2 = w * x1)"
  by dInduct

(* proof with solutions *)
(* d1\<^sup>2+d2\<^sup>2=w\<^sup>2*p\<^sup>2 & d1=-w*x2 & d2=w*x1 -> 
  [{x1'=d1, x2'=d2, d1'=-w*d2, d2'=w*d1}]
  (d1\<^sup>2+d2\<^sup>2=w\<^sup>2*p\<^sup>2 & d1=-w*x2 & d2=w*x1)*)
lemma "w \<noteq> 0 \<Longrightarrow> (d1\<^sup>2 + d2\<^sup>2 = w\<^sup>2 * p\<^sup>2 \<and> d1 = - w * x2 \<and> d2 = w * x1)\<^sub>e \<le>
  |{x1` = d1, x2` = d2, d1` = - w * d2, d2` = w * d1}] 
  (d1\<^sup>2 + d2\<^sup>2 = w\<^sup>2 * p\<^sup>2 \<and> d1 = - w * x2 \<and> d2 = w * x1)"
  (* find_local_flow *)
  apply (wlp_solve "\<lambda>t. [d1 \<leadsto> d1 * cos (t * w) + - 1 * d2 * sin (t * w), 
    d2 \<leadsto> d2 * cos (t * w) + d1 * sin (t * w), 
    x1 \<leadsto> x1 + 1 / w * d2 * (- 1 + cos (t * w)) + 1 / w * d1 * sin (t * w), 
    x2 \<leadsto> x2 + 1 / w * d1 * (1 + - 1 * cos (t * w)) + 1 / w * d2 * sin (t * w)]"
      simp: lens_defs expr_defs)
  by powers_simp
    (simp add: Groups.add_ac(2,3) factorR(1) vector_space_over_itself.vector_space_assms(3))

end (* rotational_dynamics3 *)


context basic_programs
begin


subsubsection \<open> 25. Dynamics: Spiral to equilibrium \<close>

(* w>=0 & x=0 & y=3 -> [{x'=y, y'=-w\<^sup>2*x-2*w*y}]w\<^sup>2*x\<^sup>2+y\<^sup>2<=9 *)
lemma "(w \<ge> 0 \<and> x = 0 \<and> y = 3)\<^sub>e \<le> |{x` = y, y` = - w\<^sup>2 * x - 2 * w * y}] (w\<^sup>2 * x\<^sup>2 + y\<^sup>2 \<le> 9)"
  apply (dCut "0 \<le> w")
   apply (postcondition_invariant, dInduct, expr_simp)
   apply (rule hoare_invI[where I="(w\<^sup>2 * x\<^sup>2 + y\<^sup>2 \<le> 9)\<^sup>e"])
  by dInduct_auto
    expr_simp+

end (* basic_programs *)

end