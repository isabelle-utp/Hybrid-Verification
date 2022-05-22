section \<open> Examples \<close>

text \<open> We prove partial correctness specifications of some hybrid systems with our 
verification components.\<close>

theory ARCH2022_Examples
  imports 
    HS_Lie_Derivatives
    Real_Arith_Tactics

begin


subsection \<open> Basic \<close>


subsubsection \<open> Basic assignment \<close> 

dataspace two_vars =
  variables x :: real y :: real 

context two_vars
begin

(* x>=0 -> [x:=x+1;]x>=1 *)
lemma "(x \<ge> 0)\<^sub>e \<le> |x ::= x + 1] (x \<ge> 1)"
  by hoare_wp_simp

end


subsubsection \<open> Overwrite assignment on some branches \<close>

context two_vars
begin

(* x>=0 -> [x:=x+1;][x:=x+1; ++ y:=x+1;]x>=1 *)
lemma "(x \<ge> 0)\<^sub>e \<le> |x ::= x + 1] |x ::= x + 1 \<sqinter> y ::= x + 1] (x \<ge> 1)"
  by hoare_wp_simp

end


subsubsection \<open> Overwrite assignment in loop \<close>

context two_vars
begin

(* x>=0 -> [x:=x+1;][{x:=x+1;}*@invariant(x>=1)]x>=1 *)
lemma "(x \<ge> 0)\<^sub>e \<le> |x ::= x + 1] |LOOP x ::= x + 1 INV (x \<ge> 1)] (x \<ge> 1)"
  apply (subst fbox_kcomp[symmetric])
  by (rule fbox_loopI_break) hoare_wp_auto+

end


subsubsection \<open> Overwrite assignment in ODE \<close>


context two_vars
begin

(* Proof using differential induction. Can this be better automated? *)
(* x>=0 -> [x:=x+1;][{x'=2}]x>=1 *)
lemma "\<^bold>{x \<ge> 0\<^bold>} x ::= x + 1 ; {x` = 2} \<^bold>{x \<ge> 1\<^bold>}"
proof -
  have 1: "\<^bold>{x \<ge> 1\<^bold>} {x` = 2} \<^bold>{x \<ge> 1\<^bold>}"
    by dInduct
  show ?thesis
    apply (rule hoare_fwd_assign)
     apply (simp)
    apply (subst_eval)
    apply (rule hoare_conseq[OF 1])
     apply (expr_simp)
    apply simp
    done
qed

(* Proof using the solution *)
(* x>=0 -> [x:=x+1;][{x'=2}]x>=1 *)
lemma "(x \<ge> 0)\<^sub>e \<le> |x ::= x + 1] |{x` = 2}] (x \<ge> 1)"
  apply (subst fbox_solve[where \<phi>="\<lambda>t. [x \<leadsto> 2 * \<guillemotleft>t\<guillemotright> + x]"]; simp add: wp)
  by (local_flow 1) expr_simp

(* usind differential invariants *)
(* x>=0 -> [x:=x+1;][{x'=2}]x>=1 *)
lemma "(x \<ge> 0)\<^sub>e \<le> |x ::= x + 1] |{x` = 2}] (x \<ge> 1)"
  unfolding fbox_kcomp[symmetric]
  apply (rule_tac R="($x \<ge> 1)\<^sup>e" in hoare_kcomp)
  by hoare_wp_simp (diff_inv_on_ineq "\<lambda>s. 0" "\<lambda>s. 2")

end


subsubsection \<open> Overwrite with nondeterministic assignment \<close>

context two_vars
begin

(* x>=0 -> [x:=x+1;][x:=*; ?x>=1;]x>=1 *)
lemma "\<^bold>{x \<ge> 0\<^bold>} x ::= x + 1 ; x ::= ? ; \<questiondown>x\<ge>1? \<^bold>{x \<ge> 1\<^bold>}"
  by hoare_wp_simp

end


subsubsection \<open> Tests and universal quantification \<close>

context two_vars
begin

(* x>=0 -> [x:=x+1;][?x>=2; x:=x-1; ++ ?\forall x (x>=1 -> y>=1); x:=y;]x>=1 *)
lemma "(x \<ge> 0)\<^sub>e \<le> |x ::=x+1] |(\<questiondown>x>=2?; x::=x-1) \<sqinter> (\<questiondown>\<forall>x::real. x \<ge> 1 \<longrightarrow> y \<ge> 1?; x::=y)] (x\<ge>1)"
  by hoare_wp_auto

end


subsubsection \<open> Overwrite assignment several times \<close>

context two_vars
begin

(* x>=0 & y>=1 -> [x:=x+1;][{x:=x+1;}*@invariant(x>=1) ++ y:=x+1;][{y'=2}][x:=y;]x>=1 *)
lemma "(x \<ge> 0 \<and> y \<ge>1)\<^sub>e \<le> |x ::= x + 1]|LOOP x ::= x + 1 INV (x \<ge> 1) \<sqinter> y ::= x + 1] |{y` = 2}] |x ::= y] (x \<ge> 1)"
  apply (subst fbox_solve[where \<phi>="\<lambda>t. [y \<leadsto> 2 * \<guillemotleft>t\<guillemotright> + y]"]; simp)
   apply (local_flow 1)[1]
  apply (subst change_loopI[where I="(1 \<le> x \<and> 1 \<le> y)\<^sub>e"])
  apply (subst fbox_kcomp[symmetric], rule hoare_kcomp)
   apply (subst fbox_assign[where Q="(1 \<le> x \<and> 1 \<le> y)\<^sub>e"], expr_simp)
  apply(subst le_fbox_choice_iff, rule conjI)
  by (subst fbox_loopI, auto simp: wp)
    expr_simp+

end


subsubsection \<open> Potentially overwrite dynamics \<close>

context two_vars
begin

(* x>0 & y>0 -> [{x'=5}][{x:=x+3;}*@invariant(x>0) ++ y:=x;](x>0&y>0) *)
lemma "(x > 0 \<and> y > 0)\<^sub>e \<le> |{x` = 5}]|LOOP x::=x+3 INV (x > 0) \<sqinter> y::=x] (x \<ge> 0 \<and> y \<ge> 0)"
  apply (subst change_loopI[where I="(0 < $x \<and> 0 < $y)\<^sup>e"])
  apply(subst fbox_kcomp[symmetric])
  apply(rule_tac R="(x > 0 \<and> y > 0)\<^sup>e" in hoare_kcomp)
  apply (simp add: expr_defs, rule fbox_invs_raw)
  apply (diff_inv_on_ineq "\<lambda>s. 0" "\<lambda>s. 5")
   apply (diff_inv_on_ineq "\<lambda>s. 0" "\<lambda>s. 0")
  apply (rule hoare_choice)
  by hoare_wp_auto+

end


subsubsection \<open> Potentially overwrite exponential decay \<close>

context two_vars
begin

(* proof with solutions *)
(* x>0 & y>0 -> [{x'=-x}][{x:=x+3;}*@invariant(x>0) ++ y:=x;](x>0&y>0) *)
lemma "(x > 0 \<and> y > 0)\<^sub>e \<le> |{x` = -x}]|LOOP x ::= x+3 INV (x > 0) \<sqinter> y::=x] (x > 0 \<and> y > 0)"
  apply (subst change_loopI[where I="(0 < $x \<and> 0 < $y)\<^sup>e"])
  apply (subst fbox_kcomp[symmetric])
  apply (rule_tac R="(0 < x \<and> 0 < y)\<^sup>e" in hoare_kcomp)
   apply (subst fbox_solve[where \<phi>="\<lambda>t. [x \<leadsto> x * exp (- \<guillemotleft>t\<guillemotright>)]"]; clarsimp?)
    apply (local_flow 1)[1]
   apply expr_auto[1]
  apply (rule hoare_choice)
  by hoare_wp_auto+

end

dataspace three_vars =
  variables 
    x :: real 
    y :: real 
    z :: real

lemma exp_ghost_arith: "0 < (a::real) \<longleftrightarrow> (\<exists>b. a * b\<^sup>2 = 1)"
  by (intro iffI exI[where x="1/(sqrt a)"]; clarsimp simp: field_simps)
    (metis less_numeral_extra(1) mult_less_0_iff not_one_less_zero zero_less_mult_iff)

context three_vars
begin

(* proof with solutions *)
(* x>0 & y>0 -> [{x'=-x}][{x:=x+3;}*@invariant(x>0) ++ y:=x;](x>0&y>0) *)
lemma "(x > 0 \<and> y > 0)\<^sub>e \<le> |{x` = -x}]|LOOP x ::= x+3 INV (x > 0) \<sqinter> y::=x] (x > 0 \<and> y > 0)"
  apply (subst change_loopI[where I="(0 < $x \<and> 0 < $y)\<^sup>e"])
  apply (subst fbox_kcomp[symmetric])
  apply (rule_tac R="(0 < x \<and> 0 < y)\<^sup>e" in hoare_kcomp)
   apply (dGhost "z" "(x*z\<^sup>2 = 1 \<and> y > 0)\<^sub>e" "1/2")
    apply (expr_auto add: exp_ghost_arith)
   apply (rule fbox_invs(1))
    apply (diff_inv_on_eq)
   apply (diff_inv_on_ineq "\<lambda>s. 0" "\<lambda>s. 0")
  apply (rule hoare_choice)
  by hoare_wp_auto+

end


subsubsection \<open> Dynamics: Cascaded \<close>

context two_vars
begin

(* x>0 -> [{x'=5};{x'=2};{x'=x}]x>0 *)
lemma "(x > 0)\<^sub>e \<le> |{x` = 5}; {x` = 2};{x` = x}] (x > 0)"
  apply (simp add: wp)
   apply (subst fbox_solve[where \<phi>="\<lambda>t. [x \<leadsto> 5 * \<guillemotleft>t\<guillemotright> + x]"]; clarsimp?)
   apply (local_flow 1)[1]
   apply (subst fbox_solve[where \<phi>="\<lambda>t. [x \<leadsto> 2 * \<guillemotleft>t\<guillemotright> + x]"]; clarsimp?)
   apply (local_flow 1)[1]
  apply (subst fbox_solve[where \<phi>="\<lambda>t. [x \<leadsto> x * exp \<guillemotleft>t\<guillemotright>]"]; clarsimp?)
   apply (local_flow 1)[1]
  by expr_auto

end


subsubsection \<open> Dynamics: Single integrator time \<close>

context two_vars
begin

(* proof with invariants *)
(* x=0->[{x'=1}]x>=0 *)
lemma "\<^bold>{x = 0\<^bold>} {x` = 1} \<^bold>{x \<ge> 0\<^bold>}"
  by (rule hoare_diff_inv_on_post_inv, simp, dInduct)

(* proof with solutions *)
(* x=0->[{x'=1}]x>=0 *)
lemma "\<^bold>{x = 0\<^bold>} {x` = 1} \<^bold>{x \<ge> 0\<^bold>}"
  apply (subst fbox_solve[where \<phi>="\<lambda>t. [x \<leadsto> \<guillemotleft>t\<guillemotright> + x]"]; clarsimp?)
  by (local_flow 1) expr_auto

end


subsubsection \<open> Dynamics: Single integrator \<close>

context two_vars
begin

(* x>=0 & y>=0 -> [{x'=y}]x>=0 *)
lemma "\<^bold>{x \<ge> 0 \<and> y \<ge> 0\<^bold>} {x` = y} \<^bold>{x \<ge> 0\<^bold>}"
  apply (subst fbox_solve[where \<phi>="\<lambda>t. [x \<leadsto> y * \<guillemotleft>t\<guillemotright> + x]"]; clarsimp?)
  by (local_flow 1) expr_auto

(* x>=0 & y>=0 -> [{x'=y}]x>=0 *)
lemma "\<^bold>{x \<ge> 0 \<and> y \<ge> 0\<^bold>} {x` = y} \<^bold>{x \<ge> 0\<^bold>}"
proof -
  have "\<^bold>{y \<ge> 0 \<and> x \<ge> 0\<^bold>} {x` = y} \<^bold>{y \<ge> 0 \<and> x \<ge> 0\<^bold>}"
    by (dInduct_mega)
  thus ?thesis
    by (rule hoare_conseq; simp)
qed
    
end


subsubsection \<open> Dynamics: Double integrator \<close>

context three_vars
begin

(* x>=0 & y>=0 & z>=0 -> [{x'=y,y'=z}]x>=0 *)
lemma "(x \<ge> 0 \<and> y \<ge>0 \<and> z \<ge> 0)\<^sub>e \<le> |{x` = y, y` = z}] (x \<ge> 0)"
  apply (subst fbox_solve[where \<phi>="\<lambda>t. [x \<leadsto> z * \<guillemotleft>t\<guillemotright>\<^sup>2 / 2 + y * \<guillemotleft>t\<guillemotright> + x, y \<leadsto> z * \<guillemotleft>t\<guillemotright> + y]"]; clarsimp?)
  apply (unfold local_flow_on_def, clarsimp, unfold_locales; expr_simp)
  subgoal by (lipschitz 1) (metis norm_snd_le real_norm_def)
  by (auto intro!: poly_derivatives) expr_simp

end


subsubsection \<open> Dynamics: Triple integrator \<close> (**)

dataspace four_vars =
  variables 
    x :: real 
    y :: real 
    z :: real
    w :: real

context four_vars
begin

(* x>=0 & y>=0 & z>=0 & j>=0 -> [{x'=y,y'=z,z'=j,j'=j\<^sup>2}]x>=0 *)
lemma "(x \<ge> 0 \<and> y \<ge> 0 \<and> z \<ge> 0 \<and> w \<ge> 0)\<^sub>e \<le> |{x` = y, y` = z, z` = w, w` = w\<^sup>2}] (x \<ge>0)"
  apply (diff_cut_ineq "(0 \<le> w)\<^sup>e" "(0)\<^sup>e" "(w\<^sup>2)\<^sup>e")
  apply (diff_cut_ineq "(0 \<le> z)\<^sup>e" "(0)\<^sup>e" "(w)\<^sup>e")
  apply (diff_cut_ineq "(0 \<le> y)\<^sup>e" "(0)\<^sup>e" "(z)\<^sup>e")
  by (diff_inv_on_weaken_ineq "(0 \<le> x)\<^sup>e" "(0)\<^sup>e" "(y)\<^sup>e")

end


subsubsection \<open> Dynamics: Exponential decay (1) \<close>

context two_vars
begin

(* proof with solutions *)
(* x>0 -> [{x'=-x}]x>0 *)
lemma "(x > 0)\<^sub>e \<le> |{x` = -x}] (x > 0)"
  apply (subst fbox_solve[where \<phi>="\<lambda>t. [x \<leadsto> x * exp (- \<guillemotleft>t\<guillemotright>)]"]; clarsimp?)
  by (local_flow 1) expr_auto
 
(* proof with ghosts *)
(* x>0 -> [{x'=-x}]x>0 *)
lemma "(x > 0)\<^sub>e \<le> |{x` = -x}] (x > 0)"
   apply (dGhost "y" "(x*y\<^sup>2 = 1)\<^sub>e" "1/2")
  by (expr_auto add: exp_ghost_arith)
    (diff_inv_on_eq)

end


subsubsection \<open> Dynamics: Exponential decay (2) \<close>  (**)

context two_vars
begin

(* proof with solutions *)
(* x>0 -> [{x'=-x+1}]x>0 *)
lemma "(x > 0)\<^sub>e \<le> |{x` = -x + 1}] (x > 0)"
  apply (subst fbox_solve[where \<phi>="\<lambda>t. [x \<leadsto> 1 - exp (- \<guillemotleft>t\<guillemotright>) + x * exp (- \<guillemotleft>t\<guillemotright>)]"]; clarsimp?)
  by (local_flow 1, expr_auto) 
    (metis add_pos_nonneg diff_gt_0_iff_gt exp_eq_one_iff 
      exp_ge_zero exp_less_one_iff less_eq_real_def mult.commute mult_1 
      neg_equal_zero real_0_less_add_iff right_minus_eq zero_le_mult_iff)


(* proof with ghosts *)
(* x>0 -> [{x'=-x+1}]x>0 *)
lemma "(x > 0)\<^sub>e \<le> |{x` = -x + 1}] (x > 0)"
   apply (dGhost "y" "(x*y\<^sup>2 = 1)\<^sub>e" "1/2") (* find adequate ghost *)
    apply (expr_auto add: exp_ghost_arith)
  apply (diff_inv_on_eq)
  oops

end


subsubsection \<open> Dynamics: Exponential decay (3) \<close> (**)

context two_vars
begin

(* x>0 & y>0->[{x'=-y*x}]x>0 *)
lemma "`y > 0` \<Longrightarrow> (x > 0)\<^sub>e \<le> |{x` = - y * x}] (x > 0)"
  apply (subst fbox_solve[where \<phi>="\<lambda>t. [x \<leadsto> x * exp (- \<guillemotleft>t\<guillemotright> * y)]"]; clarsimp?)
   apply (unfold local_flow_on_def, clarsimp, unfold_locales; expr_simp)
  subgoal for s apply (lipschitz "get\<^bsub>y\<^esub> s")
    using less_eq_real_def apply presburger
    by (metis abs_1 abs_mult_pos dist_commute dist_scaleR 
        less_eq_real_def mult.commute mult_1 real_norm_def 
        real_scaleR_def)
  by (auto intro!: poly_derivatives) expr_simp

end


subsubsection \<open> Dynamics: Exponential growth (1) \<close> (**)

context two_vars
begin

(* x>=0 -> [{x'=x}]x>=0 *)
lemma "(x \<ge> 0)\<^sub>e \<le> |{x` = x}] (x \<ge> 0)"
  apply (subst fbox_solve[where \<phi>="\<lambda>t. [x \<leadsto> x * exp \<guillemotleft>t\<guillemotright>]"]; clarsimp?)
  by (local_flow 1) expr_auto 

(* proof with ghosts *)
(* x>=0 -> [{x'=x}]x>=0 *)
lemma "(x \<ge> 0)\<^sub>e \<le> |{x` = x}] (x \<ge> 0)"
   apply (dGhost "y" "(x*y\<^sup>2 = 1 \<or> x=0)\<^sub>e" "1/2") (* find adequate ghost *)
   apply (expr_auto add: exp_ghost_arith)
  oops

end


subsubsection \<open> Dynamics: Exponential growth (2) \<close>

context two_vars
begin

(* x>=0 & y>=0 -> [{x'=y, y'=y\<^sup>2}]x>=0 *)
lemma "(x \<ge> 0 \<and> y \<ge> 0)\<^sub>e \<le> |{x` = y, y` = y\<^sup>2}] (x \<ge> 0)"
  by (diff_cut_ineq "(0 \<le> y)\<^sup>e" "(0)\<^sup>e" "(y\<^sup>2)\<^sup>e")
    (diff_inv_on_weaken_ineq "(0 \<le> x)\<^sup>e" "(0)\<^sup>e" "(y)\<^sup>e")

end


subsubsection \<open> Dynamics: Exponential growth (4) \<close> (* sic *)

context two_vars
begin

(* x>0 -> [{x'=x^x}]x>0 *)
lemma "(x > 0)\<^sub>e \<le> |{x` = x powr x}] (x > 0)"
  by (diff_inv_on_ineq "(0)\<^sup>e" "(x powr x)\<^sup>e")

end


subsubsection \<open> Dynamics: Exponential growth (5) \<close>

context two_vars
begin

(* x>=1 -> [{x'=x\<^sup>2+2*x^4}]x^3>=x\<^sup>2 *)
lemma "(x \<ge> 1)\<^sub>e \<le> |{x` = x\<^sup>2 + 2 * x^4}] (x^3 \<ge> x\<^sup>2)"
  apply (rule diff_cut_on_rule[where C="(1 \<le> x)\<^sup>e"])
   apply (diff_inv_on_ineq "(0)\<^sup>e" "(x\<^sup>2 + 2 * x^4)\<^sup>e")
  apply (rule diff_cut_on_rule[where C="(x\<^sup>2 \<le> x^3)\<^sup>e"])
   apply (rule fbox_inv[where I="(x\<^sup>2 \<le> x^3)\<^sup>e"])
     apply (expr_simp add: le_fun_def numeral_Bit1 field_simps)
  apply (simp only: expr_defs hoare_diff_inv_on fbox_diff_inv_on)
  apply (diff_inv_on_single_ineq_intro "(2 * x * (x\<^sup>2 + 2 * x^4))\<^sup>e" "(3 * x\<^sup>2 * (x\<^sup>2 + 2 * x^4))\<^sup>e"; clarsimp)
     apply(auto intro!: poly_derivatives simp: field_simps semiring_normalization_rules(27,28))[1]
  subgoal for X \<tau>
    apply (move_left "2::real", move_left "3::real", move_left "4::real", move_left "6::real")
    by mon_pow_simp (smt (z3) mult_le_cancel_left numerals(1) pos2 
        power_commutes power_numeral_even power_numeral_odd 
        power_one_right self_le_power)
     apply(auto intro!: poly_derivatives simp: field_simps semiring_normalization_rules(27,28))[1]
  by expr_auto (rule diff_weak_on_rule, expr_auto)

end


subsubsection \<open> Dynamics: Rotational dynamics (1) \<close>

context two_vars
begin

(* x\<^sup>2+y\<^sup>2=1 -> [{x'=-y, y'=x}]x\<^sup>2+y\<^sup>2=1 *)
lemma "(x\<^sup>2 + y\<^sup>2 = 1)\<^sub>e \<le> |{x` = -y, y` = x}] (x\<^sup>2 + y\<^sup>2 = 1)"
  by (diff_inv_on_eq)

end


subsubsection \<open> Dynamics: Rotational dynamics (2) \<close> (* prove as a linear system *)

context three_vars
begin

(* x\<^sup>2+y\<^sup>2=1 & e=x -> [{x'=-y, y'=e, e'=-y}](x\<^sup>2+y\<^sup>2=1 & e=x) *)
lemma "(x\<^sup>2 + y\<^sup>2 = 1 \<and> z = x)\<^sub>e \<le> |{x` = -y, y` = z, z` = -y}] (x\<^sup>2 + y\<^sup>2 = 1 \<and> z = x)"
  apply (rule diff_cut_on_rule[where C="(z = x)\<^sup>e"])
   apply (rule fbox_inv[where I="(z = x)\<^sup>e"])
     apply (expr_simp add: le_fun_def)
    apply (diff_inv_on_eq)
   apply (expr_simp add: le_fun_def)
  apply (rule diff_cut_on_rule[where C="(z\<^sup>2 + y\<^sup>2 = 1)\<^sup>e"])
   apply (rule fbox_inv[where I="(z\<^sup>2 + y\<^sup>2 = 1)\<^sup>e"])
     apply (expr_simp add: le_fun_def)
    apply (diff_inv_on_eq)
  by (expr_simp add: le_fun_def)
    (rule diff_weak_on_rule, expr_auto)

end

subsubsection \<open> Dynamics: Rotational dynamics (3) \<close>

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

(* d1\<^sup>2+d2\<^sup>2=w\<^sup>2*p\<^sup>2 & d1=-w*x2 & d2=w*x1 -> 
  [{x1'=d1, x2'=d2, d1'=-w*d2, d2'=w*d1}]
  (d1\<^sup>2+d2\<^sup>2=w\<^sup>2*p\<^sup>2 & d1=-w*x2 & d2=w*x1)*)
lemma "(d1\<^sup>2 + d2\<^sup>2 = \<guillemotleft>w\<guillemotright>\<^sup>2 * \<guillemotleft>p\<guillemotright>\<^sup>2 \<and> d1 = - \<guillemotleft>w\<guillemotright> * x2 \<and> d2 = \<guillemotleft>w\<guillemotright> * x1)\<^sub>e \<le>
  |{x1` = d1, x2` = d2, d1` = - \<guillemotleft>w\<guillemotright> * d2, d2` = \<guillemotleft>w\<guillemotright> * d1}] 
  (d1\<^sup>2 + d2\<^sup>2 = \<guillemotleft>w\<guillemotright>\<^sup>2 * \<guillemotleft>p\<guillemotright>\<^sup>2 \<and> d1 = - \<guillemotleft>w\<guillemotright> * x2 \<and> d2 = \<guillemotleft>w\<guillemotright> * x1)"
  by (rule fbox_invs; (rule fbox_invs)?) diff_inv_on_eq+

end


subsubsection \<open> Dynamics: Spiral to equilibrium \<close>

context four_vars
begin

(* w>=0 & x=0 & y=3 -> [{x'=y, y'=-w\<^sup>2*x-2*w*y}]w\<^sup>2*x\<^sup>2+y\<^sup>2<=9 *)
lemma "(w \<ge> 0 \<and> x = 0 \<and> y = 3)\<^sub>e \<le> |{x` = y, y` = - w\<^sup>2 * x - 2 * w * y}] (w\<^sup>2 * x\<^sup>2 + y\<^sup>2 \<le> 9)"
  apply (rule diff_cut_on_rule[where C="(0 \<le> w)\<^sup>e"])
   apply (rule fbox_inv[where I="(0 \<le> w)\<^sup>e"])
     apply (expr_simp add: le_fun_def)
    apply (diff_inv_on_ineq "(0)\<^sup>e" "(0)\<^sup>e")
   apply (expr_simp add: le_fun_def)
   apply (rule fbox_inv[where I="(w\<^sup>2 * x\<^sup>2 + y\<^sup>2 \<le> 9)\<^sup>e"])
    apply (expr_simp add: le_fun_def)
   apply (simp only: expr_defs hoare_diff_inv_on fbox_diff_inv_on)?
   apply (diff_inv_on_single_ineq_intro "(2 * w\<^sup>2 * x * y + 2 * y * (- w\<^sup>2 * x - 2 * w * y))\<^sup>e" "(0)\<^sup>e"; expr_simp)
    apply (force simp: field_simps)[1]
   apply (force intro!: poly_derivatives)
  by (expr_simp add: le_fun_def)

end


subsubsection \<open> Dynamics: Open cases \<close>

lemma has_vderiv_mono_test:
  assumes T_hyp: "is_interval T" 
    and d_hyp: "D f = f' on T"
    and xy_hyp: "x\<in>T" "y\<in>T" "x \<le> y" 
  shows "\<forall>x\<in>T. (0::real) \<le> f' x \<Longrightarrow> f x \<le> f y"
    and "\<forall>x\<in>T. f' x \<le> 0 \<Longrightarrow> f x \<ge> f y"
proof-
  have "{x..y} \<subseteq> T"
    using T_hyp xy_hyp by (meson atLeastAtMost_iff mem_is_interval_1_I subsetI) 
  hence "D f = f' on {x..y}"
    using has_vderiv_on_subset[OF d_hyp(1)] by blast
  hence "(\<And>t. x \<le> t \<Longrightarrow> t \<le> y \<Longrightarrow> D f \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R f' t) at t within {x..y})"
    unfolding has_vderiv_on_def has_vector_derivative_def by auto
  then obtain c where c_hyp: "c \<in> {x..y} \<and> f y - f x = (y - x) *\<^sub>R f' c"
    using mvt_very_simple[OF xy_hyp(3), of f "(\<lambda>t \<tau>. \<tau> *\<^sub>R f' t)"] by blast
  hence mvt_hyp: "f x = f y - f' c * (y - x)"
    by (simp add: mult.commute)
  also have "\<forall>x\<in>T. 0 \<le> f' x \<Longrightarrow> ... \<le> f y"
    using xy_hyp d_hyp c_hyp \<open>{x..y} \<subseteq> T\<close> by auto
  finally show "\<forall>x\<in>T. 0 \<le> f' x \<Longrightarrow> f x \<le> f y" .
  have "\<forall>x\<in>T. f' x \<le> 0 \<Longrightarrow> f y - f' c * (y - x) \<ge> f y"
    using xy_hyp d_hyp c_hyp \<open>{x..y} \<subseteq> T\<close> by (auto simp: mult_le_0_iff)
  thus "\<forall>x\<in>T. f' x \<le> 0 \<Longrightarrow> f x \<ge> f y"
    using mvt_hyp by auto
qed

lemma continuous_on_ge_ball_ge: 
  "continuous_on T f \<Longrightarrow> x \<in> T \<Longrightarrow> f x > (k::real) \<Longrightarrow> \<exists>\<epsilon>>0. \<forall>y\<in>ball x \<epsilon> \<inter> T. f y > k"
  unfolding continuous_on_iff apply(erule_tac x=x in ballE; clarsimp?)
  apply(erule_tac x="f x - k" in allE, clarsimp simp: dist_norm)
  apply(rename_tac \<delta>, rule_tac x=\<delta> in exI, clarsimp)
  apply(erule_tac x=y in ballE; clarsimp?)
  by (subst (asm) abs_le_eq, simp_all add: dist_commute)

lemma current_vderiv_ge_always_ge:
  fixes c::real
  assumes init: "c < x t\<^sub>0" and ode: "D x = x' on {t\<^sub>0..}" 
    and dhyp: "x' = (\<lambda>t. g (x t))" "\<forall>x\<ge>c. g x \<ge> 0"
  shows "\<forall>t\<ge>t\<^sub>0. x t > c"
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
      using continuous_on_ge_ball_ge[of _ "\<lambda>t. x t", OF cont _ \<open>c < x t\<^sub>1\<close>] \<open>t\<^sub>0  \<le> t\<^sub>1\<close> by auto
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

(* x^3>5 & y>2 -> [{x'=x^3+x^4, y'=5*y+y^2}](x^3>5 & y>2) *)
lemma "0 \<le> t \<Longrightarrow> (\<lambda>s::real^2. s$1^3>5 \<and> s$2>2) \<le> 
  |x\<acute>= (\<lambda>t s. (\<chi> i. if i=1 then s$1^3 + s$1^4 else 5 * s$2 + s$2^2)) & G on (\<lambda>s. {0..}) UNIV @ 0]
  (\<lambda>s. s$1^3>5 \<and> s$2>2)"
  apply(simp, rule diff_inv_rules, simp_all add: diff_inv_eq ivp_sols_def forall_2; clarsimp)
   apply(frule_tac x="\<lambda>t. X t $ 1 ^ 3" and g="\<lambda>t. 3 * t^2 + 3 * (root 3 t)^5" in current_vderiv_ge_always_ge)
      apply(rule poly_derivatives, simp, assumption, simp)
  apply (rule ext)
     apply (auto simp: field_simps odd_real_root_power_cancel)[1]
  apply (smt (verit, ccfv_SIG) numeral_One power3_eq_cube power4_eq_xxxx power_add_numeral power_commutes power_one_right semiring_norm(5) semiring_norm(8))
  apply (force simp: add_nonneg_pos, force)
  apply(frule_tac x="\<lambda>t. X t $ 2" in current_vderiv_ge_always_ge)
  by (force, force, force simp: add_nonneg_pos, simp)


subsubsection \<open> Dynamics: Closed cases \<close>

(* x>=1 & y=10 & z=-2 -> [{x'=y, y'=z+y^2-y & y>=0}](x>=1 & y>=0) *)
lemma "z = - 2 \<Longrightarrow> (\<lambda>s::real^2. s$1 \<ge> 1 \<and> s$2 = 10) \<le> 
  |x\<acute>= (\<lambda>s. (\<chi> i. if i=1 then s$2 else z + (s$2)^2 - s$2)) & (\<lambda>s. s$2 \<ge> 0)]
  (\<lambda>s. s$1 \<ge> 1 \<and> s$2 \<ge> 0)"
  apply(subst g_ode_inv_def[symmetric, where I="\<lambda>s. s$1 \<ge> 1 \<and> s$2 \<ge> 0"])
  apply(rule fbox_g_odei, simp_all, simp add: le_fun_def, rule diff_inv_rules)
   apply(rule_tac \<nu>'="\<lambda>s. 0" and \<mu>'="\<lambda>s. s$2" in diff_inv_rules(2))
  by (simp_all add: diff_inv_eq, force intro!: poly_derivatives)


subsubsection \<open> Dynamics: Conserved quantity \<close>

lemma dyn_cons_qty_arith: "(36::real) * (x1\<^sup>2 * (x1 * x2 ^ 3)) - 
  (- (24 * (x1\<^sup>2 * x2) * x1 ^ 3 * (x2)\<^sup>2) - 12 * (x1\<^sup>2 * x2) * x1 * x2 ^ 4) - 
  36 * (x1\<^sup>2 * (x2 * x1)) * (x2)\<^sup>2 - 12 * (x1\<^sup>2 * (x1 * x2 ^ 5)) = 24 * (x1 ^ 5 * x2 ^ 3)" 
  (is "?t1 - (- ?t2 - ?t3) - ?t4 - ?t5 = ?t6")
proof-
  have eq1: "?t1 = ?t4"
    by (simp add: power3_eq_cube power2_eq_square)
  have eq2: "- (- ?t2 - ?t3) = (?t6 + ?t3)"
    by (auto simp: field_simps semiring_normalization_rules(27) power_numeral_odd)
  have eq3: "?t3 = ?t5"
    by (auto simp: field_simps semiring_normalization_rules(27))
  show "?t1 - (- ?t2 - ?t3) - ?t4 - ?t5 = ?t6"
    unfolding eq1 eq2 eq3 
    by (simp add: field_simps semiring_normalization_rules(27) power_numeral_odd)
qed

(* x1^4*x2^2+x1^2*x2^4-3*x1^2*x2^2+1 <= c ->
    [{x1'=2*x1^4*x2+4*x1^2*x2^3-6*x1^2*x2, x2'=-4*x1^3*x2^2-2*x1*x2^4+6*x1*x2^2}] 
   x1^4*x2^2+x1^2*x2^4-3*x1^2*x2^2+1 <= c *)
lemma "(\<lambda>s::real^2. (s$1)^4*(s$2)^2+(s$1)^2*(s$2)^4-3*(s$1)^2*(s$2)^2 + 1 \<le> c) \<le> 
  |x\<acute>= (\<lambda>s. (\<chi> i. if i=1 then 2*(s$1)^4*(s$2)+4*(s$1)^2*(s$2)^3-6*(s$1)^2*(s$2) 
    else -4*(s$1)^3*(s$2)^2-2*(s$1)*(s$2)^4+6*(s$1)*(s$2)^2)) & G] 
  (\<lambda>s. (s$1)^4*(s$2)^2+(s$1)^2*(s$2)^4-3*(s$1)^2*(s$2)^2 + 1 \<le> c)"
  apply(simp, rule_tac \<mu>'="\<lambda>s. 0" and \<nu>'="\<lambda>s. 0" in diff_inv_rules(2); clarsimp simp: forall_2)
  apply(intro poly_derivatives; (assumption)?, (rule poly_derivatives)?)
  apply force+
  apply(clarsimp simp: algebra_simps(17,18,19,20) semiring_normalization_rules(27,28))
  by (auto simp: dyn_cons_qty_arith)


subsubsection \<open> Dynamics: Darboux equality \<close>

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

(* x+z=0 -> [{x'=(A*x^2+B()*x), z' = A*z*x+B()*z}] 0=-x-z *)
lemma "(\<lambda>s::real^2. s$1 + s$2 = 0) \<le> 
  |x\<acute>= (\<lambda>t s. (\<chi> i. if i=1 then A*(s$1)^2+B*(s$1) else A*(s$2)*(s$1)+B*(s$2))) & G on (\<lambda>s. UNIV) UNIV @ 0]
  (\<lambda>s. 0 = - s$1 - s$2)"
proof-
  have key: "diff_inv (\<lambda>s. s $ 1 + s $ 2 = 0)
     (\<lambda>t s. \<chi> i. if i = 1 then A*(s$1)^2+B*(s$1) else A*(s$2)*(s$1)+B*(s$2)) (\<lambda>s. UNIV) UNIV 0 G"
  proof(clarsimp simp: diff_inv_eq ivp_sols_def forall_2)
    fix X::"real\<Rightarrow>real^2" and t::real
    let "?c" = "(\<lambda>t.  X t $ 1 + X t $ 2)"
    assume init: "?c 0 = 0"
      and D1: "D (\<lambda>t. X t $ 1) = (\<lambda>t. A * (X t $ 1)\<^sup>2 + B * X t $ 1) on UNIV"
      and D2: "D (\<lambda>t. X t $ 2) = (\<lambda>t. A * X t $ 2 * X t $ 1 + B * X t $ 2) on UNIV"
    hence "D ?c = (\<lambda>t. ?c t * (A * (X t $ 1) + B)) on UNIV"
      by (auto intro!: poly_derivatives simp: field_simps)
    hence "D ?c = (\<lambda>t. (A * X t $ 1 + B) * (X t $ 1 + X t $ 2)) on {0--t}"
      using has_vderiv_on_subset[OF _ subset_UNIV[of "{0--t}"]] by (simp add: mult.commute)
    moreover have "continuous_on UNIV (\<lambda>t. A * (X t $ 1) + B)"
      apply(rule vderiv_on_continuous_on)
      using D1 by (auto intro!: poly_derivatives simp: field_simps)
    moreover have "D (\<lambda>t. 0) = (\<lambda>t. (A * X t $ 1 + B) * 0) on {0--t}"
      by (auto intro!: poly_derivatives)
    moreover note picard_lindeloef.ivp_unique_solution[OF 
      picard_lindeloef_first_order_linear[OF UNIV_I open_UNIV is_interval_univ calculation(2)] 
      UNIV_I is_interval_closed_segment_1 subset_UNIV _ 
      ivp_solsI[of ?c]
      ivp_solsI[of "\<lambda>t. 0"], of t "\<lambda>s. 0" 0 "\<lambda>s. t" 0]
    ultimately show "X t $ 1 + X t $ 2 = 0"
      using init by auto
  qed
  show ?thesis
    apply(subgoal_tac "(\<lambda>s. 0 = - s$1 - s$2) = (\<lambda>s. s$1 + s$2 = 0)", erule ssubst)
    using key by auto
qed


subsubsection \<open> Dynamics: Fractional Darboux equality \<close> (*N 30 *)

(* x+z=0 -> [{x'=(A*y+B()*x)/z^2, z' = (A*x+B())/z & y = x^2 & z^2 > 0}] x+z=0 *)
(* requires picard-lindeloef for closed intervals *)

subsubsection \<open> Dynamics: Darboux inequality \<close> (*N 31 *)

abbreviation darboux_ineq_f :: "real^2 \<Rightarrow> real^2" ("f")
  where "f s \<equiv> (\<chi> i. if i=1 then (s$1)^2 else (s$2)*(s$1)+(s$1)^2)"

abbreviation darboux_ineq_flow2 :: "real \<Rightarrow> real^2 \<Rightarrow> real^2" ("\<phi>")
  where "\<phi> t s \<equiv> (\<chi> i. if i=1 then (s$1/(1 - t * s$1)) else
      (s$2 - s$1 * ln(1 - t * s$1))/(1 - t * s$1))"

lemma darboux_flow_ivp: "(\<lambda>t. \<phi> t s) \<in> Sols (\<lambda>s. {t. 0 \<le> t \<and> t * s $ 1 < 1}) UNIV (\<lambda>t. f) 0 s"
  by (rule ivp_solsI) (auto intro!: poly_derivatives 
      simp: forall_2 add_divide_distrib power_divide vec_eq_iff power2_eq_square)

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

(* x+z>=0 -> [{x'=x^2, z' = z*x+y & y = x^2}] x+z>=0 *)
(* x' + z' \<ge> 0 \<longleftrightarrow> x^2 + z*x + x^2 \<ge> 0*)
lemma "(\<lambda>s::real^2. s$1 + s$2 \<ge> 0) \<le> 
  |EVOL \<phi> (\<lambda>s. y = (s$1)^2) (\<lambda>s. {t. 0 \<le> t \<and> t * s $ 1 < 1})]
  (\<lambda>s. s$1 + s$2 \<ge> 0)"
  apply(subst fbox_g_evol, simp_all add: le_fun_def)
  using darboux_ineq_arith by smt

no_notation darboux_ineq_flow2 ("\<phi>")
        and darboux_ineq_f ("f")

(* interval of existence or invariant rule for \<le> *)


subsubsection \<open> Dynamics: Bifurcation \<close>

lemma picard_lindeloef_dyn_bif: "continuous_on T (g::real \<Rightarrow> real) \<Longrightarrow> t\<^sub>0 \<in> T \<Longrightarrow> is_interval T \<Longrightarrow> 
  open T \<Longrightarrow> picard_lindeloef (\<lambda>t \<tau>::real. r + \<tau>^2) T UNIV t\<^sub>0"
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

(* r <= 0 -> \exists f (x=f -> [{x'=r+x^2}]x=f) *)
lemma "r \<le> 0 \<Longrightarrow> \<exists>c. (\<lambda>s::real^1. s$1 = c) \<le> 
  |x\<acute>= (\<lambda>t s. (\<chi> i. r + (s$1)^2)) & G on (\<lambda>s. UNIV) UNIV @ 0] 
  (\<lambda>s. s$1 = c)"
proof(rule_tac x="sqrt \<bar>r\<bar>" in exI, clarsimp simp: diff_inv_eq ivp_sols_def)
  fix X::"real\<Rightarrow>real^1" and t::real
  assume init: "X 0 $ 1 = sqrt (- r)" and "r \<le> 0"
     and D1: "D (\<lambda>x. X x $ 1) = (\<lambda>x. r + (X x $ 1)\<^sup>2) on UNIV"
  hence "D (\<lambda>x. X x $ 1) = (\<lambda>x. r + (X x $ 1)\<^sup>2) on {0--t}"
    using has_vderiv_on_subset by blast
  moreover have "continuous_on UNIV (\<lambda>t. X t $ 1)"
    apply(rule vderiv_on_continuous_on)
    using D1 by assumption
  moreover have key: "D (\<lambda>t. sqrt (- r)) = (\<lambda>t. r + (sqrt (- r))\<^sup>2) on {0--t}"
    apply(subgoal_tac "(\<lambda>t. r + (sqrt (- r))\<^sup>2) = (\<lambda>t. 0)")
     apply(erule ssubst, rule poly_derivatives)
    using \<open>r \<le> 0\<close> by auto
  moreover note picard_lindeloef.ivp_unique_solution[OF 
      picard_lindeloef_dyn_bif[OF calculation(2) UNIV_I is_interval_univ open_UNIV] 
      UNIV_I is_interval_closed_segment_1 subset_UNIV _ 
      ivp_solsI[of "\<lambda>x. X x $ 1" _ "\<lambda>s. {0--t}" "sqrt (- r)" 0]
      ivp_solsI[of "\<lambda>t. sqrt (- r)" _], of t r]
  ultimately show "X t $ 1 = sqrt (- r)"
    using \<open>r \<le> 0\<close> init by auto
qed

subsubsection \<open> Dynamics: Parametric switching between two different damped oscillators \<close> (*N 33 *)

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

(* verified with the help of a CAS *)


subsubsection \<open> Dynamics: Nonlinear 1 \<close>

(* x^3 >= -1 -> [{x'=(x-3)^4+a & a>=0}] x^3>=-1 *)
lemma "(\<lambda>s::real^1. s$1^3 \<ge> -1) \<le> 
  |x\<acute>= (\<lambda>s. \<chi> i. (s$1 - 3)^4 + a) & (\<lambda>s. a \<ge> 0)]
  (\<lambda>s. s$1^3 \<ge> -1)"
  apply(simp, rule_tac \<nu>'="\<lambda>s. 0" and \<mu>'="\<lambda>s. 3 * s$1^2 * ((s$1 - 3)^4 + a)" in diff_inv_rules(2))
  by (auto intro!: poly_derivatives)


subsubsection \<open> Dynamics: Nonlinear 2 \<close>

(* x1+x2^2/2=a -> [{x1'=x1*x2,x2'=-x1}]x1+x2^2/2=a *)
lemma "(\<lambda>s::real^2. s$1 + (s$2^2)/2 = a) \<le> 
  |x\<acute>= (\<lambda>s. \<chi> i. if i=1 then s$1 * s$2 else - s$1) & G]
  (\<lambda>s. s$1 + (s$2^2)/2 = a)"
  by (auto intro!: diff_inv_rules poly_derivatives)


subsubsection \<open> Dynamics: Nonlinear 4 \<close>

(* x1^2/2-x2^2/2>=a -> [{x1'=x2+x1*x2^2, x2'=-x1+x1^2*x2 & x1>=0 & x2>=0}]x1^2/2-x2^2/2>=a *)
lemma "(\<lambda>s::real^2. (s$1)^2/2 - (s$2^2)/2 \<ge> a) \<le> 
  |x\<acute>= (\<lambda>s. \<chi> i. if i=1 then s$2 + s$1 * (s$2^2) else - s$1 + s$1^2 * s$2) & (\<lambda>s. s$1 \<ge> 0 \<and> s$2 \<ge> 0)]
  (\<lambda>s. (s$1)^2/2 - (s$2^2)/2 \<ge> a)"
  apply(simp, rule_tac \<nu>'="\<lambda>s. 0" and \<mu>'="\<lambda>s. s$1*(s$2 + s$1 * (s$2^2)) - s$2 * (- s$1 + s$1^2 * s$2)" in diff_inv_rules(2))
  by (auto intro!: poly_derivatives simp: field_simps)


subsubsection \<open> Dynamics: Nonlinear 5 \<close>

(* -x1*x2>=a -> [{x1'=x1-x2+x1*x2, x2'=-x2-x2^2}]-x1*x2>=a *)
lemma "(\<lambda>s::real^2. -(s$1) *(s$2) \<ge> a) \<le> 
  |x\<acute>= (\<lambda>s. \<chi> i. if i=1 then s$1 - s$2 + s$1 * s$2 else - s$2 - s$2^2) & G]
  (\<lambda>s. -(s$1)*(s$2) \<ge> a)"
  apply(simp, rule_tac \<nu>'="\<lambda>s. 0" and \<mu>'="\<lambda>s. (- s$1 + s$2 - s$1 * s$2) * s$2 - s$1 * (- s$2 - s$2^2)" in diff_inv_rules(2))
  by (auto intro!: poly_derivatives simp: field_simps)


subsubsection \<open> Dynamics: Riccati \<close>

(* 2*x^3 >= 1/4 -> [{x'=x^2+x^4}] 2*x^3>=1/4 *)
lemma "(\<lambda>s::real^1. 2 * s$1^3 \<ge> 1/4) \<le> 
  |x\<acute>= (\<lambda>s. \<chi> i. s$1^2 + s$1^4) & G]
  (\<lambda>s. 2 * s$1^3 \<ge> 1/4)"
  apply(simp, rule_tac \<nu>'="\<lambda>s. 0" and \<mu>'="\<lambda>s. 24 * (s$1^2) * (s$1^2 + s$1^4)" in diff_inv_rules(2); clarsimp)
  by (auto intro!: poly_derivatives simp: field_simps)


subsubsection \<open> Dynamics: Nonlinear differential cut \<close>

(* x^3 >= -1 & y^5 >= 0 -> [{x'=(x-3)^4+y^5, y'=y^2}] (x^3 >= -1 & y^5 >= 0) *)
lemma "(\<lambda>s::real^2. s$1^3 \<ge> - 1 \<and> s$2^5 \<ge> 0) \<le> 
  |x\<acute>= (\<lambda>s. \<chi> i. if i=1 then (s$1 - 3)^4 else s$2^2) & G]
  (\<lambda>s. s$1^3 \<ge> - 1 \<and> s$2^5 \<ge> 0)"
  apply(simp, rule diff_inv_rules)
   apply(rule_tac \<nu>'="\<lambda>s. 0" and \<mu>'="\<lambda>s. 3 * s$1^2 * (s$1 - 3)^4" in diff_inv_rules(2))
   apply(simp_all add: forall_2, force intro!: poly_derivatives)
   apply(rule_tac \<nu>'="\<lambda>s. 0" and \<mu>'="\<lambda>s. s$2^2" in diff_inv_rules(2))
  by (auto intro!: diff_inv_rules poly_derivatives simp: forall_2)


subsubsection \<open> STTT Tutorial: Example 1 \<close>

(* v >= 0 & A > 0 -> [ { x' = v, v' = A } ] v >= 0 *)
lemma "A > 0 \<Longrightarrow> (\<lambda>s::real^2. s$2 \<ge> 0) \<le> 
  |x\<acute>= (\<lambda>s. \<chi> i. if i=1 then s$2 else A) & G]
  (\<lambda>s. s$2 \<ge> 0)"
  apply(subst local_flow.fbox_g_ode_subset[where T="UNIV" 
        and \<phi>="\<lambda>t s. \<chi> i::2. if i=1 then A * t^2/2 + s$2 * t + s$1 else A * t + s$2"])
      apply(unfold_locales, simp_all add: local_lipschitz_def forall_2 lipschitz_on_def)
    apply(clarsimp, rule_tac x=1 in exI)+
  apply(clarsimp simp: dist_norm norm_vec_def L2_set_def)
  unfolding UNIV_2 using exhaust_2 by (auto intro!: poly_derivatives simp: vec_eq_iff)


subsubsection \<open> STTT Tutorial: Example 2 \<close>

(* v >= 0 & A > 0 & B > 0 -> 
  [
    { {a := A; ++ a := 0; ++ a := -B;};
      { x' = v, v' = a & v >= 0 }
    }*@invariant(v >= 0)
  ] v >= 0 *)

lemma local_flow_STTT_Ex2:
  "local_flow (\<lambda>s::real^3. \<chi> i. if i = 1 then s$2 else (if i=2 then s$3 else 0)) UNIV UNIV
  (\<lambda>t s. \<chi> i. if i = 1 then s$3 * t^2/2 + s$2 * t + s$1 else (if i=2 then s$3 * t + s$2 else s$i))"
  apply(unfold_locales, simp_all add: local_lipschitz_def forall_2 lipschitz_on_def)
    apply(clarsimp, rule_tac x=1 in exI)+
  apply(clarsimp simp: dist_norm norm_vec_def L2_set_def)
  unfolding UNIV_3 by (auto intro!: poly_derivatives simp: forall_3 vec_eq_iff)

lemma "A > 0 \<Longrightarrow> B > 0 \<Longrightarrow> (\<lambda>s::real^3. s$2 \<ge> 0) \<le>
  |LOOP (
    (\<lambda>s. (3 ::= (\<lambda>s. A)) s \<union> (3 ::= (\<lambda>s. 0)) s \<union> (3 ::= (\<lambda>s. B)) s);
    (x\<acute>= (\<lambda>s. \<chi> i. if i=1 then s$2 else (if i=2 then s$3 else 0)) & (\<lambda>s. s$2 \<ge> 0))
  ) INV (\<lambda>s. s$2 \<ge> 0)]
  (\<lambda>s. s$2 \<ge> 0)"
  apply(rule fbox_loopI, simp_all add: le_fbox_choice_iff, intro conjI)
  by (simp_all add: local_flow.fbox_g_ode_subset[OF local_flow_STTT_Ex2], simp_all add: le_fun_def)


subsubsection \<open> STTT Tutorial: Example 3a \<close> (* 37 *)

(* v >= 0 & A > 0 & B > 0 & x+v^2/(2*B) < S
 -> [
      { {   ?x+v^2/(2*B) < S; a := A;
         ++ ?v=0; a := 0;
         ++ a := -B;
        }

        {
           {x' = v, v' = a & v >= 0 & x+v^2/(2*B) <= S}
        ++ {x' = v, v' = a & v >= 0 & x+v^2/(2*B) >= S}
        }
      }*@invariant(v >= 0 & x+v^2/(2*B) <= S)
    ] x <= S *)

lemma STTexample3a_arith:
  assumes "0 < (B::real)" "0 \<le> t" "0 \<le> x2" and key: "x1 + x2\<^sup>2 / (2 * B) \<le> S"
  shows "x2 * t - B * t\<^sup>2 / 2 + x1 + (x2 - B * t)\<^sup>2 / (2 * B) \<le> S" (is "?lhs \<le> S")
proof-
  have "?lhs = 2 * B * x2 * t/(2*B) - B^2 * t\<^sup>2 / (2*B) + (2 * B * x1)/(2*B) + (x2 - B * t)\<^sup>2 / (2 * B)"
    using \<open>0 < B\<close> by (auto simp: power2_eq_square)
  also have "(x2 - B * t)\<^sup>2 / (2 * B) = x2^2/(2*B) + B^2 * t^2/(2*B) - 2*x2*B*t/(2*B)"
    using \<open>0 < B\<close> by (auto simp: power2_diff field_simps)
  ultimately have "?lhs = x1 + x2\<^sup>2 / (2 * B)"
    using \<open>0 < B\<close> by auto
  thus "?lhs \<le> S"
    using key by simp
qed

lemma "A > 0 \<Longrightarrow> B > 0 \<Longrightarrow> (\<lambda>s::real^3. s$2 \<ge> 0 \<and> s$1 + s$2^2/(2*B) < S) \<le>
  |LOOP (
    (\<lambda>s. (\<questiondown>\<lambda>s. s$1 + s$2^2/(2*B) < S?;(3 ::= (\<lambda>s. A))) s \<union> (\<questiondown>\<lambda>s. s$2 = 0?;(3 ::= (\<lambda>s. 0))) s \<union> (3 ::= (\<lambda>s. - B)) s);
    (\<lambda>s. (x\<acute>= (\<lambda>s. \<chi> i. if i=1 then s$2 else (if i=2 then s$3 else 0)) & (\<lambda>s. s$2 \<ge> 0 \<and> s$1 + s$2^2/(2*B) \<le> S)) s \<union>
     (x\<acute>= (\<lambda>s. \<chi> i. if i=1 then s$2 else (if i=2 then s$3 else 0)) & (\<lambda>s. s$2 \<ge> 0 \<and> s$1 + s$2^2/(2*B) \<ge> S)) s)
  ) INV (\<lambda>s. s$2 \<ge> 0 \<and> s$1 + s$2^2/(2*B) \<le> S)]
  (\<lambda>s. s$1 \<le> S)"
  apply(rule fbox_loopI, simp add: le_fun_def, simp add: le_fun_def)
   apply (smt not_sum_power2_lt_zero zero_compare_simps(5))
  apply(simp add: fbox_choice local_flow.fbox_g_ode_subset[OF local_flow_STTT_Ex2])
  apply(simp add: le_fun_def, safe)
     apply(erule_tac x=0 in allE)
  by (auto simp: STTexample3a_arith)


subsubsection \<open> STTT Tutorial: Example 4a \<close>

(* v <= V & A > 0
 -> [
      { {
           ?v=V; a:=0;
        ++ ?v!=V; a:=A;
        }

        {x' = v, v' = a & v <= V}
      }*@invariant(v <= V)
    ] v <= V *)

lemma "A > 0 \<Longrightarrow> (\<lambda>s::real^3. s$2 \<le> V) \<le> 
  |LOOP 
    (\<lambda>s. (\<questiondown>\<lambda>s. s$2 = V?;(3 ::= (\<lambda>s. 0))) s \<union> (\<questiondown>\<lambda>s. s$2 \<noteq> V?;(3 ::= (\<lambda>s. A))) s);
    (x\<acute>= (\<lambda>s. \<chi> i. if i=1 then s$2 else (if i=2 then s$3 else 0)) & (\<lambda>s. s$2 \<le> V))
  INV (\<lambda>s. s$2 \<le> V)]
  (\<lambda>s. s$2 \<le> V)"
  by (rule fbox_loopI) 
    (auto simp: fbox_choice local_flow.fbox_g_ode_subset[OF local_flow_STTT_Ex2])
 

subsubsection \<open>STTT Tutorial: Example 4b\<close>

(* v <= V & A > 0
 -> [
      { a := A;

        {x' = v, v' = a & v <= V}
      }*@invariant(v <= V)
    ] v <= V *)
lemma "A > 0 \<Longrightarrow> (\<lambda>s::real^3. s$2 \<le> V) \<le>
  |LOOP 
    (3 ::= (\<lambda>s. A));
    (x\<acute>= (\<lambda>s. \<chi> i. if i=1 then s$2 else (if i=2 then s$3 else 0)) & (\<lambda>s. s$2 \<le> V))
  INV (\<lambda>s. s$2 \<le> V)]
  (\<lambda>s. s$2 \<le> V)"
  by (rule fbox_loopI) 
    (auto simp: le_fbox_choice_iff local_flow.fbox_g_ode_subset[OF local_flow_STTT_Ex2])
 

subsubsection \<open>STTT Tutorial: Example 4c\<close>

(* v <= V & A > 0
 -> [
      { {
           ?v=V; a:=0;
        ++ ?v!=V; a:=A;
        }

        {  {x' = v, v' = a & v <= V}
        ++ {x' = v, v' = a & v >= V}}
      }*@invariant(v <= V)
    ] v <= V *)
lemma "A > 0 \<Longrightarrow> (\<lambda>s::real^3. s$2 \<le> V) \<le> 
  |LOOP 
    (\<lambda>s. (\<questiondown>\<lambda>s. s$2 = V?;(3 ::= (\<lambda>s. 0))) s \<union> (\<questiondown>\<lambda>s. s$2 \<noteq> V?;(3 ::= (\<lambda>s. A))) s);
    (\<lambda>s. (x\<acute>= (\<lambda>s. \<chi> i. if i=1 then s$2 else (if i=2 then s$3 else 0)) & (\<lambda>s. s$2 \<le> V)) s \<union>
     (x\<acute>= (\<lambda>s. \<chi> i. if i=1 then s$2 else (if i=2 then s$3 else 0)) & (\<lambda>s. s$2 \<ge> V)) s)
  INV (\<lambda>s. s$2 \<le> V)]
  (\<lambda>s. s$2 \<le> V)"
  apply (rule fbox_loopI) 
    apply (simp_all add: fbox_choice local_flow.fbox_g_ode_subset[OF local_flow_STTT_Ex2])
  by (clarsimp, erule_tac x=0 in allE, auto)


subsubsection \<open> STTT Tutorial: Example 5 \<close>

lemma STTexample5_arith:
  assumes "0 < A" "0 < B" "0 < \<epsilon>" "0 \<le> x2" "0 \<le> (t::real)" 
    and key: "x1 + x2\<^sup>2 / (2 * B) + (A * (A * \<epsilon>\<^sup>2 / 2 + \<epsilon> * x2) / B + (A * \<epsilon>\<^sup>2 / 2 + \<epsilon> * x2)) \<le> S" (is "?k3 \<le> S")
    and ghyp: "\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> \<tau> \<le> \<epsilon>"
  shows "A * t\<^sup>2 / 2 + x2 * t + x1 + (A * t + x2)\<^sup>2 / (2 * B) \<le> S" (is "?k0 \<le> S")
proof-
  have "t \<le> \<epsilon>"
    using ghyp \<open>0 \<le> t\<close> by auto
  hence "A*t^2/2 + t*x2 \<le> A*\<epsilon>^2/2 + \<epsilon>*x2"
    using \<open>0 \<le> t\<close> \<open>0 < A\<close> \<open>0 \<le> x2\<close>
    by (smt (verit, ccfv_SIG) divide_right_mono mult_less_cancel_left mult_right_mono power_less_imp_less_base)
  hence "((A + B)/B) * (A*t^2/2 + t*x2) + x1 + x2\<^sup>2 / (2 * B) \<le>
    x1 + x2\<^sup>2 / (2 * B) + ((A + B)/B) * (A*\<epsilon>^2/2 + \<epsilon>*x2)" (is "?k1 \<le> ?k2")
    using \<open>0 < B\<close> \<open>0 < A\<close> by (smt (verit, ccfv_SIG) divide_pos_pos mult_less_cancel_left) 
  moreover have "?k0 = ?k1"
    using \<open>0 < B\<close> \<open>0 < A\<close> by (auto simp: field_simps power2_sum)
  moreover have "?k2 = ?k3"
    using \<open>0 < B\<close> \<open>0 < A\<close> by (auto simp: field_simps power2_sum)
  ultimately show "?k0 \<le> S"
    using key by linarith
qed

lemma local_flow_STTT_Ex5:
  "local_flow (\<lambda>s::real^4. \<chi> i. if i=1 then s$2 else (if i=2 then s$3 else (if i=3 then 0 else 1))) UNIV UNIV
  (\<lambda>t s. \<chi> i. if i = 1 then s$3 * t^2/2 + s$2 * t + s$1 else (if i=2 then s$3 * t + s$2 else (if i=3 then s$3 else t+s$4)))"
  apply(unfold_locales, simp_all add: local_lipschitz_def forall_2 lipschitz_on_def)
    apply(clarsimp, rule_tac x=1 in exI)+
  apply(clarsimp simp: dist_norm norm_vec_def L2_set_def)
  unfolding UNIV_4 by (auto intro!: poly_derivatives simp: forall_4 vec_eq_iff)

(* v >= 0 & A > 0 & B > 0 & x+v^2/(2*B) <= S & ep > 0
 -> [
      { {   ?x+v^2/(2*B) + (A/B+1)*(A/2*ep^2+ep*v) <= S; a := A;
         ++ ?v=0; a := 0;
         ++ a := -B;
        };

        c := 0;
        { x' = v, v' = a, c' = 1 & v >= 0 & c <= ep }
      }*@invariant(v >= 0 & x+v^2/(2*B) <= S)
    ] x <= S *)
lemma "A > 0 \<Longrightarrow> B > 0 \<Longrightarrow> \<epsilon> > 0 \<Longrightarrow> (\<lambda>s::real^4. s$2 \<ge> 0 \<and> s$1 + s$2^2/(2*B) \<le> S) \<le>
  |LOOP 
    (\<lambda>s.
      (\<questiondown>\<lambda>s. s$1 + s$2^2/(2*B) + (A/B + 1) * (A/2 * \<epsilon>^2 + \<epsilon> * s$2) \<le> S?;(3 ::= (\<lambda>s. A))) s \<union> 
      (\<questiondown>\<lambda>s. s$2 = 0?;(3 ::= (\<lambda>s. 0))) s \<union> 
      (3 ::= (\<lambda>s. - B)) s); 
    (4 ::= (\<lambda>s. 0));
    (x\<acute>= (\<lambda>s. \<chi> i. if i=1 then s$2 else (if i=2 then s$3 else (if i=3 then 0 else 1))) & (\<lambda>s. s$2 \<ge> 0 \<and> s$4 \<le> \<epsilon>))
  INV (\<lambda>s. s$2 \<ge> 0 \<and> s$1 + s$2^2/(2*B) \<le> S)]
  (\<lambda>s. s$1 \<le> S)"
  apply (rule fbox_loopI) 
    apply (simp_all add: fbox_choice local_flow.fbox_g_ode_subset[OF local_flow_STTT_Ex5])
   apply safe
     apply (smt not_sum_power2_lt_zero zero_compare_simps(5))
    apply(rule STTexample5_arith[of A B \<epsilon> "_ $ 2" _ "_ $ 1" S]; (simp)?)
  by (simp add: field_simps, auto simp: STTexample3a_arith[of B _ "_ $ 2" "_ $ 1" S])


subsubsection \<open> STTT Tutorial: Example 6 \<close>

lemma STTexample6_arith:
  assumes "0 < A" "0 < B" "0 < \<epsilon>" "0 \<le> x2" "0 \<le> (t::real)" "- B \<le> k" "k \<le> A"
    and key: "x1 + x2\<^sup>2 / (2 * B) + (A * (A * \<epsilon>\<^sup>2 / 2 + \<epsilon> * x2) / B + (A * \<epsilon>\<^sup>2 / 2 + \<epsilon> * x2)) \<le> S" (is "?k3 \<le> S")
    and ghyp: "\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> 0 \<le> k * \<tau> + x2 \<and> \<tau> \<le> \<epsilon>"
  shows "k * t\<^sup>2 / 2 + x2 * t + x1 + (k * t + x2)\<^sup>2 / (2 * B) \<le> S" (is "?k0 \<le> S")
proof-
  have "0 \<le> k * t + x2 + x2"
    using ghyp \<open>0 \<le> x2\<close> \<open>0 \<le> t\<close> by force
  hence "0 \<le> (k * t + 2 * x2) * t/2"
    by (metis assms(5) divide_nonneg_pos is_num_normalize(1) mult_2 mult_sign_intros(1) rel_simps(51))
  hence f1: "0 \<le> k*t^2/2 + t*x2"
    by (auto simp: field_simps)
  have f2: "0 \<le> (k + B) / B" "(k + B) / B \<le> (A + B) / B"
    using \<open>0 < A\<close> \<open>0 < B\<close> \<open>- B \<le> k\<close> \<open>k \<le> A\<close> divide_le_cancel by (auto, fastforce)
  have "t \<le> \<epsilon>"
    using ghyp \<open>0 \<le> t\<close> by auto
  hence "k*t^2/2 + t*x2 \<le> A*t^2/2 + t*x2"
    using \<open>k \<le> A\<close> by (auto simp: mult_right_mono)
  also have f3: "... \<le> A*\<epsilon>^2/2 + \<epsilon>*x2"
    using \<open>0 \<le> t\<close> \<open>0 < A\<close> \<open>0 \<le> x2\<close> \<open>t \<le> \<epsilon>\<close>
    by (smt field_sum_of_halves mult_right_mono power_less_imp_less_base mult_less_cancel_left)
  finally have "k*t^2/2 + t*x2 \<le> A*\<epsilon>^2/2 + \<epsilon>*x2" .
  hence "((k + B)/B) * (k*t^2/2 + t*x2) \<le> ((A + B)/B) * (A*\<epsilon>^2/2 + \<epsilon>*x2)"
    using f1 f2 \<open>k \<le> A\<close> apply(rule_tac b="((A + B)/B) * (A*t^2/2 + t*x2)" in order.trans)
     apply (rule mult_mono', simp, simp, simp add: mult_right_mono, simp, simp)
    by (metis f3 add_sign_intros(4) assms(1,2) less_eq_real_def mult_zero_left 
        mult_less_cancel_left zero_compare_simps(5))
  hence "((k + B)/B) * (k*t^2/2 + t*x2) + x1 + x2\<^sup>2 / (2 * B) \<le>
    x1 + x2\<^sup>2 / (2 * B) + ((A + B)/B) * (A*\<epsilon>^2/2 + \<epsilon>*x2)" (is "?k1 \<le> ?k2")
    using \<open>0 < B\<close> \<open>0 < A\<close> by (smt mult_less_cancel_left zero_compare_simps(9))
  moreover have "?k0 = ?k1"
    using \<open>0 < B\<close> \<open>0 < A\<close> by (auto simp: field_simps power2_sum)
  moreover have "?k2 = ?k3"
    using \<open>0 < B\<close> \<open>0 < A\<close> by (auto simp: field_simps power2_sum)
  ultimately show "?k0 \<le> S"
    using key by linarith
qed

(* v >= 0 & A > 0 & B > 0 & x+v^2/(2*B) <= S & ep > 0
 -> [
      { {   ?x+v^2/(2*B) + (A/B+1)*(A/2*ep^2+ep*v) <= S; a :=*; ?-B <= a & a <= A;
         ++ ?v=0; a := 0;
         ++ a := -B;
        };

        c := 0;
        { x' = v, v' = a, c' = 1 & v >= 0 & c <= ep }
      }*@invariant(v >= 0 & x+v^2/(2*B) <= S)
    ] x <= S *)
lemma "A > 0 \<Longrightarrow> B > 0 \<Longrightarrow> \<epsilon> > 0 \<Longrightarrow> (\<lambda>s::real^4. s$2 \<ge> 0 \<and> s$1 + s$2^2/(2*B) \<le> S) \<le>
  |LOOP 
    (\<lambda>s.
      (\<questiondown>\<lambda>s. s$1 + s$2^2/(2*B) + (A/B + 1) * (A/2 * \<epsilon>^2 + \<epsilon> * s$2) \<le> S?;(3 ::= ?);\<questiondown>\<lambda>s. -B \<le> s$3 \<and> s$3 \<le> A?) s \<union> 
      (\<questiondown>\<lambda>s. s$2 = 0?;(3 ::= (\<lambda>s. 0))) s \<union> 
      (3 ::= (\<lambda>s. - B)) s); 
    (4 ::= (\<lambda>s. 0));
    (x\<acute>= (\<lambda>s. \<chi> i. if i=1 then s$2 else (if i=2 then s$3 else (if i=3 then 0 else 1))) & (\<lambda>s. s$2 \<ge> 0 \<and> s$4 \<le> \<epsilon>))
  INV (\<lambda>s. s$2 \<ge> 0 \<and> s$1 + s$2^2/(2*B) \<le> S)]
  (\<lambda>s. s$1 \<le> S)"
  apply (rule fbox_loopI) 
    apply (simp_all add: fbox_choice local_flow.fbox_g_ode_subset[OF local_flow_STTT_Ex5])
   apply safe
     apply (smt not_sum_power2_lt_zero zero_compare_simps(5))
    apply(rule STTexample6_arith[of A B \<epsilon> "_$2" _ _ "_$1"]; simp?)
  by (force simp: field_simps, auto simp: STTexample3a_arith STTexample6_arith)


subsubsection \<open> STTT Tutorial: Example 7 \<close>

lemma STTexample7_arith1:
  assumes "(0::real) < A" "0 < b" "0 < \<epsilon>" "0 \<le> v" "0 \<le> t" "k \<le> A"
    and "x + v\<^sup>2 / (2 * b) + (A * (A * \<epsilon>\<^sup>2 / 2 + \<epsilon> * v) / b + (A * \<epsilon>\<^sup>2 / 2 + \<epsilon> * v)) \<le> S" (is "?expr1 \<le> S")
    and guard: "\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> 0 \<le> k * \<tau> + v \<and> \<tau> \<le> \<epsilon>"
  shows "k * t\<^sup>2 / 2 + v * t + x + (k * t + v)\<^sup>2 / (2 * b) \<le> S" (is "?lhs \<le> S")
proof-
  have obs1: "?lhs*(2*b) = k*t\<^sup>2*b + 2 * v * t*b + 2*x*b + (k*t+v)\<^sup>2" (is "_ = ?expr2 k t")
    using \<open>0 < b\<close> by (simp add: field_simps)
  have "?expr2 A \<epsilon> = ?expr1*(2*b)"
    using \<open>0 < b\<close> by (simp add: field_simps)
  also have "... \<le> S*(2*b)"
    using \<open>?expr1 \<le> S\<close> \<open>0 < b\<close> by force 
  finally have obs2: "?expr2 A \<epsilon> \<le> S*(2*b)" .
  have "t \<le> \<epsilon>"
    using guard \<open>0 \<le> t\<close> by auto
  hence "t\<^sup>2 \<le> \<epsilon>\<^sup>2" "k * t + v \<le> A * \<epsilon> + v"
    using \<open>k \<le> A\<close> \<open>0 < A\<close> power_mono[OF \<open>t \<le> \<epsilon>\<close> \<open>0 \<le> t\<close>, of 2] 
    by auto (meson \<open>0 \<le> t\<close> less_eq_real_def mult_mono)
  hence "k * t\<^sup>2 * b \<le> A * \<epsilon>\<^sup>2 * b" "2 * v * t * b \<le> 2 * v * \<epsilon> * b"
    using \<open>t \<le> \<epsilon>\<close> \<open>0 < b\<close> \<open>k \<le> A\<close> \<open>0 \<le> v\<close> 
    by (auto simp: mult_left_mono) (meson \<open>0 < A\<close> less_eq_real_def mult_mono zero_compare_simps(12))
  hence "?expr2 k t \<le> ?expr2 A \<epsilon>"
    by (smt \<open>k * t + v \<le> A * \<epsilon> + v\<close> ends_in_segment(2) \<open>0 \<le> t\<close> guard power_mono)
  hence "?lhs*(2*b) \<le> S*(2*b)" 
    using obs1 obs2 by simp
  thus "?lhs \<le> S"
    using \<open>0 < b\<close> by force
qed

lemma STTexample7_arith2:
  assumes "(0::real) < b" "0 \<le> v" "0 \<le> t" "k \<le> - b"
    and key: "x + v\<^sup>2 / (2 * b) \<le> S" 
    and guard: "\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> 0 \<le> k * \<tau> + v \<and> \<tau> \<le> \<epsilon>"
  shows "k * t\<^sup>2 / 2 + v * t + x + (k * t + v)\<^sup>2 / (2 * b) \<le> S" (is "?lhs \<le> S")
proof-
  have obs: "1 + k/b \<le> 0" "k * t + v \<ge> 0"
    using \<open>k \<le> - b\<close> \<open>0 < b\<close> guard \<open>0 \<le> t\<close> by (auto simp: mult_imp_div_pos_le real_add_le_0_iff)
  have "?lhs = (k * t + v + v)*t/2 * (1 + k/b) + x + v\<^sup>2 / (2 * b)"
    using \<open>0 < b\<close> by (auto simp: field_simps)
  also have "... \<le> x + v\<^sup>2 / (2 * b)"
    using obs \<open>0 \<le> t\<close> \<open>0 \<le> v\<close>
    by (smt mult_nonneg_nonneg zero_compare_simps(11) zero_compare_simps(6))
  also have "... \<le> S"
    using key .
  finally show ?thesis .
qed

(* v >= 0 & A > 0 & B >= b & b > 0 & x+v^2/(2*b) <= S & ep > 0
 -> [
      { {   ?x+v^2/(2*b) + (A/b+1)*(A/2*ep^2+ep*v) <= S; a :=*; ?-B <= a & a <= A;
         ++ ?v=0; a := 0;
         ++ a :=*; ?-B <=a & a <= -b;
        };

        c := 0;
        { x' = v, v' = a, c' = 1 & v >= 0 & c <= ep }
      }*@invariant(v >= 0 & x+v^2/(2*b) <= S)
    ] x <= S *)
lemma "A > 0 \<Longrightarrow> B \<ge> b \<Longrightarrow> b > 0 \<Longrightarrow> \<epsilon> > 0 \<Longrightarrow> (\<lambda>s::real^4. s$2 \<ge> 0 \<and> s$1 + s$2^2/(2*b) \<le> S) \<le> 
  |LOOP 
    (\<lambda>s. 
      (\<questiondown>\<lambda>s. s$1 + s$2^2/(2*b) + (A/b + 1) * (A/2 * \<epsilon>^2 + \<epsilon> * s$2) \<le> S?;(3 ::= ?);\<questiondown>\<lambda>s. -B \<le> s$3 \<and> s$3 \<le> A?) s \<union> 
      (\<questiondown>\<lambda>s. s$2 = 0?;(3 ::= (\<lambda>s. 0))) s \<union> 
      ((3 ::= ?);\<questiondown>\<lambda>s. -B \<le> s$3 \<and> s$3 \<le> - b?) s
    );(4 ::= (\<lambda>s. 0));
    (x\<acute>= (\<lambda>s. \<chi> i. if i=1 then s$2 else (if i=2 then s$3 else (if i=3 then 0 else 1))) & (\<lambda>s. s$2 \<ge> 0 \<and> s$4 \<le> \<epsilon>))
  INV (\<lambda>s. s$2 \<ge> 0 \<and> s$1 + s$2^2/(2*b) \<le> S)]
  (\<lambda>s. s$1 \<le> S)"
  apply (rule fbox_loopI) 
    apply (simp_all add: fbox_choice local_flow.fbox_g_ode_subset[OF local_flow_STTT_Ex5])
   apply(safe)
     apply (smt not_sum_power2_lt_zero zero_compare_simps(5))
    apply(rule STTexample7_arith1[of A b \<epsilon> "_$2" _ _ "_$1" S]; simp?)
  apply(force simp: field_simps, force)
  using STTexample7_arith2[of b "_$2" _ _ "_$1" S] by blast


subsubsection \<open> STTT Tutorial: Example 9a \<close>

lemma STTexample9a_arith:
  "(10*x-10*r) * v/4 + v\<^sup>2/2 + (x-r)*(2*r-2*x-3 * v)/2 + v * (2*r-2*x-3 * v)/2 \<le> (0::real)" 
  (is "?t1 + ?t2 + ?t3 + ?t4 \<le> 0")
proof-
  have "?t1 = 5 * (x-r) * v/2"
    by auto
  moreover have "?t3 = -((x - r)^2) - 3 * v * (x-r)/2"
    by (auto simp: field_simps power2_diff)
  moreover have "?t4 = - 2 * (x - r) * v/2 - 3 * v^2/2"
    by (auto simp: field_simps power2_diff)
  ultimately have "?t1 + ?t3 + ?t4 = -((x - r)^2) - 3 * v^2/2"
    by (auto simp: field_simps)
  hence "?t1 + ?t2 + ?t3 + ?t4 = -((x - r)^2) - v^2"
    by auto
  also have "... \<le> 0"
    by auto
  finally show ?thesis .
qed

(* v >= 0 & c() > 0 & Kp() = 2 & Kd() = 3 & 5/4*(x-xr())^2 + (x-xr())*v/2 + v^2/4 < c()
 -> [
      { x' = v, v' = -Kp()*(x-xr()) - Kd()*v }
    ] 5/4*(x-xr())^2 + (x-xr())*v/2 + v^2/4 < c() *)
lemma "c > 0 \<Longrightarrow> Kp = 2 \<Longrightarrow> Kd = 3 \<Longrightarrow> (\<lambda>s::real^2. (5/4)*(s$1-xr)^2 + (s$1-xr)*(s$2)/2 + (s$2)^2/4 < c) \<le> 
  |x\<acute>= (\<lambda>s. \<chi> i. if i=1 then s$2 else -Kp*(s$1-xr) - Kd*(s$2) ) & G]
  (\<lambda>s. (5/4)*(s$1-xr)^2 + (s$1-xr)*(s$2)/2 + (s$2)^2/4 < c)"
  apply(simp, rule_tac \<mu>'="\<lambda>s. 0" and \<nu>'="\<lambda>s. 10*(s$1-xr)*(s$2)/4 + (s$2^2)/2 + 
    (s$1-xr)*(-Kp*(s$1-xr)-Kd*(s$2))/2 + (s$2)*(-Kp*(s$1-xr)-Kd*(s$2))/2" in diff_inv_rules(3); 
      clarsimp simp: forall_2 STTexample9a_arith)
  apply(intro poly_derivatives; (rule poly_derivatives)?)
  by force+ (auto simp: field_simps)


subsubsection \<open> STTT Tutorial: Example 9b \<close> (*N 50 *)

 (* require differentiable \<Longrightarrow> lipschitz *)

(* v >= 0 & xm <= x & x <= S & xr = (xm + S)/2 & Kp = 2 & Kd = 3
           & 5/4*(x-xr)^2 + (x-xr)*v/2 + v^2/4 < ((S - xm)/2)^2
 -> [ { {  xm := x;
           xr := (xm + S)/2;
           ?5/4*(x-xr)^2 + (x-xr)*v/2 + v^2/4 < ((S - xm)/2)^2;
        ++ ?true;
        };
        {{ x' = v, v' = -Kp*(x-xr) - Kd*v & v >= 0 }
          @invariant(
            xm<=x,
            5/4*(x-(xm+S())/2)^2 + (x-(xm+S())/2)*v/2 + v^2/4 < ((S()-xm)/2)^2
         )
        }
      }*@invariant(v >= 0 & xm <= x & xr = (xm + S)/2 & 5/4*(x-xr)^2 + (x-xr)*v/2 + v^2/4 < ((S - xm)/2)^2)
    ] x <= S *)


subsubsection \<open> STTT Tutorial: Example 10 \<close> (*N 51 *)

(*
 v >= 0 & A > 0 & B >= b & b > 0 & ep > 0 & lw > 0 & y = ly & r != 0 & dx^2 + dy^2 = 1
           & abs(y-ly) + v^2/(2*b) < lw
 -> [
      { {   ?abs(y-ly) + v^2/(2*b) + (A/b+1)*(A/2*ep^2+ep*v) < lw;
            a :=*; ?-B <= a & a <= A;
            w :=*; r :=*; ?r != 0 & w*r = v;
         ++ ?v=0; a := 0; w := 0;
         ++ a :=*; ?-B <=a & a <= -b;
        }

        c := 0;
        {
        { x' = v*dx, y' = v*dy, v' = a, dx' = -dy*w, dy' = dx*w, w'=a/r, c' = 1 & v >= 0 & c <= ep }
        @invariant(c>=0, dx^2+dy^2=1,
          (v'=a -> v=old(v)+a*c),
          (v'=a -> -c*(v-a/2*c) <= y - old(y) & y - old(y) <= c*(v-a/2*c)),
          (v'=0 -> v=old(v)),
          (v'=0 -> -c*v <= y - old(y) & y - old(y) <= c*v)
        )
        }
      }*@invariant(v >= 0 & dx^2+dy^2 = 1 & r != 0 & abs(y-ly) + v^2/(2*b) < lw)
    ] abs(y-ly) < lw *)

subsubsection \<open> LICS: Example 1 Continuous car accelerates forward \<close>

(*
   v>=0 & a>=0
 -> [
      {x'=v, v'=a & v>=0}
    ] v>=0 *)
lemma "(\<lambda>s::real^3. s$2 \<ge> 0 \<and> s$3 \<ge> 0) \<le>
  |x\<acute>= (\<lambda>s. \<chi> i. if i=1 then s$2 else (if i=2 then s$3 else 0)) & (\<lambda>s. s$2 \<ge> 0)]
  (\<lambda>s. s$2 \<ge> 0)"
  by (simp_all add: local_flow.fbox_g_ode_subset[OF local_flow_STTT_Ex2], simp add: le_fun_def)
 

subsubsection \<open> LICS: Example 2 Single car drives forward \<close>

(* v>=0  & A>=0 & b>0
 -> [
      {
        {a:=A; ++ a:=-b;}
        {x'=v, v'=a & v>=0}
      }*@invariant(v>=0)
    ] v>=0 *)
lemma "A \<ge> 0 \<Longrightarrow> b > 0 \<Longrightarrow> (\<lambda>s::real^3. s$2 \<ge> 0) \<le>
  |LOOP
    (\<lambda>s. (3 ::= (\<lambda>s. A)) s \<union> (3 ::= (\<lambda>s. -b)) s);
    (x\<acute>= (\<lambda>s. \<chi> i. if i=1 then s$2 else (if i=2 then s$3 else 0)) & (\<lambda>s. s$2 \<ge> 0))
  INV (\<lambda>s. s$2 \<ge> 0)]
  (\<lambda>s. s$2 \<ge> 0)"
  apply (rule fbox_loopI) 
  by (simp_all add: local_flow.fbox_g_ode_subset[OF local_flow_STTT_Ex2] fbox_choice)
    (simp add: le_fun_def)

subsubsection \<open> LICS: Example 3a event-triggered car drives forward \<close>

(*
( v >= 0
	 & A >= 0
	 & b > 0 )
->
  [
    {
      {  ?(m-x>=2); a := A;
      ++ a := -b;
      };
      {x' = v, v' = a & v >= 0}
    }*@invariant(v >= 0)
  ]v >= 0 *)
lemma "A \<ge> 0 \<Longrightarrow> b > 0 \<Longrightarrow> (\<lambda>s::real^3. s$2 \<ge> 0) \<le>
  |LOOP
    (\<lambda>s. (\<questiondown>\<lambda>s. m - s$1 \<ge> 2?;(3 ::= (\<lambda>s. A))) s \<union> (3 ::= (\<lambda>s. -b)) s);
    (x\<acute>= (\<lambda>s. \<chi> i. if i=1 then s$2 else (if i=2 then s$3 else 0)) & (\<lambda>s. s$2 \<ge> 0))
  INV (\<lambda>s. s$2 \<ge> 0)]
  (\<lambda>s. s$2 \<ge> 0)"
  apply (rule fbox_loopI) 
  by (simp_all add: local_flow.fbox_g_ode_subset[OF local_flow_STTT_Ex2] fbox_choice)
    (simp add: le_fun_def)


subsubsection \<open> LICS: Example 4a safe stopping of time-triggered car \<close>

lemma LICSexample4a_arith:
  assumes "(0::real) \<le> A" "0 < b" "v\<^sup>2 \<le> 2 * b * (m - x)" "0 \<le> t"
      and guard: "\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> 0 \<le> A * \<tau> + v \<and> \<tau> \<le> \<epsilon>"
      and key: "v\<^sup>2 + (A * (A * \<epsilon>\<^sup>2 + 2 * \<epsilon> * v) + b * (A * \<epsilon>\<^sup>2 + 2 * \<epsilon> * v)) \<le> 2 * b * (m - x)" (is "?expr1 \<le> _")
    shows "(A * t + v)\<^sup>2 \<le> 2 * b * (m - (A * t\<^sup>2 / 2 + v * t + x))"
proof-
  have "t \<le> \<epsilon>" "0 \<le> v"
    using guard \<open>0 \<le> t\<close> by (force, erule_tac x=0 in allE, auto)
  hence "A * t\<^sup>2 + 2 * t * v \<le> A * \<epsilon>\<^sup>2 + 2 * \<epsilon> * v"
    using \<open>0 \<le> A\<close> \<open>0 \<le> t\<close>
    by (smt mult_less_cancel_left_disj mult_right_mono power_less_imp_less_base) 
  hence "v\<^sup>2 + (A + b) * (A * t\<^sup>2 + 2 * t * v) \<le> v\<^sup>2 + (A + b) * (A * \<epsilon>\<^sup>2 + 2 * \<epsilon> * v)"
    using \<open>0 \<le> A\<close> \<open>0 < b\<close> by (smt mult_left_mono) 
  also have "... = ?expr1"
    by (auto simp: field_simps)
  finally have "v\<^sup>2 + (A + b) * (A * t\<^sup>2 + 2 * t * v) \<le> 2 * b * (m - x)"
    using key by auto
  thus ?thesis
    by (auto simp: field_simps)
qed

(*v^2<=2*b*(m-x) & v>=0  & A>=0 & b>0
 -> [
      {
        {?(2*b*(m-x) >= v^2+(A+b)*(A*ep^2+2*ep*v)); a:=A; ++ a:=-b; }
        t := 0;
        {x'=v, v'=a, t'=1 & v>=0 & t<=ep}
      }*@invariant(v^2<=2*b*(m-x))
    ] x <= m *)
lemma "A \<ge> 0 \<Longrightarrow> b > 0 \<Longrightarrow> (\<lambda>s::real^4. s$2^2 \<le> 2*b*(m-s$1) \<and> s$2 \<ge> 0) \<le>
  |LOOP
    (\<lambda>s. (\<questiondown>\<lambda>s. 2*b*(m-s$1) \<ge> s$2^2+(A+b)*(A*\<epsilon>\<^sup>2+2*\<epsilon>*(s$2))?;(3 ::= (\<lambda>s. A))) s \<union> (3 ::= (\<lambda>s. -b)) s);
    (4 ::= (\<lambda>s. 0));
    (x\<acute>= (\<lambda>s. \<chi> i. if i=1 then s$2 else (if i=2 then s$3 else (if i=3 then 0 else 1))) & (\<lambda>s. s$2 \<ge> 0 \<and> s$4 \<le> \<epsilon>))
  INV (\<lambda>s. s$2^2 \<le> 2*b*(m-s$1))]
  (\<lambda>s. s$1 \<le> m)"
  apply (rule fbox_loopI) 
    apply (simp_all add: fbox_choice local_flow.fbox_g_ode_subset[OF local_flow_STTT_Ex5])
   apply(safe, smt not_sum_power2_lt_zero zero_compare_simps(10))
  apply(rule LICSexample4a_arith[of A b "_$2" m "_$1" _ \<epsilon>]; simp?)
   apply(force simp: field_simps)
  apply bin_unfold
  apply distribute
  apply (mon_simp_vars b m)
  done

subsubsection \<open> LICS: Example 4b progress of time-triggered car \<close>  (*N 56 *)

(* ep() > 0 & A() > 0 & b() > 0
->
  \forall p \exists m
  <
    {
        {?(2*b()*(m-x) >= v^2+(A()+b())*(A()*ep()^2+2*ep()*v)); a:=A(); ++ a:=-b(); }
        t := 0;
        {x'=v, v'=a, t'=1 & v>=0 & t<=ep()}
    }*
  > (x >= p) *)


subsubsection \<open> LICS: Example 4c relative safety of time-triggered car \<close>

lemma in_fbox_loopI: 
  "I s \<Longrightarrow> I \<le> Q \<Longrightarrow> I \<le> |R] I \<Longrightarrow> ( |LOOP R INV I] Q) s"
  using fbox_loopI[of I I Q R] by auto

abbreviation LICS_Ex4c_f :: "real \<Rightarrow> real \<Rightarrow> real^4 \<Rightarrow> real^4" ("f")
  where "f time acc s \<equiv> (\<chi> i. if i=1 then s$2 else (if i=2 then acc else if i=3 then 0 else time))"

lemma local_flow_LICS_Ex4c_1:
  "local_flow (f k a) UNIV UNIV
  (\<lambda>t s. \<chi> i. if i=1 then a * t^2/2 + s$2 * t + s$1 else 
             (if i=2 then a * t + s$2               else 
             (if i=3 then s$3                       else 
                          k * t + s$4               )))"
  apply(unfold_locales, simp_all add: local_lipschitz_def forall_2 lipschitz_on_def)
    apply(clarsimp, rule_tac x=1 in exI)+
  apply(clarsimp simp: dist_norm norm_vec_def L2_set_def)
  unfolding UNIV_4 by (auto intro!: poly_derivatives simp: forall_4 vec_eq_iff)

lemma local_flow_LICS_Ex4c_2:
  "local_flow (\<lambda>s. f k (s$3) s) UNIV UNIV
  (\<lambda>t s. \<chi> i. if i=1 then s$3 * t^2/2 + s$2 * t + s$1 else 
             (if i=2 then s$3 * t + s$2               else 
             (if i=3 then s$3                       else 
                          k * t + s$4               )))"
  apply(unfold_locales, simp_all add: local_lipschitz_def forall_2 lipschitz_on_def)
    apply(clarsimp, rule_tac x=1 in exI)+
  apply(clarsimp simp: dist_norm norm_vec_def L2_set_def)
  unfolding UNIV_4 by (auto intro!: poly_derivatives simp: forall_4 vec_eq_iff)

lemma LICSexample4c_arith1:
  assumes "v\<^sup>2 \<le> 2 * b * (m - x)" "0 \<le> t" "A \<ge> 0" "b > 0"
    and key: "v\<^sup>2 + (A * (A * \<epsilon>\<^sup>2 + 2 * \<epsilon> * v) + b * (A * \<epsilon>\<^sup>2 + 2 * \<epsilon> * v)) \<le> 2 * b * (m - x)"
    and guard: "\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> (0::real) \<le> A * \<tau> + v \<and> \<tau> \<le> \<epsilon>"
  shows "(A * t + v)\<^sup>2 \<le> 2 * b * (m - (A * t\<^sup>2 / 2 + v * t + x))" (is "_ \<le> ?rhs")
proof-
  have "t \<le> \<epsilon>" "0 \<le> \<epsilon>" "0 \<le> v"
    using guard \<open>0 \<le> t\<close> by (force, erule_tac x=0 in allE, simp, erule_tac x=0 in allE, simp)
  hence obs1: "A * t\<^sup>2 + 2 * t * v \<le> A * \<epsilon>\<^sup>2 + 2 * \<epsilon> * v"
    using \<open>A \<ge> 0\<close> \<open>0 \<le> t\<close> \<open>t \<le> \<epsilon>\<close> by (smt mult_mono power_mono zero_compare_simps(12)) 
  have obs2:"?rhs + A * b * t^2 + 2 * b * v * t = 2 * b * (m - x)"
    by (simp add: field_simps)
  have "(A * t + v)\<^sup>2 + A * b * t^2 + 2 * b * v * t = v\<^sup>2 + (A * (A * t\<^sup>2 + 2 * t * v) + b * (A * t\<^sup>2 + 2 * t * v))"
    by (simp add: field_simps)
  also have "... \<le> v\<^sup>2 + (A * (A * \<epsilon>\<^sup>2 + 2 * \<epsilon> * v) + b * (A * \<epsilon>\<^sup>2 + 2 * \<epsilon> * v))"
    using obs1 \<open>A \<ge> 0\<close> \<open>b > 0\<close> by (smt mult_less_cancel_left) 
  also have "... \<le> 2 * b * (m - x)"
    using key .
  finally show ?thesis
    using obs2 by auto
qed

(* ( [{x' = v, v' = -b()}]x<=m()
   & v >= 0
	 & A() >= 0
	 & b() > 0 )
->
  [
    {
      {  ?(2*b()*(m()-x) >= v^2 + (A() + b())*(A()*ep()^2 + 2*ep()*v)); a := A();
      ++ a := -b();
      };
      t := 0;
      {x' = v, v' = a, t' = 1 & v >= 0 & t <= ep()}
    }*@invariant(v^2<=2*b()*(m()-x))
  ]x<=m() *)

lemma 
  assumes "A \<ge> 0" "b > 0" "s$2 \<ge> 0"
  shows "( |x\<acute>=(f 0 (-b)) & (\<lambda>s. True)] (\<lambda>s. s$1 \<le> m)) s \<Longrightarrow> 
  ( |LOOP
    (\<lambda>s. (\<questiondown>\<lambda>s. 2*b*(m-s$1) \<ge> s$2^2+(A+b)*(A*\<epsilon>^2+2*\<epsilon>*(s$2))?;(3 ::= (\<lambda>s. A))) s \<union> (3 ::= (\<lambda>s. -b)) s);
    (4 ::= (\<lambda>s. 0));
    (x\<acute>= (\<lambda>s. f 1 (s$3) s) & (\<lambda>s. s$2 \<ge> 0 \<and> s$4 \<le> \<epsilon>))
  INV (\<lambda>s. s$2^2 \<le> 2*b*(m-s$1))] (\<lambda>s. s$1 \<le> m)) s"
  apply(subst (asm) local_flow.fbox_g_ode_subset[OF local_flow_LICS_Ex4c_1], simp_all)
  apply(rule in_fbox_loopI)
     apply(erule_tac x="s$2/b" in allE)
  using \<open>b > 0\<close> \<open>s$2 \<ge> 0\<close> apply(simp add: field_simps)
   apply (simp add: le_fun_def, smt \<open>b > 0\<close> mult_sign_intros(6) sum_power2_ge_zero)
  apply(simp add: fbox_choice)
  apply(simp_all add: local_flow.fbox_g_ode_subset[OF local_flow_LICS_Ex4c_2], safe)
  apply(rule LICSexample4c_arith1[OF _ _ \<open>0 \<le> A\<close> \<open>0 < b\<close>, of "_$2" m "_$1" _ \<epsilon>]; simp?)
  by (auto simp: field_simps)

no_notation LICS_Ex4c_f ("f")


subsubsection \<open> LICS: Example 5 Controllability Equivalence \<close>

lemma LICSexample5_arith1:
  assumes "(0::real) < b" "0 \<le> t"
    and key: "v\<^sup>2 \<le> 2 * b * (m - x)"
  shows "v * t - b * t\<^sup>2 / 2 + x \<le> m"
proof-
  have "v\<^sup>2 \<le> 2 * b * (m - x) + (b * t - v)^2"
    using key by (simp add: add_increasing2) 
  hence "b^2 * t^2 - 2 * b * v * t \<ge> 2 * b * x - 2 * b * m"
    by (auto simp: field_simps power2_diff)
  hence "(b^2/b) * t^2 - 2 * (b/b) * v * t \<ge> 2 * (b/b) * x - 2 * (b/b) * m"
    using \<open>b > 0\<close> apply (auto simp: field_simps)
    apply (clarsimp simp: power2_eq_square[symmetric])
    apply (subst (asm) algebra_simps(18)[symmetric])+
    using mult_left_le_imp_le[of b "x * 2 + t * (v * 2)" "b * t^2 + m * 2"]
    by blast
  thus ?thesis
    using \<open>b > 0\<close>
    by (simp add: field_simps)
qed

lemma LICSexample5_arith2:
  assumes "(0::real) < b" "0 \<le> v" "\<forall>t\<in>{0..}. v * t - b * t\<^sup>2 / 2 + x \<le> m"
  shows "v\<^sup>2 \<le> 2 * b * (m - x)"
proof(cases "v = 0")
  case True
  have "m - x \<ge> 0"
    using assms by (erule_tac x=0 in ballE, auto)
  thus ?thesis 
    using assms True by auto
next
  case False
  hence obs: "v > 0 \<and> (\<exists>k. k > 0 \<and> v = b * k)"
    using assms(1,2)
    by (metis (no_types, opaque_lifting) approximation_preproc_push_neg(1) 
        dual_order.order_iff_strict mult_less_cancel_right nonzero_mult_div_cancel_left 
        times_divide_eq_right vector_space_over_itself.scale_zero_left)
  {fix t::real assume "t \<ge> 0"
    hence "v * t - b * t\<^sup>2 / 2 + x \<le> m"
      using assms by auto
    hence "2 * b * v * t - b * b * t\<^sup>2 + 2 * b * x \<le> 2 * b * m"
      using \<open>b > 0\<close> by (simp add: field_simps) (metis distrib_left mult_le_cancel_left_pos) 
    hence "- b\<^sup>2 * t\<^sup>2 + 2 * b * v * t \<le> 2 * b * m - 2 * b * x"
      using \<open>b > 0\<close> by (simp add: power2_eq_square) 
    hence "v^2 \<le> 2 * b * (m - x) + (b^2 * t^2 + v^2 - 2 * b * v * t)"
      by (simp add: field_simps)
    also have "... = 2 * b * (m - x) + (b * t - v)^2"
      by (simp add: power2_diff power_mult_distrib)
    finally have "v^2 \<le> 2 * b * (m - x) + (b * t - v)^2" .}
  hence "\<forall>t\<ge>0. v\<^sup>2 \<le> 2 * b * (m - x) + (b * t - v)\<^sup>2"
    by blast
  then obtain k where "v\<^sup>2 \<le> 2 * b * (m - x) + (b * k - v)\<^sup>2 \<and> k > 0 \<and> v = b * k"
    using obs by fastforce
  then show ?thesis 
    by auto
qed

(* v>=0 & b>0 -> ( v^2<=2*b*(m-x) <-> [{x'=v, v'=-b}]x<=m ) *)
lemma "b > 0 \<Longrightarrow> (s::real^2)$2 \<ge> 0 \<Longrightarrow> 
   s$2^2 \<le> 2*b*(m-s$1) \<longleftrightarrow> ( |x\<acute>= (\<lambda>s. \<chi> i. if i=1 then s$2 else -b) & (\<lambda>s. True)] (\<lambda>s. s$1 \<le> m)) s"
  apply(subst local_flow.fbox_g_ode_subset[where T="UNIV" 
        and \<phi>="\<lambda>t s. \<chi> i::2. if i=1 then -b * t^2/2 + s$2 * t + s$1 else -b * t + s$2"])
      apply(unfold_locales, simp_all add: local_lipschitz_def forall_2 lipschitz_on_def)
     apply(clarsimp simp: dist_norm norm_vec_def L2_set_def, rule_tac x=1 in exI)+
  unfolding UNIV_2 apply clarsimp
  apply(force intro!: poly_derivatives)
  using exhaust_2 apply(force simp: vec_eq_iff)
  by (auto simp: LICSexample5_arith1 LICSexample5_arith2)


subsubsection \<open> LICS: Example 6 MPC Acceleration Equivalence \<close>  (*N 59 *)

lemma LICSexample6_arith1:
  assumes "0 \<le> v" "0 < b" "0 \<le> A" "0 \<le> \<epsilon>" and guard: "\<forall>t\<in>{0..}. (\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> \<tau> \<le> \<epsilon>) \<longrightarrow> (\<forall>\<tau>\<in>{0..}. 
  A * t * \<tau> + v * \<tau> - b * \<tau>\<^sup>2 / 2 + (A * t\<^sup>2 / 2 + v * t + x) \<le> (m::real))"
  shows "v\<^sup>2 + (A * (A * \<epsilon>\<^sup>2 + 2 * \<epsilon> * v) + b * (A * \<epsilon>\<^sup>2 + 2 * \<epsilon> * v)) \<le> 2 * b * (m - x)"
proof-
  {fix \<tau>::real
    assume "\<tau> \<ge> 0"
    hence "A * \<epsilon> * \<tau> + v * \<tau> - b * \<tau>\<^sup>2 / 2 + (A * \<epsilon>\<^sup>2 / 2 + v * \<epsilon> + x) \<le> m"
      using guard \<open>0 \<le> \<epsilon>\<close> apply(erule_tac x=\<epsilon> in ballE)
      by (erule impE, auto simp: closed_segment_eq_real_ivl)
    hence "2 * (A * \<epsilon> * \<tau> + v * \<tau> - b * \<tau>\<^sup>2 / 2 + (A * \<epsilon>\<^sup>2 / 2 + v * \<epsilon> + x)) * b \<le> 2 * m * b"
      using \<open>0 < b\<close> by (meson less_eq_real_def mult_left_mono mult_right_mono rel_simps(51)) 
    hence "2 * A * \<epsilon> * \<tau> * b + 2 * v * \<tau> * b - b^2 * \<tau>\<^sup>2 + b * (A * \<epsilon>\<^sup>2 + 2 * v * \<epsilon>) \<le> 2 * b * (m - x)"
      using \<open>0 < b\<close> apply(simp add: algebra_simps(17,18,19,20) add.assoc[symmetric] 
         power2_eq_square[symmetric] mult.assoc[symmetric])
      by (simp add: mult.commute mult.left_commute power2_eq_square)}
  hence "\<forall>\<tau>\<ge>0. 2 * A * \<epsilon> * \<tau> * b + 2 * v * \<tau> * b - b^2 * \<tau>\<^sup>2 + b * (A * \<epsilon>\<^sup>2 + 2 * v * \<epsilon>) \<le> 2 * b * (m - x)"
    by blast
  moreover have "2 * A * \<epsilon> * ((A*\<epsilon> + v)/b) * b + 2 * v * ((A*\<epsilon> + v)/b) * b - b^2 * ((A*\<epsilon> + v)/b)\<^sup>2 =
    2 * A * \<epsilon> * (A*\<epsilon> + v) + 2 * v * (A*\<epsilon> + v) - (A*\<epsilon> + v)\<^sup>2"
    using \<open>0 < b\<close> by (simp add: field_simps)
  moreover have "... = v\<^sup>2 + A * (A * \<epsilon>\<^sup>2 + 2 * \<epsilon> * v)"
    using \<open>0 < b\<close> by (simp add: field_simps)
  moreover have "(A*\<epsilon> + v)/b \<ge> 0"
    using assms by auto
  ultimately have "v\<^sup>2 + A * (A * \<epsilon>\<^sup>2 + 2 * \<epsilon> * v) + b * (A * \<epsilon>\<^sup>2 + 2 * v * \<epsilon>) \<le> 2 * b * (m - x)"
    using assms by (erule_tac x="(A*\<epsilon> + v)/b" in allE, auto)
  thus ?thesis
    by argo
qed


lemma LICSexample6_arith2:
  assumes "0 \<le> v" "0 < b" "0 \<le> A" "0 \<le> t" "0 \<le> \<tau>" "t \<le> \<epsilon>"
    and "v\<^sup>2 + (A * (A * \<epsilon>\<^sup>2 + 2 * \<epsilon> * v) + b * (A * \<epsilon>\<^sup>2 + 2 * \<epsilon> * v)) \<le> 2 * b * (m - x)"
  shows "A * \<epsilon> * \<tau> + s $ 2 * \<tau> - b * \<tau>\<^sup>2 / 2 + (A * \<epsilon>\<^sup>2 / 2 + s $ 2 * \<epsilon> + s $ 1) \<le> m"
  (* Need to show that function (\<lambda>\<tau>. A * \<epsilon> * \<tau> + s $ 2 * \<tau> - b * \<tau>\<^sup>2 / 2) attains maximum at \<tau> = (A*\<epsilon> + v)/b *)
  oops

lemma local_flow_LICS_Ex6:
  "local_flow (\<lambda>s::real^3. \<chi> i. if i=1 then s$2 else (if i=2 then k1 else k2)) UNIV UNIV
  (\<lambda>t s. \<chi> i. if i = 1 then k1 * t^2/2 + s$2 * t + s$1 else (if i=2 then k1 * t + s$2 else k2 * t + s$3))"
  apply(unfold_locales, simp_all add: local_lipschitz_def forall_2 lipschitz_on_def)
    apply(clarsimp, rule_tac x=1 in exI)+
  apply(clarsimp simp: dist_norm norm_vec_def L2_set_def)
  unfolding UNIV_3 by (auto intro!: poly_derivatives simp: forall_3 vec_eq_iff)

(* v>=0 & b>0 & A>=0 & ep>=0 -> (
    [t:=0; {x'=v, v'=A, t'=1 & t<=ep}][{x'=v, v'=-b}]x<=m
    <->
    2*b*(m-x) >= v^2 + (A + b)*(A*ep^2 + 2*ep*v)
   ) *)
lemma "s$2 \<ge> 0 \<Longrightarrow> b>0 \<Longrightarrow> A \<ge> 0 \<Longrightarrow> \<epsilon> \<ge> 0 \<Longrightarrow>  
  ( |(3 ::= (\<lambda>s. 0));
    (x\<acute>= (\<lambda>s::real^3. \<chi> i. if i=1 then s$2 else (if i=2 then A else 1)) & (\<lambda>s. s$3 \<le> \<epsilon>))]
  |x\<acute>= (\<lambda>s. \<chi> i. if i=1 then s$2 else (if i=2 then -b else 0)) & (\<lambda>s. True)] (\<lambda>s. s$1 \<le> m)) s
\<longleftrightarrow>
  2*b*(m-s$1) \<ge> s$2^2+(A+b)*(A*\<epsilon>^2+2*\<epsilon>*(s$2))"
  apply (simp add: le_fbox_choice_iff local_flow.fbox_g_ode_subset[OF local_flow_LICS_Ex6], safe)
  apply(subst Groups.algebra_simps(17))
   apply(rule LICSexample6_arith1[of "_$2" b A \<epsilon> "_$1" m]; simp?)
   apply(force simp: field_simps)
  apply(erule_tac x=t in allE; clarsimp)
  apply(rename_tac t \<tau>)
  apply(rule_tac b="A * \<epsilon> * \<tau> + s $ 2 * \<tau> - b * \<tau>\<^sup>2 / 2 + (A * \<epsilon>\<^sup>2 / 2 + s $ 2 * \<epsilon> + s $ 1)" in order.trans)
   apply(simp add: algebra_simps)
  (* using LICSexample6_arith2 *)
  oops


subsubsection \<open> LICS: Example 7 Model-Predictive Control Design Car \<close>  (*N 60 *)

notation LICS_Ex4c_f ("f")

(* [{x'=v, v'=-b}](x<=m)
   & v >= 0
   & A >= 0
   & b > 0
->
  [
    {
    {{?([t:=0; {x'=v, v'=A, t'=1 & v >= 0 & t<=ep}] [{x'=v, v'=-b}](x<=m));
       a := A;}
    ++ a := -b;}
      t := 0;
      {x'=v, v'=a, t'=1 & v>=0 & t<=ep}
    }*@invariant([{x'=v, v'=-b}](x<=m))
  ] (x <= m) *)

lemma "( |x\<acute>=(f 0 (-b)) & (\<lambda>s. True)] (\<lambda>s. s$1 \<le> m)) s \<Longrightarrow> s$2 \<ge> 0 \<Longrightarrow> A \<ge> 0 \<Longrightarrow> b > 0 \<Longrightarrow> 
  ( |LOOP (
  (\<lambda>s. (\<questiondown>|(3 ::= (\<lambda>s. 0));(x\<acute>= (f 1 A) & (\<lambda>s. s$2 \<ge> 0 \<and> s$4 \<le> \<epsilon>))] |x\<acute>= (f 0 (-b)) & (\<lambda>s. True)] (\<lambda>s. s$1 \<le> m)?;
  (3 ::= (\<lambda>s. A))) s \<union> 
  (3 ::= (\<lambda>s. -b)) s); 
  (4 ::= (\<lambda>s. 0)); 
  (x\<acute>= (\<lambda>s. f 1 (s$3) s) & (\<lambda>s. s$2 \<ge> 0 \<and> s$4 \<le> \<epsilon>))
  ) INV (\<lambda>s. ( |x\<acute>=(f 1 (-b)) & (\<lambda>s. True)] (\<lambda>s. s$1 \<le> m)) s)] (\<lambda>s. s$1 \<le> m)) s"
  apply(rule in_fbox_loopI, simp_all add: local_flow.fbox_g_ode_subset[OF local_flow_LICS_Ex4c_1]
      local_flow.fbox_g_ode_subset[OF local_flow_LICS_Ex4c_2] le_fbox_choice_iff, safe)
      apply(erule_tac x=0 in allE, erule_tac x=0 in allE, simp)
  oops


no_notation LICS_Ex4c_f ("f")


subsection \<open>Advanced\<close>


subsubsection \<open> ETCS: Essentials \<close>

locale ETCS =
  fixes \<epsilon> b A m::real
(* Real ep; /* Control cycle duration upper bound */
   Real b;  /* Braking force */
   Real A;  /* Maximum acceleration */
   Real m;  /* End of movement authority (train must not drive past m) *)
begin

(* Real stopDist(Real v) = v^2/(2*b) *)
abbreviation "stopDist v \<equiv> v^2/(2*b)"

(* Real accCompensation(Real v) = (((A/b) + 1)*((A/2)*ep^2 + ep*v)) *)
abbreviation "accCompensation v \<equiv> ((A/b) + 1) * ((A/2)*\<epsilon>^2 + \<epsilon> * v)"

(* Real SB(Real v) = stopDist(v) + accCompensation(v) *)
abbreviation "SB v \<equiv> stopDist v + accCompensation v"

(* initial(Real m, Real z, Real v) <-> (v >= 0 & m-z >= stopDist(v) & b>0 & A>=0 & ep>=0) *)
abbreviation "initial m' z v \<equiv> (v \<ge> 0 \<and> (m' - z) \<ge> stopDist v)" (* Initial states *)

(* Bool safe(Real m, Real z, Real v, Real d) <-> (z >= m -> v <= d) *)
abbreviation "safe m' z v \<delta> \<equiv> z \<ge> m' \<longrightarrow> v \<le> \<delta>" 

(* Bool loopInv(Real m, Real z, Real v) <-> (v >= 0 & m-z >= stopDist(v) *)
abbreviation "loopInv m' z v \<equiv> v \<ge> 0 \<and> m' - z \<ge> stopDist v" (* always maintain sufficient stopping distance *)

(*HP ctrl ::= {?m - z <= SB(v); a := -b; ++ ?m - z >= SB(v); a :=  A; *)
abbreviation "ctrl s \<equiv> (\<questiondown>\<lambda>s::real^4. m - s$1 \<le> SB (s$2)?;(3 ::= (\<lambda>s. -b))) s \<union> 
 (\<questiondown>\<lambda>s. m - s$1 \<ge> SB (s$2)?;(3 ::= (\<lambda>s. A))) s" (* train controller *)

(* HP drive ::= {t := 0;{z'=v, v'=a, t'=1  & v >= 0 & t <= ep} *)
abbreviation "drive \<equiv> (4 ::= (\<lambda>s. 0));
  (x\<acute>= (\<lambda>s::real^4. \<chi> i. if i=1 then s$2 else (if i=2 then s$3 else (if i=3 then 0 else 1))) 
  & (\<lambda>s. s$2 \<ge> 0 \<and> s$4 \<le> \<epsilon>))"

lemma ETCS_arith1: 
  assumes "0 < b" "0 \<le> A" "0 \<le> v" "0 \<le> t"
    and "v\<^sup>2 / (2 * b) + (A * (A * \<epsilon>\<^sup>2 / 2 + \<epsilon> * v)/ b + (A * \<epsilon>\<^sup>2 / 2 + \<epsilon> * v)) \<le> m - x" (is "?expr1 \<le> m - x")
    and guard: "\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> \<tau> \<le> \<epsilon>"
  shows "(A * t + v)\<^sup>2/(2 * b) \<le> m - (A * t\<^sup>2/2 + v * t + x)" (is "?lhs \<le> ?rhs")
proof-
  have "2*b*(v\<^sup>2/(2*b) + (A*(A*\<epsilon>\<^sup>2/2+\<epsilon>* v)/b + (A*\<epsilon>\<^sup>2/2+\<epsilon>* v))) \<le> 2*b*(m-x)" (is "?expr2 \<le> 2*b*(m-x)")
    using \<open>0 < b\<close> mult_left_mono[OF \<open>?expr1 \<le> m - x\<close>, of "2 * b"] by auto
  also have "?expr2 = v\<^sup>2 +  2 * A * (A * \<epsilon>\<^sup>2 / 2 + \<epsilon> * v) + b * A * \<epsilon>\<^sup>2 + 2 * b * \<epsilon> * v"
    using \<open>0 < b\<close> by (auto simp: field_simps)
  also have "... = v\<^sup>2 +  A^2 * \<epsilon>\<^sup>2 + 2 * A * \<epsilon> * v + b * A * \<epsilon>\<^sup>2 + 2 * b * \<epsilon> * v"
    by (auto simp: field_simps)
  finally have obs: "v\<^sup>2 +  A\<^sup>2*\<epsilon>\<^sup>2 + 2*A*\<epsilon>* v + b*A*\<epsilon>\<^sup>2 + 2*b*\<epsilon>* v \<le> 2*b*(m-x)" (is "?expr3 \<epsilon> \<le> 2*b*(m-x)") .
  have "t \<le> \<epsilon>"
    using guard \<open>0 \<le> t\<close> by auto
  hence "v\<^sup>2 + A\<^sup>2 * t\<^sup>2 + b * A * t\<^sup>2 \<le> v\<^sup>2 + A\<^sup>2 * \<epsilon>\<^sup>2 + b * A * \<epsilon>\<^sup>2"
    using power_mono[OF \<open>t \<le> \<epsilon>\<close> \<open>0 \<le> t\<close>, of 2]
    by (smt assms(1,2) mult_less_cancel_left zero_compare_simps(4) zero_le_power) 
  hence "v\<^sup>2 + A\<^sup>2 * t\<^sup>2 + 2 * A * t * v + b * A * t\<^sup>2 \<le> v\<^sup>2 + A\<^sup>2 * \<epsilon>\<^sup>2 + 2 * A * \<epsilon> * v + b * A * \<epsilon>\<^sup>2"
    using assms(1,2,3,4) \<open>t \<le> \<epsilon>\<close> by (smt mult_left_mono mult_right_mono) 
  hence "?expr3 t \<le> 2 * b * (m - x)"
    using assms(1,2,3,4) \<open>t \<le> \<epsilon>\<close> obs
    by (smt (z3) mult_less_cancel_left mult_minus_right mult_right_mono_neg) 
  hence "A\<^sup>2 * t\<^sup>2 + v\<^sup>2 + 2 * A * t * v \<le> 2 * b * m - b * A * t\<^sup>2 - 2 * b * t * v - 2 * b * x"
    by (simp add: right_diff_distrib)
  hence "(A * t + v)\<^sup>2 \<le> 2 * b * m - b * A * t\<^sup>2 - 2 * b * t * v - 2 * b * x"
    unfolding cross3_simps(29)[of A t 2] power2_sum[of "A*t" v] by (simp add: mult.assoc)
  hence "?lhs \<le> (2 * b * m - b * A * t\<^sup>2 - 2 * b * t * v - 2 * b * x)/(2 * b)" (is "_ \<le> ?expr4")
    using \<open>0 < b\<close> divide_right_mono by fastforce
  also have "?expr4 = ?rhs"
    using \<open>0 < b\<close> by (auto simp: field_simps)
  finally show "?lhs \<le> ?rhs" .
qed

(* Safety specification of the form: initial -> [{ctrl;plant}*]safe *)
lemma "b > 0 \<Longrightarrow> A \<ge> 0 \<Longrightarrow> \<epsilon> \<ge> 0 \<Longrightarrow> 
  (\<lambda>s. initial m (s$1) (s$2)) \<le> |LOOP ctrl;drive INV (\<lambda>s. loopInv m (s$1) (s$2))] (\<lambda>s. s$1 \<le> m)"
  apply (rule fbox_loopI)
    apply (simp_all add: le_fbox_choice_iff local_flow.fbox_g_ode_subset[OF local_flow_STTT_Ex5], safe)
    apply (smt divide_le_cancel divide_minus_left not_sum_power2_lt_zero)
   apply(auto simp: field_simps)[1]
  by (rule ETCS_arith1[of "_$2" _ "_$1"], auto simp: field_simps)

subsection \<open> ETCS: Proposition 1 (Controllability) \<close> (*N 62 *)

(* Bool Assumptions(Real v, Real d) <-> ( v>=0 & d>=0 & b>0 ) *)
abbreviation "assumptions v \<delta> \<equiv> (v \<ge> 0 \<and> \<delta> \<ge> 0 \<and> b > 0)" 

lemma ETCS_Prop1_arith1:
  assumes "0 \<le> v" "0 \<le> \<delta>" "0 < b" "x \<le> m"
    and "\<forall>t\<in>{0..}. (\<forall>\<tau>\<in>{0--t}. b * \<tau> \<le> v) \<longrightarrow>
       m \<le> v * t - b * t\<^sup>2 / 2 + x \<longrightarrow> v - b * t \<le> \<delta>"
  shows "v\<^sup>2 - \<delta>\<^sup>2 \<le> 2 * b * (m - x)"
    (* solve arithmetic *)
  sorry

lemma ETCS_Prop1_arith2:
  assumes "0 \<le> v" "0 \<le> \<delta>" "0 < b" "x \<le> m" "0 \<le> t"
      and key: "v\<^sup>2 - \<delta>\<^sup>2 \<le> 2 * b * (m - x)" "m \<le> v * t - b * t\<^sup>2 / 2 + x"
      and guard: "\<forall>\<tau>\<in>{0--t}. b * \<tau> \<le> v"
    shows "v - b * t \<le> \<delta>"
proof-
  have "2 * b * (m - x) \<le> 2 * b * (v * t - b * t\<^sup>2 / 2) - v\<^sup>2 + v\<^sup>2"
    using key(2) \<open>0 < b\<close> by simp
  also have "... = v\<^sup>2 - (v - b * t)\<^sup>2"
    using \<open>0 < b\<close> by (simp add: power2_diff field_simps)
  finally have "(v - b * t)\<^sup>2 \<le> \<delta>\<^sup>2"
    using key(1) by simp
  thus "v - b * t \<le> \<delta>"
    using guard \<open>0 \<le> t\<close> \<open>0 \<le> \<delta>\<close> by auto
qed

(* Assumptions(v, d) & z<=m
  ->
  ( [ {z'=v, v'=-b & v>=0 } ](z>=m -> v<=d)
    <->
    v^2-d^2 <= 2*b*(m-z)
  ) *)
lemma "assumptions (s$2) \<delta> \<and> (s$1) \<le> m \<Longrightarrow> 
  ( |x\<acute>= (\<lambda>t s::real^2. \<chi> i. if i=1 then (s$2) else -b) & (\<lambda>s. s$2 \<ge> 0) on (\<lambda>s. {0..}) UNIV @ 0]
  (\<lambda>s. s$1 \<ge> m \<longrightarrow> s$2 \<le> \<delta>)) s \<longleftrightarrow> s$2^2 - \<delta>^2 \<le> 2*b*(m-s$1)"
  apply(subst local_flow.fbox_g_ode_subset[where T="UNIV" 
        and \<phi>="\<lambda>t s. \<chi> i::2. if i=1 then -b * t^2/2 + s$2 * t + s$1 else -b * t + s$2"])
      apply(unfold_locales, simp_all add: local_lipschitz_def forall_2 lipschitz_on_def)
     apply(clarsimp simp: dist_norm norm_vec_def L2_set_def, rule_tac x=1 in exI)+
  unfolding UNIV_2 using exhaust_2 
  by (auto intro!: poly_derivatives simp: vec_eq_iff 
      ETCS_Prop1_arith1 closed_segment_eq_real_ivl ETCS_Prop1_arith2)


subsection \<open> ETCS: Proposition 4 (Reactivity) \<close> (*N 63 *)

(* Bool Assumptions(Real v, Real d) <-> ( v>=0 & d>=0 & b>0 ) *)
term "assumptions v \<delta>"

(* Bool Controllable(Real m, Real z, Real v, Real d) <-> (v^2-d^2 <= 2*b*(m-z) & Assumptions(v, d)) *)
abbreviation "controllable m' z v \<delta> \<equiv> v^2 - \<delta>^2 \<le> 2 * b * (m' - z) \<and> assumptions v \<delta>"

(* HP drive ::= {t := 0;{z'=v, v'=a, t'=1  & v >= 0 & t <= ep}} *)
term "drive"

(* em = 0 & d >= 0 & b > 0 & ep > 0 & A > 0 & v>=0
  -> ((\<forall> m \<forall> z (m-z>= sb & Controllable(m,z,v,d) -> [ a:=A; drive; ]Controllable(m,z,v,d)) )
      <->
      sb >= (v^2 - d^2) /(2*b) + (A/b + 1) * (A/2 * ep^2 + ep*v)) *)
lemma "\<delta> \<ge> 0 \<and> b > 0 \<and> \<epsilon> > 0 \<and> A > 0 \<and> s$2 \<ge> 0 \<Longrightarrow> 
 (\<forall>m. \<forall>z. m - s$1 \<ge> sb \<and> controllable m (s$1) (s$2) \<delta> \<longrightarrow> ( |(3 ::= (\<lambda>s. A));drive] (\<lambda>s. controllable m (s$1) (s$2) \<delta>)) s)
  \<longleftrightarrow> sb \<ge> (s$2\<^sup>2 - \<delta>\<^sup>2)/(2*b) + (A/b + 1) * (A/2 * \<epsilon>\<^sup>2 + \<epsilon> * (s$2))"
  apply (simp_all add: local_flow.fbox_g_ode_subset[OF local_flow_STTT_Ex5])
  apply(rule iffI, safe)
  oops

end

(*
% 10 unsolved problems
% 3 basic need sorry in arithmetic
% 1 advanced need sorry in arithmetic
% 1 basic has been solved with evol
% 1 advanced does not match Isabelle syntax
% 2 basic did not even try
% 1 basic is diamond
% 1 basic requires change of interval
*)

end