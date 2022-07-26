section \<open> Examples \<close>

text \<open> We prove partial correctness specifications of some hybrid systems with our 
verification components.\<close>

theory ARCH2022_Examples
  imports 
    HS_Lie_Derivatives
    Real_Arith_Tactics

begin


subsection \<open> Basic \<close>

lit_vars \<comment> \<open> disable constants \<close>
no_notation (ASCII) disj (infixr "|" 30)

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
  apply (subst fbox_solve[where \<phi>="\<lambda>t. [x \<leadsto> 2 * t + x]"]; simp add: wp)
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
  apply (subst fbox_solve[where \<phi>="\<lambda>t. [y \<leadsto> 2 * t + y]"]; simp)
   apply (local_flow 1)[1]
  apply (subst change_loopI[where I="(1 \<le> x \<and> 1 \<le> y)\<^sub>e"])
  apply (subst fbox_kcomp[symmetric], rule hoare_kcomp)
   apply (subst fbox_assign[where Q="(1 \<le> x \<and> 1 \<le> y)\<^sub>e"], expr_simp)
  apply(subst le_fbox_choice_iff, rule conjI)
  by (subst fbox_loopI, auto simp: wp)
    expr_simp+

lemma "\<^bold>{x \<ge> 0 \<and> y \<ge> 1\<^bold>} x ::= x + 1; ((LOOP x ::= x + 1 INV (x \<ge> 1) \<sqinter> y ::= x + 1); {y` = 2}; x ::= y) \<^bold>{x \<ge> 1\<^bold>}"
  apply (rule hoare_kcomp[where R="(x \<ge> 1 \<and> y \<ge> 1)\<^sup>e"])
   apply (hoare_wp_auto)
  apply (rule hoare_kcomp[where R="(x \<ge> 1 \<and> y \<ge> 1)\<^sup>e"])
   apply (rule hoare_kcomp[where R="(x \<ge> 1 \<and> y \<ge> 1)\<^sup>e"])
    apply (rule hoare_choice)
     \<comment> \<open> Use the fact that y is outside the frame of the loop to preserve its invariants \<close>
     apply (rule nmods_frame_law[where a="{y}\<^sub>v"])
       apply (rule nmods_loop)
        apply (simp)
       apply (rule nmods_assign)
         apply (simp_all add: unrest)
      apply unrest
     apply (rule hoare_loopI)
       apply (hoare_wp_auto)
      apply (expr_auto)
     apply (expr_auto)
    apply (hoare_wp_auto)
   apply (dInduct_mega)
  apply (hoare_wp_auto)
  done

end

subsubsection \<open> Potentially overwrite dynamics \<close>

context two_vars
begin

(* x>0 & y>0 -> [{x'=5}][{x:=x+3;}*@invariant(x>0) ++ y:=x;](x>0&y>0) *)

lemma "\<^bold>{x > 0 \<and> y > 0\<^bold>} {x` = 5} ; (LOOP x::=x+3 INV (x > 0) \<sqinter> y::=x) \<^bold>{x \<ge> 0 \<and> y \<ge> 0\<^bold>}"
proof -
  have "\<^bold>{x > 0 \<and> y > 0\<^bold>} {x` = 5} ; (LOOP x::=x+3 INV (x > 0) \<sqinter> y::=x) \<^bold>{x > 0 \<and> y > 0\<^bold>}"
    apply (rule hoare_kcomp_inv)
   apply (dInduct_mega)
    apply (rule hoare_choice)
     apply (rule nmods_frame_law[where a="{y}\<^sub>v"])
    apply (simp add: closure, unrest)
     apply (rule hoare_loopI)
       apply (hoare_wp_auto)
      apply expr_auto
     apply expr_auto
    apply (hoare_wp_auto)
    done
  thus ?thesis
    by (rule hoare_conseq; expr_auto)
qed

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
   apply (subst fbox_solve[where \<phi>="\<lambda>t. [x \<leadsto> x * exp (- t)]"]; clarsimp?)
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
   apply (subst fbox_solve[where \<phi>="\<lambda>t. [x \<leadsto> 5 * t + x]"]; clarsimp?)
   apply (local_flow 1)[1]
   apply (subst fbox_solve[where \<phi>="\<lambda>t. [x \<leadsto> 2 * t + x]"]; clarsimp?)
   apply (local_flow 1)[1]
  apply (subst fbox_solve[where \<phi>="\<lambda>t. [x \<leadsto> x * exp t]"]; clarsimp?)
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
  apply (subst fbox_solve[where \<phi>="\<lambda>t. [x \<leadsto> t + x]"]; clarsimp?)
  by (local_flow 1) expr_auto

end


subsubsection \<open> Dynamics: Single integrator \<close>

context two_vars
begin

(* x>=0 & y>=0 -> [{x'=y}]x>=0 *)
lemma "\<^bold>{x \<ge> 0 \<and> y \<ge> 0\<^bold>} {x` = y} \<^bold>{x \<ge> 0\<^bold>}"
  apply (subst fbox_solve[where \<phi>="\<lambda>t. [x \<leadsto> y * t + x]"]; clarsimp?)
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
  apply (subst fbox_solve[where \<phi>="\<lambda>t. [x \<leadsto> z * t\<^sup>2 / 2 + y * t + x, y \<leadsto> z * t + y]"]; clarsimp?)
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
  apply (subst fbox_solve[where \<phi>="\<lambda>t. [x \<leadsto> x * exp (- t)]"]; clarsimp?)
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
  apply (subst fbox_solve[where \<phi>="\<lambda>t. [x \<leadsto> 1 - exp (- t) + x * exp (- t)]"]; clarsimp?)
  by (local_flow 1, expr_auto) 
    (metis add_pos_nonneg diff_gt_0_iff_gt exp_eq_one_iff 
      exp_ge_zero exp_less_one_iff less_eq_real_def mult.commute mult_1 
      neg_equal_zero real_0_less_add_iff right_minus_eq zero_le_mult_iff)

end


subsubsection \<open> Dynamics: Exponential decay (3) \<close> (**)

context two_vars
begin

(* x>0 & y>0->[{x'=-y*x}]x>0 *)
lemma "`y > 0` \<Longrightarrow> (x > 0)\<^sub>e \<le> |{x` = - y * x}] (x > 0)"
  apply (subst fbox_solve[where \<phi>="\<lambda>t. [x \<leadsto> x * exp (- t * y)]"]; clarsimp?)
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
  apply (subst fbox_solve[where \<phi>="\<lambda>t. [x \<leadsto> x * exp t]"]; clarsimp?)
  by (local_flow 1) expr_auto 

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
lemma "(x \<ge> 1)\<^sub>e \<le> |{x` = x\<^sup>2 + 2 * x\<^sup>4}] (x^3 \<ge> x\<^sup>2)"
  apply (rule diff_cut_on_rule[where C="(1 \<le> x)\<^sup>e"])
   apply (diff_inv_on_ineq "(0)\<^sup>e" "(x\<^sup>2 + 2 * x\<^sup>4)\<^sup>e")
  apply (rule diff_cut_on_rule[where C="(x\<^sup>2 \<le> x\<^sup>3)\<^sup>e"])
   apply (rule fbox_inv[where I="(x\<^sup>2 \<le> x\<^sup>3)\<^sup>e"])
     apply (expr_simp add: le_fun_def numeral_Bit1 field_simps)
  apply (simp only: expr_defs hoare_diff_inv_on fbox_diff_inv_on)
  apply (diff_inv_on_single_ineq_intro "(2 * x * (x\<^sup>2 + 2 * x\<^sup>4))\<^sup>e" "(3 * x\<^sup>2 * (x\<^sup>2 + 2 * x\<^sup>4))\<^sup>e"; clarsimp)
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

lemma "(x\<^sup>2 + y\<^sup>2 = 1)\<^sub>e \<le> |{x` = -y, y` = x}] (x\<^sup>2 + y\<^sup>2 = 1)"
  apply (subst fbox_solve[where \<phi>="\<lambda>t. [x \<leadsto> $x * cos t + - 1 * $y * sin t, y \<leadsto> $y * cos t + $x * sin t]"])
  apply (clarsimp simp: local_flow_on_def)
  apply (unfold_locales; clarsimp?)
     apply (lipschitz 1, simp add: abs_minus_commute norm_Pair)
     apply vderiv
    apply expr_simp
  by expr_simp (smt (verit, ccfv_SIG) norm_rotate_eq(1))

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
lemma "(d1\<^sup>2 + d2\<^sup>2 = w\<^sup>2 * p\<^sup>2 \<and> d1 = - w * x2 \<and> d2 = w * x1)\<^sub>e \<le>
  |{x1` = d1, x2` = d2, d1` = - w * d2, d2` = w * d1}] 
  (d1\<^sup>2 + d2\<^sup>2 = w\<^sup>2 * p\<^sup>2 \<and> d1 = - w * x2 \<and> d2 = w * x1)"
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

lemma Collect_ge_ivl: "Collect ((\<le>) 0) = {(0::real)..}"
  by auto

context two_vars
begin

(* x^3>5 & y>2 -> [{x'=x^3+x^4, y'=5*y+y^2}](x^3>5 & y>2) *)
lemma "(x\<^sup>3 > 5 \<and> y > 2)\<^sub>e \<le> |{x` = x\<^sup>3 + x\<^sup>4, y` = 5*y + y\<^sup>2}] (x\<^sup>3 > 5 \<and> y > 2)"
  apply (rule fbox_invs; (rule fbox_invs)?)
  apply (expr_simp)
  apply (clarsimp simp only: fbox_diff_inv_on diff_inv_on_eq ivp_sols_def)
   apply (expr_simp add: Collect_ge_ivl)
  subgoal for s X t
    apply(rule current_vderiv_ge_always_ge[of 5 "\<lambda>t. (fst (X t))\<^sup>3" 0 
        "\<lambda>t. 3 * (fst (X t))\<^sup>2 * ((fst (X t))\<^sup>3 + (fst (X t))\<^sup>4)", where g="\<lambda>t. 3 * t\<^sup>2 + 3 * (root 3 t)\<^sup>5", rule_format])
    by (auto intro!: poly_derivatives simp: odd_real_root_power_cancel split: if_splits) 
      (clarsimp simp: fun_eq_iff, ferrack)
  apply (clarsimp simp only: fbox_diff_inv_on diff_inv_on_eq ivp_sols_def)
   apply (expr_simp add: Collect_ge_ivl)
  by (rule current_vderiv_ge_always_ge[rule_format, of 2 "\<lambda>t. (snd (_ t))", where g="\<lambda>t. 5 * t + t\<^sup>2"])
    (auto intro!: poly_derivatives simp: odd_real_root_power_cancel split: if_splits)

end



subsubsection \<open> Dynamics: Closed cases \<close>

context three_vars
begin

(* x>=1 & y=10 & z=-2 -> [{x'=y, y'=z+y^2-y & y>=0}](x>=1 & y>=0) *)
lemma "(x \<ge> 1 \<and> y = 10 \<and> z = - 2)\<^sub>e \<le> |{x` = y, y` =$z + y\<^sup>2 - y | y \<ge> 0}] (x \<ge> 1 \<and> y \<ge> 0)"
  apply (rule fbox_diff_invI[where I="(x \<ge> 1 \<and> y \<ge> 0)\<^sup>e"]; force?)
    apply (rule fbox_invs(1))
     apply expr_simp
    apply (simp only: expr_defs hoare_diff_inv_on fbox_diff_inv_on)
    apply (diff_inv_on_single_ineq_intro "(0)\<^sup>e" "(y)\<^sup>e"; expr_simp)
  apply (metis indeps(1) lens_plus_def plus_vwb_lens vwbs(1) vwbs(2))
  by (force intro!: poly_derivatives)
    (expr_simp add: hoare_diff_inv_on fbox_diff_inv_on diff_inv_on_eq)

end


subsubsection \<open> Dynamics: Conserved quantity \<close>

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
  apply (simp only: expr_defs hoare_diff_inv_on fbox_diff_inv_on)
  apply (diff_inv_on_single_ineq_intro "(0)\<^sup>e" "(0)\<^sup>e"; expr_simp)
  apply (intro poly_derivatives; (assumption)?, (rule poly_derivatives)?)
  by force+ ferrack

end


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

dataspace darboux =
  constants A::real B::real
  variables x::real y::real z::real

context darboux
begin

(* x+z=0 -> [{x'=(A*x^2+B()*x), z' = A*z*x+B()*z}] 0=-x-z *)
lemma "(x + z = 0)\<^sub>e \<le> |{x` = A*x\<^sup>2 + \<guillemotleft>B\<guillemotright>*x, z` = A*z*x+B*z | G on UNIV UNIV @ 0}] (0= -x - z)"
  apply (subgoal_tac "(0= -x - z)\<^sup>e = (x + z = 0)\<^sup>e"; force?)
  apply (erule ssubst)
  apply (simp only: expr_defs hoare_diff_inv_on fbox_diff_inv_on fbox_diff_inv_on')
  apply (expr_simp add: diff_inv_on_eq ivp_sols_def, clarsimp)
  subgoal for s X t
    apply (rule picard_lindeloef.ivp_unique_solution[of "(\<lambda>t r. r * (A * (fst (X t)) + B))" UNIV UNIV 0 "get\<^bsub>x\<^esub> s + get\<^bsub>z\<^esub> s" "\<lambda>s. UNIV" t 
          _ "\<lambda>t. 0"]; (clarsimp simp: ivp_sols_def)?)
      prefer 2 apply (intro poly_derivatives, force, force, force, force)
      apply (distribute, mon_pow_simp)
     prefer 2 apply (force intro!: poly_derivatives)
    apply (unfold_locales; clarsimp?)
     apply (force intro!: vderiv_on_continuous_on poly_derivatives)
    apply distribute
    apply (rule_tac f'="\<lambda>(t, r). Blinfun (\<lambda>r. r * (A * fst (X t)) + r * B) " in c1_implies_local_lipschitz; clarsimp?)
    apply (rule has_derivative_Blinfun)
     apply (auto intro!: derivative_eq_intros vderiv_on_continuous_on split: prod.splits)[1]
    apply (rule continuous_on_blinfun_componentwise)
    apply (simp add: prod.case_eq_if)
    apply (subst bounded_linear_Blinfun_apply)
    subgoal for i w
      apply (rule_tac f="(\<lambda>r. r * (A * fst (X (fst w))) + r * B)" in has_derivative_bounded_linear)
      by (auto intro!: derivative_eq_intros)
    by (auto intro!: continuous_intros vderiv_on_continuous_on
        continuous_on_compose[of UNIV fst X, unfolded comp_def] )
  done

end


subsubsection \<open> Dynamics: Fractional Darboux equality \<close> (*N 30 *)

context darboux
begin

(* x+z=0 -> [{x'=(A*y+B()*x)/z^2, z' = (A*x+B())/z & y = x^2 & z^2 > 0}] x+z=0 *)
lemma "(x + z = 0)\<^sub>e \<le> |{x` = (A*y + B*x)/z\<^sup>2, z` = (A*x+B)/z | (y = x\<^sup>2 \<and> z\<^sup>2 > 0)}] (x + z = 0)"
    oops

end


subsubsection \<open> Dynamics: Darboux inequality \<close> (*N 31 *)

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
      intro!: poly_derivatives split: if_splits)
  done

(* x+z>=0 -> [{x'=x^2, z' = z*x+y & y = x^2}] x+z>=0 *)
lemma "(x + z \<ge> 0)\<^sub>e \<le> |EVOL \<phi> (y = x\<^sup>2)\<^sub>e ({t. 0 \<le> t \<and> t * x < 1})\<^sub>e] (x + z \<ge> 0)"
  apply (subst fbox_g_evol)
  using var_defs darboux_ineq_arith
  by (clarsimp simp: expr_simps expr_defs)

no_notation darboux_ineq_f2 ("f") 
  and darboux_ineq_flow2 ("\<phi>")

end


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

context two_vars
begin

(* r <= 0 -> \exists f (x=f -> [{x'=r+x^2}]x=f) *)
lemma 
  fixes r::real
  shows "`\<guillemotleft>r\<guillemotright> \<le> 0` \<longrightarrow> (\<exists>f. (x=f)\<^sub>e \<le> |{x` = \<guillemotleft>r\<guillemotright> + x^2| True on UNIV UNIV @ 0}] (x=f))"
proof(clarsimp, rule_tac x="sqrt \<bar>r\<bar>" in exI, clarsimp simp: hoare_diff_inv_on diff_inv_on_eq ivp_sols_def)
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
     apply(erule ssubst, rule poly_derivatives)
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


subsubsection \<open> Dynamics: Parametric switching between two different damped oscillators \<close> (*N 33 *)

lemma dyn_param_switch_arith1:
  assumes hyp: "w\<^sup>2 * (y * a)\<^sup>2 + y\<^sup>2 \<le> c" 
    and w_hyp: "0 \<le> (w::real)" 
    and a_hyp: "- 2 \<le> a" "a \<le> 2" 
  shows "4 * w\<^sup>2 * (y * a)\<^sup>2 + y\<^sup>2 \<le> c * (16 * w\<^sup>2 + 1) / (4 * w\<^sup>2 + 1)"
  using assms apply -
  apply (auto simp: field_simps)
  apply (mon_simp_vars w a)
  apply (mon_simp_vars c w)
  apply ferrack
  sorry

lemma dyn_param_switch_arith2: "w\<^sup>2 * (y * b)\<^sup>2 + y\<^sup>2 \<le> (c::real) \<Longrightarrow>
          0 \<le> w \<Longrightarrow>
          1 \<le> b\<^sup>2 * 3 \<Longrightarrow>
          (w / 2)\<^sup>2 * (y * b)\<^sup>2 + y\<^sup>2 \<le> c * ((w / 2)\<^sup>2 + 1) / (2 * (w / 2)\<^sup>2 + 1)"
  apply (auto simp: field_simps)
  apply (mon_simp_vars w b)
  apply (mon_simp_vars c w)
  apply ferrack
  sorry


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
   apply (simp add: wp; expr_auto)[1]
    apply (rule diff_cut_on_rule[where C="(0 \<le> d \<and> 0 \<le> w \<and> -2 \<le> a \<and> a \<le> 2 \<and> b\<^sup>2 \<ge> 1/3)\<^sup>e"])
         apply (rule fbox_inv[where I="(0 \<le> d \<and> 0 \<le> w \<and> -2 \<le> a \<and> a \<le> 2 \<and> b\<^sup>2 \<ge> 1/3)\<^sup>e"])
  apply (expr_simp add: le_fun_def)
    apply (simp only: expr_defs hoare_diff_inv_on fbox_diff_inv_on)?
    apply (intro diff_inv_on_raw_conjI; (diff_inv_on_ineq "(0)\<^sup>e" "(0)\<^sup>e")?)
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
  by (auto intro!: poly_derivatives)

end


subsubsection \<open> Dynamics: Nonlinear 1 \<close>

dataspace dyn_nonlinear = 
  constants a :: real
  variables x1::real x2::real

context dyn_nonlinear
begin
(* x^3 >= -1 -> [{x'=(x-3)^4+a & a>=0}] x^3>=-1 *)
lemma "(x1\<^sup>3 \<ge> -1)\<^sub>e \<le> |{x1` = (x1-3)\<^sup>4 + a | (a\<ge>0)}] (x1\<^sup>3 \<ge> -1)"
  by (diff_inv_on_ineq "(0)\<^sup>e" "(3*x1\<^sup>2*((x1-3)\<^sup>4 + a))\<^sup>e")

end


subsubsection \<open> Dynamics: Nonlinear 2 \<close>

context dyn_nonlinear
begin

(* x1+x2^2/2=a -> [{x1'=x1*x2,x2'=-x1}]x1+x2^2/2=a *)
lemma "(x1 + x2\<^sup>2/2 = a)\<^sub>e \<le> |{x1` = x1 * x2, x2` = -x1}] (x1 + x2\<^sup>2/2 = a)"
  by (diff_inv_on_eq)

end


subsubsection \<open> Dynamics: Nonlinear 4 \<close>

context dyn_nonlinear
begin

(* x1^2/2-x2^2/2>=a -> [{x1'=x2+x1*x2^2, x2'=-x1+x1^2*x2 & x1>=0 & x2>=0}]x1^2/2-x2^2/2>=a *)
lemma "(x1\<^sup>2/2 - x2\<^sup>2/2 \<ge> a)\<^sub>e \<le> |{x1` = x2 + x1*x2\<^sup>2, x2` = -x1 + x1\<^sup>2 * x2| (x1 \<ge> 0 \<and> x2 \<ge> 0)}] (x1\<^sup>2/2 - x2\<^sup>2/2 \<ge> a)"
  apply (simp only: expr_defs hoare_diff_inv_on fbox_diff_inv_on)
  apply (diff_inv_on_single_ineq_intro "(0)\<^sup>e" "(x1 * (x2 + x1*x2\<^sup>2) - x2 * (-x1 + x1\<^sup>2 * x2))\<^sup>e"; expr_simp)
  by (auto simp: field_simps fun_eq_iff intro!: poly_derivatives split: if_splits)

end


subsubsection \<open> Dynamics: Nonlinear 5 \<close>

context dyn_nonlinear
begin

(* -x1*x2>=a -> [{x1'=x1-x2+x1*x2, x2'=-x2-x2^2}]-x1*x2>=a *)
lemma "(-x1*x2 \<ge> a)\<^sub>e \<le> |{x1` = x1 - x2 + x1*x2, x2` = -x2 - x2\<^sup>2}] (-x1*x2 \<ge> a)"
  apply (simp only: expr_defs hoare_diff_inv_on fbox_diff_inv_on)
  by (diff_inv_on_single_ineq_intro "(0)\<^sup>e" "((- x1 + x2 - x1*x2)*x2 - x1 * (-x2 - x2\<^sup>2))\<^sup>e"; expr_simp)
    (auto simp: field_simps fun_eq_iff intro!: poly_derivatives split: if_splits)

end


subsubsection \<open> Dynamics: Riccati \<close>

context two_vars
begin

(* 2*x^3 >= 1/4 -> [{x'=x^2+x^4}] 2*x^3>=1/4 *)
lemma "(2*x\<^sup>3 \<ge> 1/4)\<^sub>e \<le> |{x` = x\<^sup>2 + x^4}] (2*x\<^sup>3 \<ge> 1/4)"
  by (diff_inv_on_ineq "(0)\<^sup>e" "(6*x\<^sup>2*(x\<^sup>2 + x^4))\<^sup>e")

end


subsubsection \<open> Dynamics: Nonlinear differential cut \<close>

context two_vars
begin

(* x^3 >= -1 & y^5 >= 0 -> [{x'=(x-3)^4+y^5, y'=y^2}] (x^3 >= -1 & y^5 >= 0) *)
lemma "(x\<^sup>3 \<ge> -1 \<and> y\<^sup>5 \<ge> 0)\<^sub>e \<le> |{x` = (x-3)\<^sup>4+y\<^sup>5, y` = y\<^sup>2}] (x\<^sup>3 \<ge> -1 \<and> y\<^sup>5 \<ge> 0)"
  apply (diff_cut_ineq "(0 \<le> y\<^sup>5)\<^sup>e" "(0)\<^sup>e" "(5*y\<^sup>4*y\<^sup>2)\<^sup>e")
  apply (diff_cut_ineq "(-1 \<le> x\<^sup>3)\<^sup>e" "(0)\<^sup>e" "(3*x\<^sup>2*((x-3)\<^sup>4+y\<^sup>5))\<^sup>e")
  by (rule diff_weak_on_rule, expr_auto)

end


subsubsection \<open> STTT Tutorial: Example 1 \<close>

dataspace STTT =
  constants A::real B::real S::real V::real \<epsilon>::real
  variables x::real v::real a::real c::real

context STTT
begin

lemma "(v \<ge> 0 \<and> A > 0)\<^sub>e \<le> |{x` = v, v` = A}] (v \<ge> 0)"
  apply (rule diff_cut_on_rule[where C="(0 \<le> A)\<^sup>e"])
   apply (rule fbox_inv[where I="(0 \<le> A)\<^sup>e"])
     apply (expr_simp add: le_fun_def)
    apply (diff_inv_on_ineq "(0)\<^sup>e" "(0)\<^sup>e")
   apply vderiv
  apply (diff_cut_ineq "(0 \<le> v)\<^sup>e" "(0)\<^sup>e" "(A)\<^sup>e")
  by (rule diff_weak_on_rule, expr_auto)

end


subsubsection \<open> STTT Tutorial: Example 2 \<close>

context STTT
begin

lemma local_flow_STTT: "local_flow_on [v \<leadsto> $a, x \<leadsto> $v] (x +\<^sub>L v) UNIV UNIV 
  (\<lambda>t. [x \<leadsto> $a * t\<^sup>2 / 2 + $v * t + $x, v \<leadsto> $a * t + $v])"
  apply (clarsimp simp add: local_flow_on_def)
  apply (unfold_locales; expr_simp)
  apply (clarsimp simp: local_lipschitz_def lipschitz_on_def, rule_tac x=1 in exI)+
    apply (expr_simp, clarsimp simp: dist_norm split: prod.splits)
  by (metis norm_snd_le real_norm_def) (expr_simp, vderiv)

(* v >= 0 & A > 0 & B > 0 -> 
  [
    { {a := A; ++ a := 0; ++ a := -B;};
      { x' = v, v' = a & v >= 0 }
    }*@invariant(v >= 0)
  ] v >= 0 *)
lemma "(v \<ge> 0 \<and> A > 0 \<and> B > 0)\<^sub>e \<le> 
  |LOOP 
    ((a ::= A \<sqinter> a ::= 0 \<sqinter> a ::= -B); 
    ({x` = v, v` = a | (v \<ge> 0)})) 
   INV (v\<ge> 0)
  ] (v \<ge> 0)"
  by (hoare_wp_auto local_flow: local_flow_STTT)

end


subsubsection \<open> STTT Tutorial: Example 3a \<close> (* 37 *)

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

context STTT
begin

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
lemma "(v \<ge> 0 \<and> A > 0 \<and> B > 0 \<and> x + v\<^sup>2/(2*B) < S)\<^sub>e \<le>
  |LOOP 
    ((\<questiondown>x + v\<^sup>2/(2*B) < S?; a ::= A) 
      \<sqinter> (\<questiondown>v=0?; a ::= 0) 
      \<sqinter> (a ::= - B)
    );({x` = v, v` = a | (v \<ge> 0 \<and> x + v\<^sup>2/(2*B) \<le> S)}
      \<sqinter> {x` = v, v` = a | (v \<ge> 0 \<and> x + v\<^sup>2/(2*B) \<ge> S)}
    )
   INV (v \<ge> 0 \<and> x + v\<^sup>2/(2*B) \<le> S)
  ] (x \<le> S)"
  apply (subst change_loopI[where I="(v \<ge> 0 \<and> A > 0 \<and> B > 0 \<and> x + v\<^sup>2/(2*B) \<le> S)\<^sup>e"])
  apply (rule_tac hoare_loopI)
    apply (hoare_wp_simp local_flow: local_flow_STTT; expr_simp)
    apply (auto simp: STTexample3a_arith)
  by expr_simp (smt (verit, ccfv_threshold) divide_eq_0_iff divide_pos_pos 
      zero_less_power zero_power2)

end


subsubsection \<open> STTT Tutorial: Example 4a \<close>

context STTT
begin

(* v <= V & A > 0
 -> [
      { {
           ?v=V; a:=0;
        ++ ?v!=V; a:=A;
        }

        {x' = v, v' = a & v <= V}
      }*@invariant(v <= V)
    ] v <= V *)
lemma "(v \<le> V \<and> A > 0)\<^sub>e \<le>
  |LOOP 
    (
      (\<questiondown>v = V?; a ::= 0) 
      \<sqinter> (\<questiondown>v \<noteq> V?; a ::= A) 
    );(
      {x` = v, v` = a | (v \<le> V)}
    )
   INV (v \<le> V)
  ] (v \<le> V)"
  by (hoare_wp_auto local_flow: local_flow_STTT)

end


subsubsection \<open>STTT Tutorial: Example 4b\<close>

context STTT
begin

(* v <= V & A > 0 -> 
  [{ 
    a := A;
    {x' = v, v' = a & v <= V}
   }*@invariant(v <= V)
  ] v <= V *)
lemma "(v \<le> V \<and> A > 0)\<^sub>e \<le>
  |LOOP 
    (a ::= A);
    {x` = v, v` = a | (v \<le> V)}
   INV (v \<le> V)
  ] (v \<le> V)"
  by (hoare_wp_auto local_flow: local_flow_STTT)

end
 

subsubsection \<open>STTT Tutorial: Example 4c\<close>

context STTT
begin

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
lemma "(v \<le> V \<and> A > 0)\<^sub>e \<le>
  |LOOP 
    (
      (\<questiondown>v = V?; a ::= 0) 
      \<sqinter> (\<questiondown>v \<noteq> V?; a ::= A) 
    );(
      {x` = v, v` = a | (v \<le> V)}
      \<sqinter> {x` = v, v` = a | (v \<ge> V)}
    )
   INV (v \<le> V)
  ] (v \<le> V)"
  by (hoare_wp_auto local_flow: local_flow_STTT)

end


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

context STTT
begin

lemma local_flow_STTT2: "local_flow_on [c \<leadsto> 1, v \<leadsto> $a, x \<leadsto> $v] (x +\<^sub>L v +\<^sub>L c) UNIV UNIV
  (\<lambda>t. [c \<leadsto> t + c, x \<leadsto> $a * t\<^sup>2 / 2 + $v * t + $x, v \<leadsto> $a * t + $v])"
  apply (clarsimp simp add: local_flow_on_def)
  apply (unfold_locales; expr_simp)
  by (rule c1_implies_local_lipschitz[of UNIV UNIV _ "(\<lambda>(t::real,c). Blinfun (\<lambda>c. (fst (snd c), 0)))"])
    (auto intro!: has_derivative_Blinfun derivative_eq_intros poly_derivatives)

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
lemma "(v \<ge> 0 \<and> A > 0 \<and> B > 0 \<and> x + v\<^sup>2/(2 * B) \<le> S \<and> \<epsilon> > 0)\<^sub>e \<le>
  |LOOP 
    ((\<questiondown>x + v\<^sup>2/(2*B) + (A/B + 1)*(A/2*\<epsilon>\<^sup>2 + \<epsilon> * v) \<le> S?; a ::= A) 
      \<sqinter> (\<questiondown>v=0?; a ::= 0) 
      \<sqinter> (a ::= - B)
    );(
      (c ::= 0); 
      {x` = v, v` = a, c` = 1 | (v \<ge> 0 \<and> x + v\<^sup>2/(2*B) \<le> S)}
    )
   INV (v \<ge> 0 \<and> x + v\<^sup>2/(2 * B) \<le> S)
  ] (x \<le> S)"
  apply (subst change_loopI[where I="(v \<ge> 0 \<and> A > 0 \<and> B > 0 \<and> x + v\<^sup>2/(2*B) \<le> S \<and> \<epsilon> > 0)\<^sup>e"])
  apply (rule_tac hoare_loopI)
    apply (hoare_wp_simp local_flow: local_flow_STTT2; expr_simp)
   apply (auto simp: STTexample5_arith)
  by expr_auto
    (smt (verit, best) divide_eq_0_iff divide_pos_pos zero_eq_power2 zero_less_power2)

end


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

context STTT
begin

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
lemma "(v \<ge> 0 \<and> A > 0 \<and> B > 0 \<and> x + v\<^sup>2/(2 * B) \<le> S \<and> \<epsilon> > 0)\<^sub>e \<le>
  |LOOP 
    ((\<questiondown>x + v\<^sup>2/(2*B) + (A/B + 1)*(A/2*\<epsilon>\<^sup>2 + \<epsilon> * v) \<le> S?; a ::= ?; \<questiondown>-B \<le> a \<and> a \<le> A?) 
      \<sqinter> (\<questiondown>v=0?; a ::= 0) 
      \<sqinter> (a ::= - B)
    );(
      (c ::= 0); 
      {x` = v, v` = a, c` = 1 | (v \<ge> 0 \<and> c \<le> \<epsilon>)}
    )
   INV (v \<ge> 0 \<and> x + v\<^sup>2/(2 * B) \<le> S)
  ] (x \<le> S)"
  apply (subst change_loopI[where I="(v \<ge> 0 \<and> A > 0 \<and> B > 0 \<and> x + v\<^sup>2/(2*B) \<le> S \<and> \<epsilon> > 0)\<^sup>e"])
  apply (rule_tac hoare_loopI)
    apply (hoare_wp_simp local_flow: local_flow_STTT2; expr_simp)
  prefer 3 subgoal by expr_simp (smt (verit, best) divide_eq_0_iff divide_pos_pos zero_less_power zero_power2)
   prefer 2 subgoal by expr_simp
  apply (expr_simp, clarsimp, intro conjI; clarsimp simp: STTexample3a_arith STTexample6_arith)
  by (rule STTexample6_arith[of A B \<epsilon> "get\<^bsub>v\<^esub> _" _ _ "get\<^bsub>x\<^esub> _" S])
    (auto simp: field_simps)

end

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

context STTT
begin

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
lemma "(v \<ge> 0 \<and> A > 0 \<and> B \<ge> b \<and> b > 0 \<and> x + v\<^sup>2/(2 * b) \<le> S \<and> \<epsilon> > 0)\<^sub>e \<le>
  |LOOP 
    ((\<questiondown>x + v\<^sup>2/(2*b) + (A/b + 1)*(A/2*\<epsilon>\<^sup>2 + \<epsilon> * v) \<le> S?; a ::= ?; \<questiondown>-B \<le> a \<and> a \<le> A?) 
      \<sqinter> (\<questiondown>v=0?; a ::= 0) 
      \<sqinter> (a ::= ?; \<questiondown>-B \<le> a \<and> a \<le> - b?)
    );(
      (c ::= 0); 
      {x` = v, v` = a, c` = 1 | (v \<ge> 0 \<and> c \<le> \<epsilon>)}
    )
   INV (v \<ge> 0 \<and> x + v\<^sup>2/(2 * b) \<le> S)
  ] (x \<le> S)"
  apply (subst change_loopI[where I="(v \<ge> 0 \<and> A > 0 \<and> B \<ge> b \<and> b > 0 \<and> x + v\<^sup>2/(2*b) \<le> S \<and> \<epsilon> > 0)\<^sup>e"])
  apply (rule_tac hoare_loopI)
    apply (hoare_wp_simp local_flow: local_flow_STTT2; expr_simp)
    prefer 3 subgoal by expr_simp (smt not_sum_power2_lt_zero zero_compare_simps(5))
   prefer 2 subgoal by expr_simp
  apply (expr_simp, clarsimp, intro conjI; clarsimp simp: STTexample7_arith1 STTexample7_arith2)
  by (rule STTexample7_arith1[of A b \<epsilon>]; clarsimp simp: field_simps)
    (rule STTexample7_arith2[of b "get\<^bsub>v\<^esub> _" _ _ "get\<^bsub>x\<^esub> _" S \<epsilon>]; clarsimp simp: field_simps)

end


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

context STTT
begin

(* v >= 0 & c() > 0 & Kp() = 2 & Kd() = 3 & 5/4*(x-xr())^2 + (x-xr())*v/2 + v^2/4 < c()
 -> [
      { x' = v, v' = -Kp()*(x-xr()) - Kd()*v }
    ] 5/4*(x-xr())^2 + (x-xr())*v/2 + v^2/4 < c() *)
lemma "(v \<ge> 0 \<and> c > 0 \<and> Kp = 2 \<and> Kd = 3 \<and> (5/4)*(x-xr)\<^sup>2 + (x-xr)* v/2 + v\<^sup>2/4 < c)\<^sub>e \<le>
  |{x` = v, v` = -Kp * (x-xr) - Kd * v}] 
  ((5/4)*(x-xr)\<^sup>2 + (x-xr)* v/2 + v\<^sup>2/4 < c)"
  apply (rule diff_cut_on_rule[where C="(c > 0 \<and> Kp = 2 \<and> Kd = 3)\<^sup>e"])
   apply (rule fbox_inv[where I="(c > 0 \<and> Kp = 2 \<and> Kd = 3)\<^sup>e"])
     apply (expr_simp add: le_fun_def)
    apply (simp only: expr_defs hoare_diff_inv_on fbox_diff_inv_on)
    apply (intro diff_inv_on_raw_conjI; (diff_inv_on_ineq "(0)\<^sup>e" "(0)\<^sup>e" | diff_inv_on_eq))
       apply expr_simp
   apply (rule fbox_inv[where I="((5/4)*(x-xr)\<^sup>2 + (x-xr)* v/2 + v\<^sup>2/4 < c)\<^sup>e"])
    apply (expr_simp add: le_fun_def)
  prefer 2 apply (expr_simp add: le_fun_def)
   apply (expr_simp add: hoare_diff_inv_on fbox_diff_inv_on)
  apply (diff_inv_on_single_ineq_intro "(10 *(x-xr) * v/4 + v\<^sup>2/2 + (x-xr)*(-Kp * (x-xr) - Kd * v)/2 
  + (v/2) * (-Kp * (x-xr) - Kd * v))\<^sup>e" "(0)\<^sup>e"; 
      expr_simp add: le_fun_def STTexample9a_arith)
  apply (metis indeps(1) lens_plus_def plus_vwb_lens vwbs(1) vwbs(2))
  by (intro poly_derivatives; (rule poly_derivatives)?; force?)
    (auto simp: field_simps)

end


subsubsection \<open> STTT Tutorial: Example 9b \<close> (*N 50 *)

lemma STTT_9b_arith1:
  assumes "0 \<le> (v::real)" and "xm \<le> x" and "xr * 2 = xm + S" 
    and "5 * (x - xr)\<^sup>2 / 4 + (x - xr) * v / 2 + v\<^sup>2 / 4 < ((S - xm) / 2)\<^sup>2" 
  shows "x \<le> S"
  sorry

dataspace STTT_9b =
  constants S::real Kp::real Kd::real
  variables x::real v::real xm::real xr::real

context STTT_9b
begin

(* x' = v, v' = -Kp*(x-xr) - Kd*v with Kp = 2 & Kd = 3*)
lemma local_flow_STTT_9b: "local_flow_on [v \<leadsto> 2 * xr - 2 * x - 3 * v, x \<leadsto> v] (x +\<^sub>L v) UNIV UNIV 
  (\<lambda>t. [x \<leadsto> exp (-2*t) * (xr - 2 * xr * exp t + xr * exp (2 * t) - v + v * exp t - x + 2 * x * exp t), 
  v \<leadsto> exp (-2*t) * (-2 * xr + 2 * xr * exp t + 2 * v - v * exp t + 2 * x - 2 * x * exp t)])"
  apply (clarsimp simp add: local_flow_on_def)
  apply (unfold_locales; expr_simp)
  apply (rule c1_implies_local_lipschitz[of UNIV UNIV _ 
        "(\<lambda>(t::real,c). Blinfun (\<lambda>c. (snd c, - 2 * fst c - 3 * snd c)))"]; expr_simp)
  by (auto intro!: has_derivative_Blinfun derivative_eq_intros poly_derivatives split: if_splits)
    (auto simp: fun_eq_iff field_simps exp_minus_inverse)

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
lemma "Kp = 2 \<Longrightarrow> Kd = 3 \<Longrightarrow> (v \<ge> 0 \<and> xm \<le> x \<and> x \<le> S \<and> xr = (xm + S)/2  
  \<and> (5/4)*(x-xr)\<^sup>2 + (x-xr)* v/2 + v\<^sup>2/4 < ((S - xm)/2)\<^sup>2)\<^sub>e \<le>
  |LOOP 
    ((xm ::= x; 
      xr ::= (xm + S)/2;
      \<questiondown>5/4*(x-xr)\<^sup>2 + (x-xr)* v/2 + v\<^sup>2/4 < ((S - xm)/2)\<^sup>2?) 
    \<sqinter> \<questiondown>True?);
    {x` = v, v` = -Kp * (x-xr) - Kd * v | v \<ge> 0}
   INV (v \<ge> 0 \<and> xm \<le> x \<and> xr = (xm + S)/2 \<and> 5/4*(x-xr)\<^sup>2 + (x-xr)* v/2 + v\<^sup>2/4 < ((S - xm)/2)\<^sup>2)] 
  (x \<le> S)"
  apply (subst change_loopI[where I="(v \<ge> 0 \<and> xm \<le> x \<and> xr = (xm + S)/2 \<and> Kp = 2 \<and> Kd = 3 
  \<and> 5/4*(x-xr)\<^sup>2 + (x-xr)* v/2 + v\<^sup>2/4 < ((S - xm)/2)\<^sup>2)\<^sup>e"])
  apply (rule hoare_loopI)
    prefer 3 subgoal
    using STTT_9b_arith1[of "get\<^bsub>v\<^esub> _" "get\<^bsub>xm\<^esub> _" "get\<^bsub>x\<^esub> _"]
    by expr_simp force
   prefer 2 apply expr_simp
  apply simp
  apply (rule_tac R="(v \<ge> 0 \<and> xm \<le> x \<and> x \<le> S \<and> xr = (xm + S)/2  
  \<and> (5/4)*(x-xr)\<^sup>2 + (x-xr)* v/2 + v\<^sup>2/4 < ((S - xm)/2)\<^sup>2)\<^sup>e" in hoare_kcomp)
   apply (subst le_fbox_choice_iff)
   apply (intro conjI[rotated])
  subgoal
    using STTT_9b_arith1[of "get\<^bsub>v\<^esub> _" "get\<^bsub>xm\<^esub> _" "get\<^bsub>x\<^esub> _"]
    by (simp add: wp, expr_simp, force)
  subgoal
    using STTT_9b_arith1[of "get\<^bsub>v\<^esub> _" "get\<^bsub>xm\<^esub> _" "get\<^bsub>x\<^esub> _"]
    by (simp add: wp, expr_simp, force)
  apply (rule_tac C="(xm \<le> x \<and> xr = (xm + S) / 2)\<^sup>e" in diff_cut_on_rule)
  subgoal
    apply (rule_tac a="(xm \<le> x \<and> xr = (xm + S) / 2)\<^sup>e" and b="(v \<ge> 0 \<and> x \<le> S 
  \<and> (5/4)*(x-xr)\<^sup>2 + (x-xr)* v/2 + v\<^sup>2/4 < ((S - xm)/2)\<^sup>2)\<^sup>e" in hoare_conj_preI)
     prefer 2 apply (force simp: fun_eq_iff)
    apply (rule fbox_invs)
     apply (simp only: expr_defs hoare_diff_inv_on fbox_diff_inv_on)?
     apply (diff_inv_on_single_ineq_intro "(0)\<^sup>e" "(v)\<^sup>e"; expr_simp)
    by (auto intro!: poly_derivatives)[1](diff_inv_on_eq)
  apply simp
  apply (rule_tac I="(5 * ($x - $xr)\<^sup>2 / 4 + ($x - $xr) * $v / 2 + ($v)\<^sup>2 / 4 < ((S - $xm) / 2)\<^sup>2)\<^sup>e" in fbox_diff_invI)
    prefer 3 apply expr_auto
   prefer 2 apply expr_auto
    apply (simp add: field_class.power_divide add_divide_distrib sign_distrib_laws, bin_unfold?, distribute?)+
    apply (simp only: expr_defs hoare_diff_inv_on fbox_diff_inv_on)?
    apply (diff_inv_on_single_ineq_intro "(10 * $x * ($v) - 10 * $v * $xr
    + (2 * ((2 * $xr - 2 * $x - 3 * $v) * $x) + 2 * ($v)\<^sup>2
    - 2 * ((2 * $xr - 2 * $x - 3 * $v) * $xr))
    + 2 * ($v) * (2 * $xr - 2 * $x - 3 * $v))\<^sup>e" "(0)\<^sup>e"; expr_simp)
   prefer 2 
  subgoal for X s
    apply (simp add: sign_distrib_laws, distribute?)
    apply (intro poly_derivatives; (force | (rule poly_derivatives))?)
    by (simp add: sign_distrib_laws, distribute?) 
      (simp add: power2_eq_square[symmetric])
    apply (clarsimp simp: field_class.power_divide add_divide_distrib, bin_unfold?, distribute?)
  apply (clarsimp simp: field_class.power_divide add_divide_distrib power2_eq_square[symmetric])
  by (smt (verit, ccfv_SIG) distrib_right realpow_square_minus_le sum_squares_bound)


end


subsubsection \<open> STTT Tutorial: Example 10 \<close> (*N 51 *)

dataspace STTT_10 =
  constants A::real B::real \<epsilon>::real
  variables a::real v::real x::real dx::real y::real dy::real w::real r::real c::real

definition annot_inv :: "'a \<Rightarrow> 'b \<Rightarrow> 'a" (infixr "@inv" 65)
  where "x @inv i = x"

lemma fbox_kcompI: "P \<le> |X1] (@R) \<Longrightarrow> R \<le> |X2] (@Q) \<Longrightarrow> P \<le> |X1 ; X2] (@Q)"
  by (simp add: fbox_kcomp) (auto simp: fbox_def)

lemma new_varI: 
  "(\<And>k. (@P \<and> $x = k)\<^sub>e \<le> |X] (@Q)) \<Longrightarrow> (@P)\<^sub>e \<le> |X] (@Q)"
  "(\<And>k. (@P \<and> $x = k)\<^sub>e \<le> |X] (@Q)) \<Longrightarrow> (\<lambda>s. P s) \<le> |X] (@Q)"
  by (expr_auto add: fbox_def)+

lemma circumf_within_square:
  fixes x::real
  assumes "x\<^sup>2 + y\<^sup>2 = r\<^sup>2" and "0 < r"
  shows "-r \<le> x" and "x \<le> r"
    and "-r \<le> y" and "y \<le> r"
proof-
  have "x\<^sup>2 \<ge> 0" and "y\<^sup>2 \<ge> 0"
    by force+
  hence "x\<^sup>2 \<le> r\<^sup>2" and "y\<^sup>2 \<le> r\<^sup>2"
    using assms by linarith+
  hence "\<bar>x\<bar> \<le> r" and "\<bar>y\<bar> \<le> r"
    using real_le_rsqrt assms
    by (meson less_eq_real_def power2_le_iff_abs_le)+
  thus "-r \<le> x" and "x \<le> r"
    and "-r \<le> y" and "y \<le> r"
    by linarith+
qed

lemma STTT_10_arith1:
  assumes v_ge0: "0 \<le> (v::real)"
    and v_eq: "v = a * c + v0"
    and circumf: "(dx)\<^sup>2 + (dy)\<^sup>2 = 1" 
  shows "- (a * c) - v0 \<le> (a * c + v0) * dy" 
    and "(a * c + v0) * dy \<le> (a * c) + v0"
  using assms circumf_within_square[where r=1, simplified]
proof-
  have in_square: "-1 \<le> dy \<and> dy \<le> 1"
    using circumf_within_square[where r=1] 
      circumf by auto
  hence "- v \<le> v * dy \<and> v * dy \<le> v"
  proof(cases "dy \<ge> 0")
    case True
    hence "- v \<le> v * dy"
      using v_ge0
      by (meson mult_nonneg_nonneg neg_le_0_iff_le order_trans)
    moreover have "v * dy \<le> v"
      using in_square True
        mult_left_le v_ge0 by blast
    ultimately show ?thesis 
      by simp
  next
    case False
    hence "- v \<le> v * dy"
      using v_ge0 in_square
      by (metis minus_le_iff mult.commute mult_left_le 
          vector_space_over_itself.scale_minus_left)
    moreover have "v * dy \<le> v"
      using in_square False
        mult_left_le v_ge0 by blast
    ultimately show ?thesis 
      by simp
  qed
  thus "- (a * c) - v0 \<le> (a * c + v0) * dy" 
    and "(a * c + v0) * dy \<le> (a * c) + v0"
    using v_eq 
    by auto
qed

lemma STTT_10_arith2:
  assumes "t \<le> \<epsilon>" and "v = a * t + v0" and "0 \<le> (t::real)" 
    and v_ge: "0 \<le> a * t + v0" 
    and "0 < A" and "0 < b" and "a \<le> A" and "0 \<le> v0" 
    and delta_hyps: "a * t\<^sup>2 / 2 - t * (a * t + v0) \<le> y - y0"
    "y - y0 \<le> t * (a * t + v0) - a * t\<^sup>2 / 2" 
    and abs_hyp: "\<bar>y0 - ly\<bar> + v0\<^sup>2 / (2 * b) + (A / b + 1) * (A * \<epsilon>\<^sup>2 / 2 + \<epsilon> * v0) < lw"
  shows "\<bar>y - ly\<bar> + (a * t + v0)\<^sup>2 / (2 * b) < lw"
proof-
  have fact1: "v0\<^sup>2 / (2 * b) \<ge> 0"
    using \<open>0 \<le> v0\<close> \<open>0 < b\<close> by auto
  have fact2: "A / b + 1 > 1"
    using \<open>0 < A\<close> \<open>0 < b\<close>
    by (simp add: add_pos_pos)
  have "a * t + v0 \<le> A * t + v0"
    using \<open>a \<le> A\<close> \<open>0 \<le> t\<close> \<open>0 \<le> v0\<close>
    by (simp add: mult_right_mono) 
  hence fact3: "(a * t + v0)\<^sup>2 / (2 * b) \<le> (A * t + v0)\<^sup>2 / (2 * b)"
    using \<open>0 < b\<close> apply -
    by (frule power_mono[OF _ v_ge, of "A * t + v0" 2])
      (rule divide_right_mono, auto)
  have fact4: "a * t\<^sup>2 / 2 \<le> A * t\<^sup>2 / 2"
    using \<open>a \<le> A\<close>
    by (simp add: mult_right_mono)
  have fact5: "A\<^sup>2 * t\<^sup>2 / (2 * b) + A * t * v0 / b + v0\<^sup>2 / (2 * b) = (A*t + v0)\<^sup>2/(2*b)"
    by (bin_unfold, simp add: add_divide_distrib)
  have "A * t\<^sup>2 / 2 \<le> A * \<epsilon>\<^sup>2 / 2" (* here we start the proof *)
    using \<open>t \<le> \<epsilon>\<close> \<open>0 < A\<close> \<open>0 \<le> v0\<close> \<open>0 \<le> t\<close>
    by auto
  moreover have "t * v0 \<le> \<epsilon> * v0"
    using \<open>t \<le> \<epsilon>\<close> \<open>0 < A\<close> \<open>0 \<le> v0\<close> \<open>0 \<le> t\<close>
    by (simp add: mult_right_mono)
  ultimately have "A * t\<^sup>2 / 2 + t * v0 \<le> A * \<epsilon>\<^sup>2 / 2 + \<epsilon> * v0"
    by linarith
  hence "(A / b + 1) * (A * t\<^sup>2 / 2 + t * v0) \<le> (A / b + 1) * (A * \<epsilon>\<^sup>2 / 2 + \<epsilon> * v0)"
    using fact2
    by (simp add: mult_left_mono)
  hence key: "\<bar>y0 - ly\<bar> < lw - v0\<^sup>2 / (2 * b) - (A / b + 1) * (A * t\<^sup>2 / 2 + t * v0)" (is "_ < ?J")
    using abs_hyp by linarith
  have J_eqK: 
    "?J = lw - v0\<^sup>2 / (2 * b) - A\<^sup>2 * t\<^sup>2 / (2 * b) - A * t * v0 / b - A * t\<^sup>2 / 2 - t * v0" (is "_ = ?K")
    by (auto simp: field_simps)
  hence "y0 - ly < ?J"
    using key by linarith
  moreover have "y - y0 \<le> a * t\<^sup>2 / 2 + t * v0"
    using delta_hyps(2) 
    by (auto simp: field_simps)
  ultimately have "y - ly < ?J + a * t\<^sup>2 / 2 + t * v0"
    by linarith
  also have "... \<le> lw - (A * t + v0)\<^sup>2 / (2 * b)"
    using J_eqK fact4 fact5 by linarith
  also have "... \<le> lw - (a * t + v0)\<^sup>2 / (2 * b)"
    using fact1 fact3 by linarith
  finally have result1: "y - ly < lw - (a * t + v0)\<^sup>2 / (2 * b)" .
  have "- ?J < y0 - ly"
    using key by linarith
  moreover have "- a * t\<^sup>2 / 2 - t * v0 \<le> y - y0"
    using delta_hyps(1) 
    by (auto simp: field_simps)
  ultimately have "y - ly > - ?J - a * t\<^sup>2 / 2 - t * v0"
    by linarith
  moreover have "- ?J - a * t\<^sup>2 / 2 - t * v0 \<ge> - lw + (A * t + v0)\<^sup>2 / (2 * b)"
    using J_eqK fact1 fact4 fact5 by linarith
  moreover have "- lw + (A * t + v0)\<^sup>2 / (2 * b) \<ge> - lw + (a * t + v0)\<^sup>2 / (2 * b)"
    using fact1 fact3 by linarith
  ultimately have result2: "-lw + (a * t + v0)\<^sup>2 / (2 * b) < y - ly" 
    by linarith
  show "\<bar>y - ly\<bar> + (a * t + v0)\<^sup>2 / (2 * b) < lw"
    using result1 result2 by linarith
qed

lemma STTT_10_arith3:
  assumes v_eq: "v = a * t + v0" 
    and "0 \<le> (t::real)" and v_ge0: "0 \<le> a * t + v0" 
    and "0 < b" and "0 \<le> v0" and "a \<le> - b" 
    and delta_hyps: "a * (t)\<^sup>2 / 2 - t * (a * t + v0) \<le> y - y0" 
    "y - y0 \<le> t * (a * t + v0) - a * (t)\<^sup>2 / 2" 
    and abs_hyp: "\<bar>y0 - ly\<bar> + v0\<^sup>2 / (2 * b) < lw"
  shows "\<bar>y - ly\<bar> + (a * t + v0)\<^sup>2 / (2 * b) < lw"
proof-
  have "a < 0" "(v + v0)*t \<ge> 0" "b \<le> - a"
    using \<open>0 < b\<close> \<open>a \<le> - b\<close> \<open>0 \<le> v0\<close> 
      v_eq v_ge0 \<open>0 \<le> t\<close>
    by auto
  hence "b*(v + v0)*t \<le> - a*(v + v0)*t"
    using mult_right_mono[OF \<open>b \<le> - a\<close> \<open>(v + v0)*t \<ge> 0\<close>]
    by auto
  hence "b*(v + v0)*t/(2*b) \<le> - a*(v + v0)*t/(2*b)"
    using \<open>0 < b\<close>
    by (simp add: mult_left_mono)
      (auto simp: field_simps)
  hence fact1: "(v + v0)*t/2 \<le> - a*(v + v0)*t/(2*b)"
    using \<open>0 < b\<close>
    by auto
  have fact2: "(a * t + v0)\<^sup>2 / (2 * b) = v0\<^sup>2 / (2 * b) + a*(v + v0)*t/ (2 * b)"
    by (auto simp add: add_divide_distrib v_eq field_simps)
  have "a * t\<^sup>2/2 + v0 * t = (a * t\<^sup>2 + v0 * t + v0 * t)/2"
    by (simp add: add_divide_distrib)
  also have "... = (v + v0)*t/2"
    using v_eq 
    by (auto simp: field_simps)
  finally have fact3: "a * t\<^sup>2/2 + v0 * t = (v + v0)*t/2" .
  hence "y - y0 \<le> (v + v0)*t/2"
    using delta_hyps(2)
    by (auto simp: field_simps)
  moreover have "y0 - ly < lw - v0\<^sup>2 / (2 * b)"
    using abs_hyp by linarith
  ultimately have "y - ly < lw - v0\<^sup>2 / (2 * b) + (v + v0)*t/2"
    by linarith
  hence result1: "y - ly < lw - (a * t + v0)\<^sup>2 / (2 * b)"
    using fact1 fact2 by linarith
  have "- (v + v0)*t/2 \<le> y - y0"
    using delta_hyps(1) fact3
    by (auto simp: field_simps)
  moreover have "- lw + v0\<^sup>2 / (2 * b) < y0 - ly"
    using abs_hyp by linarith
  ultimately have "- lw + v0\<^sup>2 / (2 * b) - (v + v0)*t/2 < y - ly"
    by linarith
  hence result2: "- (lw - (a * t + v0)\<^sup>2 / (2 * b)) < y - ly"
    using fact1 fact2 by linarith
  show "\<bar>y - ly\<bar> + (a * t + v0)\<^sup>2 / (2 * b) < lw"
    using result1 result2 by linarith
qed

context STTT_10
begin 

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
lemma "`(v \<ge> 0 \<and> A > 0 \<and> B \<ge> b \<and> b > 0 \<and> \<epsilon> > 0 \<and> lw > 0 \<and> y = ly \<and> r \<noteq> 0 \<and> dx\<^sup>2 + dy\<^sup>2 = 1
           \<and> \<bar>y-ly\<bar> + v\<^sup>2/(2*b) < lw)
 \<longrightarrow> ( |LOOP
      ( (   (\<questiondown>\<bar>y - ly\<bar> + v\<^sup>2/(2*b) + (A/b+1)*(A/2*\<epsilon>\<^sup>2+\<epsilon>* v) < lw?;
            a ::= ?; \<questiondown>-B \<le> a \<and> a \<le> A?;
            w ::= ?; r ::= ?; \<questiondown>r \<noteq> 0 \<and> w*r = v?)
         \<sqinter> (\<questiondown>v=0?; a ::= 0; w ::= 0)
         \<sqinter> (a ::= ?; \<questiondown>-B \<le> a \<and> a \<le> -b?)
        );
        c ::= 0;
        (
        {x` = v * dx, y` = v * dy, v` = a, dx` = -dy*w, dy` = dx*w, w` = a/r, c` = 1 | v >= 0 \<and> c \<le> \<epsilon>}
        @inv (c \<ge> 0 \<and> dx\<^sup>2+dy\<^sup>2=1 \<and>
          (v'=a \<longrightarrow> v = old(v)+a*c) \<and>
          (v'=a \<longrightarrow> -c*(v-a/2*c) \<le> y - old(y) \<and> y - old(y) \<le> c*(v-a/2*c)) \<and>
          (v'=0 \<longrightarrow> v = old(v)) \<and>
          (v'=0 \<longrightarrow> -c * v \<le> y - old(y) \<and> y - old(y) \<le> c * v)
        )\<^sub>e
        )
      ) INV (v \<ge> 0 \<and> dx\<^sup>2+dy\<^sup>2 = 1 \<and> r \<noteq> 0 \<and> \<bar>y - ly\<bar> + v\<^sup>2/(2*b) < lw)
    ] (\<bar>y - ly\<bar> < lw))`"
  apply (subst impl_eq_leq)
  apply (subst change_loopI[where I="(v \<ge> 0 \<and> A > 0 \<and> B \<ge> b \<and> b > 0 \<and> \<epsilon> > 0 \<and> lw > 0 \<and> r \<noteq> 0 
  \<and> dx\<^sup>2+dy\<^sup>2 = 1 \<and> \<bar>y - ly\<bar> + v\<^sup>2/(2*b) < lw)\<^sup>e"])
  apply (rule fbox_loopI)
    apply (clarsimp simp: le_fun_def)
   apply (clarsimp simp: le_fun_def)
   apply (smt (verit, best) divide_eq_0_iff divide_pos_pos zero_less_power zero_power2)
  apply (rule_tac R="(v \<ge> 0 \<and> A > 0 \<and> B \<ge> b \<and> b > 0 \<and> \<epsilon> > 0 \<and> lw > 0 \<and> r \<noteq> 0 \<and> dx\<^sup>2+dy\<^sup>2 = 1 
    \<and> \<bar>y - ly\<bar> + v\<^sup>2/(2*b) < lw \<and> c=0
    \<and> ((\<bar>y - ly\<bar> + v\<^sup>2/(2*b) + (A/b+1)*(A/2*\<epsilon>\<^sup>2+\<epsilon>* v) < lw \<and> -B \<le> a \<and> a \<le> A \<and> w*r = v)
      \<or> (v = 0 \<and> a = 0 \<and> w = 0)
      \<or> (-B \<le> a \<and> a \<le> -b)))\<^sup>e" in fbox_kcompI)
   apply (clarsimp simp: wp, expr_simp, hol_clarsimp)
  apply (rule_tac x=v in new_varI(2))
  apply (rule_tac x=y in new_varI(2))
  apply (rename_tac v0 y0)
  apply (simp only: annot_inv_def)
  apply (rule_tac C="(v = a * c + v0)\<^sup>e" in diff_cut_on_rule)
  subgoal for v0 y0
    apply (rule_tac I="(v = a * c + v0)\<^sup>e" in fbox_diff_invI)
    by (diff_inv_on_eq) (clarsimp simp: le_fun_def)+
  apply (rule_tac C="(c \<ge> 0 \<and> v \<ge> 0 \<and> dx\<^sup>2+dy\<^sup>2 = 1 \<and> A > 0 \<and> B \<ge> b \<and> b > 0 \<and> \<epsilon> > 0 \<and> lw > 0 \<and> r \<noteq> 0)\<^sup>e" in diff_cut_on_rule)
  subgoal for v0 y0
    apply (rule_tac I="(c \<ge> 0 \<and> v \<ge> 0 \<and> dx\<^sup>2+dy\<^sup>2 = 1 \<and> A > 0 \<and> B \<ge> b \<and> b > 0 \<and> \<epsilon> > 0 \<and> lw > 0 \<and> r \<noteq> 0)\<^sup>e" in fbox_diff_invI)
      apply (intro fbox_invs)
              apply (simp only: fbox_diff_inv_on)
              apply (diff_inv_on_single_ineq_intro "(0)\<^sup>e" "(1)\<^sup>e"; (force | vderiv))
             apply (rule diff_weak_on_rule, expr_simp)
    by (diff_inv_on_eq | (rule nmods_invariant[OF nmods_g_orbital_on_discrete']; expr_simp))+
      (clarsimp simp: le_fun_def)+
  apply (rule_tac C="(-c * v + a*c\<^sup>2/2 \<le> y - y0 \<and> y - y0 \<le> c * v - a*c\<^sup>2/2)\<^sup>e" in diff_cut_on_rule)
  subgoal for v0 y0
    apply (rule_tac I="(-c * v + a*c\<^sup>2/2 \<le> y - y0 \<and> y - y0 \<le> c * v - a*c\<^sup>2/2)\<^sup>e" in fbox_diff_invI)
      apply (intro fbox_invs)
       apply (simp only: fbox_diff_inv_on)
       apply (diff_inv_on_single_ineq_intro "(- v)\<^sup>e" "(v * dy)\<^sup>e"; (force | vderiv)?)
       apply (simp add: expr_simps, clarify)
       apply (rule STTT_10_arith1[of "get\<^bsub>v\<^esub> (put\<^bsub>x +\<^sub>L y +\<^sub>L v +\<^sub>L dx +\<^sub>L dy +\<^sub>L w +\<^sub>L c\<^esub> _ _)"]; assumption)
      apply (simp only: fbox_diff_inv_on)
      apply (diff_inv_on_single_ineq_intro "(v * dy)\<^sup>e" "(v)\<^sup>e" ; (force | vderiv)?)
    apply (simp add: expr_simps, clarify)
      apply (rule STTT_10_arith1[of "get\<^bsub>v\<^esub> (put\<^bsub>x +\<^sub>L y +\<^sub>L v +\<^sub>L dx +\<^sub>L dy +\<^sub>L w +\<^sub>L c\<^esub> _ _)"]; assumption)
    by (clarsimp simp: le_fun_def)+
  apply (rule_tac b="(\<bar>$y - ly\<bar> + ($v)\<^sup>2 / (2 * b) < lw)\<^sup>e" and
      a="(0 \<le> $v \<and> 0 < A \<and> b \<le> B \<and> 0 < b \<and> 0 < \<epsilon> \<and> 0 < lw \<and> $r \<noteq> 0 \<and> ($dx)\<^sup>2 + ($dy)\<^sup>2 = 1)\<^sup>e" in hoare_conj_posI)
    apply (rule diff_weak_on_rule, expr_simp)
   prefer 2 apply expr_simp
  apply (rule_tac a="(0 \<le> $v \<and> 0 < A \<and> b \<le> B \<and> 0 < b \<and> 0 < \<epsilon> \<and> 0 < lw \<and> $r \<noteq> 0 \<and> $c = 0
    \<and> v = v0 \<and> y = y0
    \<and> ($dx)\<^sup>2 + ($dy)\<^sup>2 = 1 \<and> \<bar>$y - ly\<bar> + ($v)\<^sup>2 / (2 * b) < lw)\<^sup>e" 
      and b="(\<bar>$y - ly\<bar> + ($v)\<^sup>2 / (2 * b) + (A / b + 1) * (A / 2 * \<epsilon>\<^sup>2 + \<epsilon> * $v) < lw 
    \<and> - B \<le> $a \<and> $a \<le> A \<and> $w * $r = $v)\<^sup>e"
      and c="($v = 0 \<and> $a = 0 \<and> $w = 0 \<or> - B \<le> $a \<and> $a \<le> - b)\<^sup>e" in hoare_disj_preI[rotated])
    apply (rule_tac a="(0 \<le> $v \<and> 0 < A \<and> b \<le> B \<and> 0 < b \<and> 0 < \<epsilon> \<and> 0 < lw \<and> $r \<noteq> 0 \<and> $c = 0
      \<and> v = v0 \<and> y = y0
      \<and> ($dx)\<^sup>2 + ($dy)\<^sup>2 = 1 \<and> \<bar>$y - ly\<bar> + ($v)\<^sup>2 / (2 * b) < lw)\<^sup>e" 
      and b="($v = 0 \<and> $a = 0 \<and> $w = 0)\<^sup>e"
      and c="(- B \<le> $a \<and> $a \<le> - b)\<^sup>e" in hoare_disj_preI[rotated, rotated], expr_simp)
     prefer 3 subgoal by expr_auto
  subgoal for v0 y0 (* SUBGOAL 1*)
    apply (rule_tac C="(a=0)\<^sup>e" in diff_cut_on_rule)
    subgoal
      apply (rule_tac I="(a=0)\<^sup>e" in fbox_diff_invI)
      by (diff_inv_on_eq) (clarsimp simp: le_fun_def)+
    apply (rule_tac C="(v0=0)\<^sup>e" in diff_cut_on_rule)
    subgoal
      apply (rule_tac I="(v0=0)\<^sup>e" in fbox_diff_invI)
      by (diff_inv_on_eq) (clarsimp simp: le_fun_def)+
    apply (rule_tac C="(\<bar>y0 - ly\<bar> < lw)\<^sup>e" in diff_cut_on_rule)
    subgoal
      apply (rule_tac I="(\<bar>y0 - ly\<bar> < lw)\<^sup>e" in fbox_diff_invI)
      by (diff_inv_on_ineq "(0)\<^sup>e" "(0)\<^sup>e") (clarsimp simp: le_fun_def)+
    by (rule diff_weak_on_rule) expr_auto
   prefer 2 subgoal for v0 y0 (* SUBGOAL 2*)
    apply (rule_tac C="(\<bar>y0 - ly\<bar> + (v0)\<^sup>2 / (2 * b) + (A / b + 1) * (A / 2 * \<epsilon>\<^sup>2 + \<epsilon> * v0) < lw)\<^sup>e" in diff_cut_on_rule)
    subgoal
      apply (rule_tac I="(\<bar>y0 - ly\<bar> + (v0)\<^sup>2 / (2 * b) + (A / b + 1) * (A / 2 * \<epsilon>\<^sup>2 + \<epsilon> * v0) < lw)\<^sup>e" in fbox_diff_invI)
      by (diff_inv_on_ineq "(0)\<^sup>e" "(0)\<^sup>e") (clarsimp simp: le_fun_def)+
    apply (rule_tac C="(v0 \<ge> 0 \<and> - B \<le> $a \<and> $a \<le> A)\<^sup>e" in diff_cut_on_rule)
    subgoal
      apply (rule_tac I="(v0 \<ge> 0 \<and> - B \<le> $a \<and> $a \<le> A)\<^sup>e" in fbox_diff_invI)
      apply (intro fbox_invs)
      by (diff_inv_on_ineq "(0)\<^sup>e" "(0)\<^sup>e")+ (clarsimp simp: le_fun_def)+
    apply (rule diff_weak_on_rule)
    by expr_auto (rule STTT_10_arith2[of _ \<epsilon> "get\<^bsub>v\<^esub> _"]; assumption)
  subgoal for v0 y0 (* SUBGOAL 3 *)
    apply (rule_tac C="(v0 \<ge> 0 \<and> - B \<le> $a \<and> $a \<le> - b)\<^sup>e" in diff_cut_on_rule)
    subgoal
      apply (rule_tac I="(v0 \<ge> 0 \<and> - B \<le> $a \<and> $a \<le> - b)\<^sup>e" in fbox_diff_invI)
        apply (intro fbox_invs)
      by (diff_inv_on_ineq "(0)\<^sup>e" "(0)\<^sup>e")+ (clarsimp simp: le_fun_def)+
    apply (rule_tac C="(\<bar>y0 - ly\<bar> + (v0)\<^sup>2 / (2 * b) < lw)\<^sup>e" in diff_cut_on_rule)
    subgoal
      apply (rule_tac I="(\<bar>y0 - ly\<bar> + (v0)\<^sup>2 / (2 * b) < lw)\<^sup>e" in fbox_diff_invI)
      by (diff_inv_on_ineq "(0)\<^sup>e" "(0)\<^sup>e")+ (clarsimp simp: le_fun_def)+
    apply (rule diff_weak_on_rule)
    by expr_auto (rule STTT_10_arith3[of "get\<^bsub>v\<^esub> _"]; assumption)
  done

end 


subsubsection \<open> LICS: Example 1 Continuous car accelertes forward \<close>

dataspace LICS =
  constants A::real B::real b::real m::real \<epsilon>::real
  variables x::real v::real a::real t::real

context LICS
begin

lemma local_flow_LICS: "local_flow_on [v \<leadsto> $a, x \<leadsto> $v] (x +\<^sub>L v) UNIV UNIV 
  (\<lambda>\<tau>. [x \<leadsto> $a * \<tau>\<^sup>2 / 2 + $v * \<tau> + $x, v \<leadsto> $a * \<tau> + $v])"
  apply (clarsimp simp add: local_flow_on_def)
  apply (unfold_locales; expr_simp)
   apply (rule c1_implies_local_lipschitz[of UNIV UNIV _ "(\<lambda>(t::real,c). Blinfun (\<lambda>c. ((snd c), 0)))"])
  by (auto intro!: has_derivative_Blinfun derivative_eq_intros poly_derivatives)

(* v>=0 & a>=0 -> [{x'=v, v'=a & v>=0}] v>=0 *)
lemma "(v \<ge> 0 \<and> a \<ge> 0)\<^sub>e \<le> |{x` = v, v` = a | (v \<ge> 0)}] (v \<ge> 0)"
  by (hoare_wp_auto local_flow: local_flow_LICS)

end
 

subsubsection \<open> LICS: Example 2 Single car drives forward \<close>

context LICS
begin

(* v>=0  & A>=0 & b>0
 -> [
      {
        {a:=A; ++ a:=-b;}
        {x'=v, v'=a & v>=0}
      }*@invariant(v>=0)
    ] v>=0 *)
lemma "(v \<ge> 0 \<and> A > 0 \<and> b > 0)\<^sub>e \<le>
  |LOOP 
    (
      (a ::= A \<sqinter> a ::= -b);
      {x` = v, v` = a | (v \<ge> 0)}
    )
   INV (v \<ge> 0)
  ] (v \<ge> 0)"
  by (hoare_wp_auto local_flow: local_flow_LICS)

end


subsubsection \<open> LICS: Example 3a event-triggered car drives forward \<close>

context LICS
begin

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
lemma "(v \<ge> 0 \<and> A > 0 \<and> b > 0)\<^sub>e \<le>
  |LOOP 
    (
      ( (\<questiondown>m - x \<ge> 2?; a ::= A) 
      \<sqinter> a ::= -b);
      {x` = v, v` = a | (v \<ge> 0)}
    )
   INV (v \<ge> 0)
  ] (v \<ge> 0)"
  by (hoare_wp_auto local_flow: local_flow_LICS)

end


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

context LICS
begin

lemma local_flow_LICS2: "local_flow_on [t \<leadsto> 1, v \<leadsto> $a, x \<leadsto> $v] (x +\<^sub>L v +\<^sub>L t) UNIV UNIV
  (\<lambda>\<tau>. [t \<leadsto> \<tau> + t, x \<leadsto> $a * \<tau>\<^sup>2 / 2 + $v * \<tau> + $x, v \<leadsto> $a * \<tau> + $v])"
  apply (clarsimp simp add: local_flow_on_def)
  apply (unfold_locales; expr_simp)
  by (rule c1_implies_local_lipschitz[of UNIV UNIV _ "(\<lambda>(t::real,c). Blinfun (\<lambda>c. (fst (snd c), 0)))"])
    (auto intro!: has_derivative_Blinfun derivative_eq_intros poly_derivatives)

(*v^2<=2*b*(m-x) & v>=0  & A>=0 & b>0
 -> [
      {
        {?(2*b*(m-x) >= v^2+(A+b)*(A*ep^2+2*ep*v)); a:=A; ++ a:=-b; }
        t := 0;
        {x'=v, v'=a, t'=1 & v>=0 & t<=ep}
      }*@invariant(v^2<=2*b*(m-x))
    ] x <= m *)
lemma "(v\<^sup>2 \<le> 2*b*(m-x) \<and> v\<ge>0 \<and> A \<ge> 0 \<and> b>0)\<^sub>e \<le>
  |LOOP 
    ((\<questiondown>2*b*(m-x) \<ge> v\<^sup>2+(A+b)*(A * \<epsilon>\<^sup>2+2*\<epsilon> * v)?; a ::= A) \<sqinter> a ::= - b);
    (t ::= 0);
    {x` = v, v` = a, t` = 1 | (v \<ge> 0 \<and> t \<le> \<epsilon>)}
   INV (v\<^sup>2 \<le> 2*b*(m-x))] 
  (x \<le> m)"
  apply (subst change_loopI[where I="(v\<^sup>2 \<le> 2*b*(m-x) \<and> A \<ge> 0 \<and> b > 0)\<^sup>e"])
  apply (rule hoare_loopI)
    apply (clarsimp simp add: wp fbox_g_dL_easiest[OF local_flow_LICS2] 
      unrest_ssubst var_alpha_combine  usubst usubst_eval refine_iff_implies)
  using LICSexample4a_arith[of A b "get\<^bsub>v\<^esub> _" m "get\<^bsub>x\<^esub> _" _ \<epsilon>]
     apply (force simp: field_simps)
    apply (bin_unfold, distribute, mon_simp_vars b m)
   apply (expr_simp)
  by clarsimp
    (smt (verit, ccfv_SIG) mult.commute mult_le_cancel_left zero_le_power2)

end


subsubsection \<open> LICS: Example 4b progress of time-triggered car \<close>  (*N 56 *)

context LICS
begin

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
lemma "`\<epsilon> > 0 \<and> A > 0 \<and> b > 0 
  \<longrightarrow> (\<forall>p. \<exists>M. 
  ( |(
    ((\<questiondown>(2*b*(M-x) \<ge> v\<^sup>2+(A + b)*(A*\<epsilon>\<^sup>2+2*\<epsilon>* v))?;a ::= A) \<sqinter> (a ::= -b)); t::=0;
    {x` = v, v` = a, t` = 1 | (v \<ge> 0 \<and> t \<le> \<epsilon>)}
    )\<^sup>*\<rangle>
  (x \<ge> p)))`"
  oops


end


subsubsection \<open> LICS: Example 4c relative safety of time-triggered car \<close>

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

context LICS
begin

lemma local_flow_LICS3: "local_flow_on [v \<leadsto> c, x \<leadsto> $v] (x +\<^sub>L v) UNIV UNIV 
  (\<lambda>\<tau>. [x \<leadsto> c * \<tau>\<^sup>2 / 2 + $v * \<tau> + $x, v \<leadsto> c * \<tau> + $v])"
  apply (clarsimp simp add: local_flow_on_def)
  apply (unfold_locales; expr_simp)
   apply (rule c1_implies_local_lipschitz[of UNIV UNIV _ "(\<lambda>(t::real,c). Blinfun (\<lambda>c. ((snd c), 0)))"])
  by (auto intro!: has_derivative_Blinfun derivative_eq_intros poly_derivatives)

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
lemma "`|{x` = v, v` = -b}](x\<le>m \<and> v \<ge> 0 \<and> A \<ge> 0 \<and> b > 0) 
  \<longrightarrow> |LOOP ((\<questiondown>(2*b*(m-x) \<ge> v\<^sup>2+(A + b)*(A*\<epsilon>\<^sup>2+2*\<epsilon>* v))?;a ::= A) \<sqinter> (a ::= -b)); t::=0;
  {x` = v, v` = a, t` = 1 | (v \<ge> 0 \<and> t \<le> \<epsilon>)} INV (v\<^sup>2 \<le> 2*b*(m - x))](x\<le>m)`"
  apply (clarsimp simp: wp fbox_g_dL_easiest[OF local_flow_LICS3] taut_def)
  apply (rule in_fbox_loopI)
    apply (expr_simp, frule bspec[where x=0]; clarsimp)
    apply (erule_tac x="get\<^bsub>v\<^esub> s/b" in ballE; clarsimp simp: field_simps)
    apply (expr_simp, frule bspec[where x=0]; clarsimp)
  apply (smt (verit, best) zero_le_mult_iff zero_le_power2)
  apply (hoare_wp_auto local_flow: local_flow_LICS2; frule bspec[where x=0]; clarsimp)
  using LICSexample4c_arith1[of "get\<^bsub>v\<^esub> _" b m "get\<^bsub>x\<^esub> _" _ A \<epsilon>]
  by (auto simp: field_simps)

end


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

context LICS
begin

(* v>=0 & b>0 -> ( v^2<=2*b*(m-x) <-> [{x'=v, v'=-b}]x<=m ) *)
lemma "`v \<ge> 0 \<and> b > 0 \<longrightarrow> (v\<^sup>2 \<le> 2*b*(m-x) \<longleftrightarrow> |{x` = v, v` = -b}](x\<le>m))`"
  by (clarsimp simp: taut_def wp fbox_g_dL_easiest[OF local_flow_LICS3]; expr_simp)
    (auto simp: LICSexample5_arith1 LICSexample5_arith2)

end


subsubsection \<open> LICS: Example 6 MPC Acceleration Equivalence \<close>  (*N 59 *)

lemma LICSexample6_arith1:
  assumes "0 \<le> v" "0 < b" "0 \<le> A" "0 \<le> \<epsilon>" 
    and guard: "\<forall>t\<in>{0..}. (\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> \<tau> \<le> \<epsilon>) \<longrightarrow> (\<forall>\<tau>\<in>{0..}. 
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


context LICS
begin

lemma local_flow_LICS4: "local_flow_on [t \<leadsto> 1, v \<leadsto> c, x \<leadsto> $v] (x +\<^sub>L v +\<^sub>L t) UNIV UNIV 
  (\<lambda>\<tau>. [x \<leadsto> c * \<tau>\<^sup>2 / 2 + $v * \<tau> + $x, v \<leadsto> c * \<tau> + $v, t \<leadsto> \<tau> + t])"
  apply (clarsimp simp add: local_flow_on_def)
  apply (unfold_locales; expr_simp)
   apply (rule c1_implies_local_lipschitz[of UNIV UNIV _ "(\<lambda>(t::real,c). Blinfun (\<lambda>c. (fst (snd c), 0)))"])
  by (auto intro!: has_derivative_Blinfun derivative_eq_intros poly_derivatives)

(* v>=0 & b>0 & A>=0 & ep>=0 -> (
    [t:=0; {x'=v, v'=A, t'=1 & t<=ep}][{x'=v, v'=-b}]x<=m
    <->
    2*b*(m-x) >= v^2 + (A + b)*(A*ep^2 + 2*ep*v)
   ) *)
lemma "`v \<ge> 0 \<and> b > 0 \<and> A \<ge> 0 \<and> \<epsilon> \<ge> 0 \<longrightarrow> 
    ( |t::=0; {x` = v, v` = A, t` = 1| (t \<le> \<epsilon>)}]|{x` = v, v` = -b}](x\<le>m))
    \<longleftrightarrow> 
    2*b*(m-x) \<ge> v\<^sup>2 + (A + b)*(A*\<epsilon>\<^sup>2 + 2*\<epsilon>* v)`"
  apply (clarsimp simp: wp taut_def fbox_g_dL_easiest[OF local_flow_LICS3] 
      fbox_g_dL_easiest[OF local_flow_LICS4], safe; expr_simp; clarsimp?)
  using LICSexample6_arith1[of "get\<^bsub>v\<^esub> _" b A \<epsilon> "get\<^bsub>x\<^esub> _" m]
   apply (force simp: field_simps)
  apply (frule spec[where x=0]; clarsimp)
  apply (rename_tac s t \<tau>)
  apply distribute
  apply (mon_simp_vars A \<epsilon>)
  apply (mon_simp_vars \<epsilon> b)
  sorry

end



subsubsection \<open> LICS: Example 7 Model-Predictive Control Design Car \<close>  (*N 60 *)

lemma LICSexample7_arith: "\<forall>t\<in>{0..}. v * t - b * t\<^sup>2 / 2 + x \<le> m \<Longrightarrow>
       0 \<le> A \<Longrightarrow>
       0 < b \<Longrightarrow>
       0 \<le> (t::real) \<Longrightarrow>
       \<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> b * \<tau> \<le> v \<and> \<tau> \<le> \<epsilon> \<Longrightarrow>
       0 \<le> \<tau> \<Longrightarrow> (v - b * t) * \<tau> - b * \<tau>\<^sup>2 / 2 + (v * t - b * t\<^sup>2 / 2 + x) \<le> m"
  sorry


context LICS
begin

lemma local_flow_LICS7: "local_flow_on [t \<leadsto> 1, v \<leadsto> a, x \<leadsto> $v] (x +\<^sub>L v +\<^sub>L t) UNIV UNIV 
  (\<lambda>\<tau>. [x \<leadsto> a * \<tau>\<^sup>2 / 2 + $v * \<tau> + $x, v \<leadsto> a * \<tau> + $v, t \<leadsto> \<tau> + t])"
  apply (clarsimp simp add: local_flow_on_def)
  apply (unfold_locales; expr_simp)
   apply (rule c1_implies_local_lipschitz[of UNIV UNIV _ "(\<lambda>(t::real,c). Blinfun (\<lambda>c. (fst (snd c), 0)))"])
  by (auto intro!: has_derivative_Blinfun derivative_eq_intros poly_derivatives)

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
lemma "`(( |{x` = v, v` = -b}](x \<le> m))
   \<and> v \<ge> 0
   \<and> A \<ge> 0
   \<and> b > 0)
\<longrightarrow>
  ( | LOOP (
    ((\<questiondown> |t::=0; {x `= v, v `= A, t `= 1 | (v \<ge> 0 \<and> t \<le> \<epsilon>)}] |{x `= v, v `= -b}] (x \<le> m)?; 
        a ::= A) \<sqinter> a ::= -b);
    t ::= 0;
    {x `= v, v `= a, t `= 1 | (v \<ge> 0 \<and> t \<le> \<epsilon>)}
    ) INV ( |{x `= v, v `= -b}](x \<le> m))
  ] (x \<le> m))`"
  apply (subst impl_eq_leq)
  apply (subst change_loopI[where I="( |{x `= v, v `= -b}](x \<le> m) \<and> A \<ge> 0 \<and> b > 0)\<^sup>e"])
  apply (rule fbox_loopI)
    apply (clarsimp)
   apply (clarsimp simp: fbox_g_dL_easiest[OF local_flow_LICS3] wp)
   apply (erule_tac x=0 in ballE, expr_simp, force)
  apply (clarsimp simp: fbox_g_dL_easiest[OF local_flow_LICS7] 
      fbox_g_dL_easiest[OF local_flow_LICS3] wp fbox_g_dL_easiest[OF local_flow_LICS4],
      safe; expr_simp?, clarsimp?)
  using LICSexample7_arith[of "get\<^bsub>v\<^esub> _" b] by auto

end


subsection \<open>Advanced\<close>


subsubsection \<open> ETCS: Essentials \<close>

lemma ETCS_arith1: 
  assumes "0 < b" "0 \<le> A" "0 \<le> v" "0 \<le> (t::real)"
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

lemma ETCS_Prop1_arith1:
  assumes "0 \<le> v" "0 \<le> \<delta>" "0 < (b::real)" "x \<le> m"
    and "\<forall>t\<in>{0..}. (\<forall>\<tau>\<in>{0--t}. b * \<tau> \<le> v) \<longrightarrow>
       m \<le> v * t - b * t\<^sup>2 / 2 + x \<longrightarrow> v - b * t \<le> \<delta>"
  shows "v\<^sup>2 - \<delta>\<^sup>2 \<le> 2 * b * (m - x)"
    (* solve arithmetic *)
  sorry

lemma ETCS_Prop1_arith2:
  assumes "0 \<le> v" "0 \<le> \<delta>" "0 < b" "x \<le> m" "0 \<le> (t::real)"
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

dataspace ETCS =
  constants 
    \<epsilon> :: real \<comment> \<open> control cycle duration upper bound \<close>
    b :: real \<comment> \<open> braking force \<close>
    A :: real \<comment> \<open> maximum acceleration \<close>
    m :: real \<comment> \<open> end of movement authority (train must not drive past m) \<close>
  variables
    t :: real
    z :: real
    v :: real
    a :: real
context ETCS
begin

(* Real stopDist(Real v) = v^2/(2*b) *)
abbreviation "stopDist w \<equiv> w\<^sup>2/(2*b)"

(* Real accCompensation(Real v) = (((A/b) + 1)*((A/2)*ep^2 + ep*v)) *)
abbreviation "accCompensation w \<equiv> ((A/b) + 1) * ((A/2)*\<epsilon>\<^sup>2 + \<epsilon> * w)"

(* Real SB(Real v) = stopDist(v) + accCompensation(v) *)
abbreviation "SB w \<equiv> stopDist w + accCompensation w"

(* initial(Real m, Real z, Real v) <-> (v >= 0 & m-z >= stopDist(v) & b>0 & A>=0 & ep>=0) *)
abbreviation "initial \<equiv> (v \<ge> 0 \<and> (m - z) \<ge> stopDist v \<and> b > 0 \<and> A \<ge> 0 \<and> \<epsilon> \<ge> 0)\<^sub>e"
\<comment> \<open> initial states \<close>

(* Bool safe(Real m, Real z, Real v, Real d) <-> (z >= m -> v <= d) *)
abbreviation "safe \<mu> \<zeta> w \<delta> \<equiv> \<zeta> \<ge> \<mu> \<longrightarrow> w \<le> \<delta>" 

(* Bool loopInv(Real m, Real z, Real v) <-> (v >= 0 & m-z >= stopDist(v) *)
abbreviation "loopInv \<equiv> (v \<ge> 0 \<and> m - z \<ge> stopDist v)\<^sub>e"
\<comment> \<open> always maintain sufficient stopping distance \<close>

(* HP ctrl ::= {?m - z <= SB(v); a := -b; ++ ?m - z >= SB(v); a :=  A; *)
abbreviation "ctrl \<equiv> (\<questiondown>m - z \<le> SB(v)?; a ::= -b) \<sqinter> (\<questiondown>m - z \<ge> SB(v)?; a ::= A)"
\<comment> \<open> train controller \<close>


subsubsection \<open> ETCS: Proposition 1 (Controllability) \<close> (*N 62 *)

(* HP drive ::= {t := 0;{z'=v, v'=a, t'=1  & v >= 0 & t <= ep} *)
abbreviation "drive \<equiv> (t ::= 0);{z` = v, v` = a, t` = 1 | (v \<ge> 0 \<and> t \<le> \<epsilon>)}"

lemma local_flow_LICS1: "local_flow_on [t \<leadsto> 1, v \<leadsto> $a, z \<leadsto> $v] (z +\<^sub>L v +\<^sub>L t) UNIV UNIV
  (\<lambda>\<tau>. [t \<leadsto> \<tau> + t, z \<leadsto> $a * \<tau>\<^sup>2 / 2 + $v * \<tau> + $z, v \<leadsto> $a * \<tau> + $v])"
  apply (clarsimp simp add: local_flow_on_def)
  apply (unfold_locales; expr_simp)
  by (rule c1_implies_local_lipschitz[of UNIV UNIV _ "(\<lambda>(t::real,c). Blinfun (\<lambda>c. (fst (snd c), 0)))"])
    (auto intro!: has_derivative_Blinfun derivative_eq_intros poly_derivatives)

(* initial(m, z, v)  ->
    [
      {
        ctrl;
        drive;
      }*@invariant(loopInv(m, z, v))
    ] (z <= m) *)
lemma "initial \<le> |LOOP ctrl;drive INV @loopInv] (z \<le> m)"
  apply (subst change_loopI[where I="(@loopInv \<and> b > 0 \<and> A \<ge> 0 \<and> \<epsilon> \<ge> 0)\<^sup>e"])
  apply (rule hoare_loopI)
  using ETCS_arith1[of b A "get\<^bsub>v\<^esub> _" _ \<epsilon> m "get\<^bsub>z\<^esub> _"]
  by (auto simp: unrest_ssubst var_alpha_combine wp usubst usubst_eval 
      fbox_g_dL_easiest[OF local_flow_LICS1] field_simps taut_def)
    (smt (verit, best) mult_left_le_imp_le zero_le_square)

(* Bool Assumptions(Real v, Real d) <-> ( v>=0 & d>=0 & b>0 ) *)
abbreviation "Assumptions d \<equiv> (v \<ge> 0 \<and> d \<ge> 0 \<and> b > 0)\<^sub>e"

lemma local_flow_LICS2: "local_flow_on [v \<leadsto> -b, z \<leadsto> $v] (z +\<^sub>L v) UNIV UNIV
  (\<lambda>\<tau>. [z \<leadsto> -b * \<tau>\<^sup>2 / 2 + $v * \<tau> + $z, v \<leadsto> -b * \<tau> + $v])"
  apply (clarsimp simp add: local_flow_on_def)
  apply (unfold_locales; expr_simp)
  by (rule c1_implies_local_lipschitz[of UNIV UNIV _ "(\<lambda>(t::real,c). Blinfun (\<lambda>c. ((snd c), 0)))"])
    (auto intro!: has_derivative_Blinfun derivative_eq_intros poly_derivatives)

(* Assumptions(v, d) & z<=m
  ->
  ( [ {z'=v, v'=-b & v>=0 } ](z>=m -> v<=d)
    <->
    v^2-d^2 <= 2*b*(m-z)
  ) *)
lemma "`@(Assumptions d) \<and> z \<le> m \<longrightarrow>
  ( |{z` = v, v` = -b | (v \<ge> 0)}] (z \<ge> m \<longrightarrow> v \<le> d)
  \<longleftrightarrow>
  v\<^sup>2 -d\<^sup>2 \<le> 2*b*(m-z))`"
  apply (clarsimp simp: wp taut_def fbox_g_dL_easiest[OF local_flow_LICS2], safe; expr_simp)
  using ETCS_Prop1_arith1 apply (force simp: closed_segment_eq_real_ivl)
  using ETCS_Prop1_arith2 by (force simp: closed_segment_eq_real_ivl)


subsubsection \<open> ETCS: Proposition 4 (Reactivity) \<close> (*N 63 *)

(* Bool Controllable(Real m, Real z, Real v, Real d) <-> (v^2-d^2 <= 2*b*(m-z) & Assumptions(v, d)) *)
abbreviation "Controllable d \<equiv> (v\<^sup>2 -d\<^sup>2 \<le> 2*b*(m-z) \<and> @(Assumptions d))\<^sub>e"



(*
em = 0 & d >= 0 & b > 0 & ep > 0 & A > 0 & v>=0
  -> ((\forall m \forall z (m-z>= sb & Controllable(m,z,v,d) -> [ a:=A; drive; ]Controllable(m,z,v,d)) )
      <->
      sb >= (v^2 - d^2) /(2*b) + (A/b + 1) * (A/2 * ep^2 + ep*v)
     )
*)
lemma "`em = 0 \<and> d \<ge> 0 \<and> b > 0 \<and> \<epsilon> > 0 \<and> A > 0 \<and> v \<ge> 0 
  \<longrightarrow> ((\<forall>m.\<forall>z. m - z \<ge> sb \<and> @(Controllable d) \<longrightarrow> |a ::= A; drive]@(Controllable d)) 
    \<longleftrightarrow> (sb \<ge> (v\<^sup>2 - d\<^sup>2)/(2*b) + (A/b + 1) * (A/2 * \<epsilon>\<^sup>2 + \<epsilon> * v)))`"
  apply (simp only: taut_def)
  apply (hol_clarsimp simp: wp taut_def fbox_g_dL_easiest[OF local_flow_LICS1]; expr_simp)
   apply (safe; clarsimp simp: dlo_simps)
      apply (metis diff_zero)
  oops

end


end