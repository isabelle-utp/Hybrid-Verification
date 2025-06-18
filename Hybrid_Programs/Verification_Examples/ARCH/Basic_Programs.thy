theory Basic_Programs
  imports "Hybrid-Verification.Hybrid_Verification"
begin


subsection \<open> Basic \<close>

dataspace basic_programs = 
  variables 
    w :: real
    x :: real
    y :: real
    z :: real

context basic_programs
begin


subsubsection \<open> 1. Basic assignment \<close> 

(* x>=0 -> [x:=x+1;]x>=1 *)
lemma "(x \<ge> 0)\<^sub>e \<le> |x ::= x + 1] (x \<ge> 1)"
  by wlp_simp


subsubsection \<open> 2. Overwrite assignment on some branches \<close>

(* x>=0 -> [x:=x+1;][x:=x+1; ++ y:=x+1;]x>=1 *)
lemma "(x \<ge> 0)\<^sub>e \<le> |x ::= x + 1] |x ::= x + 1 \<sqinter> y ::= x + 1] (x \<ge> 1)"
  unfolding fbox_kcomp[symmetric]
  by wlp_simp


subsubsection \<open> 3. Overwrite assignment in loop \<close>

(* x>=0 -> [x:=x+1;][{x:=x+1;}*@invariant(x>=1)]x>=1 *)
lemma "(x \<ge> 0)\<^sub>e \<le> |x ::= x + 1] |LOOP x ::= x + 1 INV (x \<ge> 1)] (x \<ge> 1)"
  unfolding fbox_kcomp[symmetric]
  by wlp_simp


subsubsection \<open> 4. Overwrite assignment in ODE \<close>

(* using invariants *)
(* x>=0 -> [x:=x+1;][{x'=2}]x>=1 *)
lemma "(x \<ge> 0)\<^sub>e \<le> |x ::= x + 1] |{x` = 2}] (x \<ge> 1)"
  unfolding fbox_kcomp[symmetric]
  apply symbolic_exec
  apply postcondition_invariant
  by dInduct 
    expr_simp

(* using the solution *)
(* x>=0 -> [x:=x+1;][{x'=2}]x>=1 *)
lemma "(x \<ge> 0)\<^sub>e \<le> |x ::= x + 1] |{x` = 2}] (x \<ge> 1)"
  by (wlp_solve "\<lambda>t. [x \<leadsto> 2 * t + x]")


subsubsection \<open> 5. Overwrite with nondeterministic assignment \<close>

(* x>=0 -> [x:=x+1;][x:=*; ?x>=1;]x>=1 *)
lemma "H{x \<ge> 0} x ::= x + 1 ; x ::= ? ; \<questiondown>x\<ge>1? {x \<ge> 1}"
  by wlp_simp


subsubsection \<open> 6. Tests and universal quantification \<close>

(* x>=0 -> [x:=x+1;][?x>=2; x:=x-1; ++ ?\forall x (x>=1 -> y>=1); x:=y;]x>=1 *)
lemma "(x \<ge> 0)\<^sub>e \<le> |x ::=x+1] |(\<questiondown>x>=2?; x::=x-1) \<sqinter> (\<questiondown>\<forall>x::real. x \<ge> 1 \<longrightarrow> y \<ge> 1?; x::=y)] (x\<ge>1)"
  by wlp_full
    expr_auto


subsubsection \<open> 7. Overwrite assignment several times \<close>

lemma [local_flow]: "local_flow_on [y \<leadsto> 2] y UNIV UNIV (\<lambda>\<tau>. [y \<leadsto> 2 * \<tau> + y])"
  by local_flow_on_auto

(* using the solution *)
(* x>=0 & y>=1 -> [x:=x+1;][{x:=x+1;}*@invariant(x>=1) ++ y:=x+1;][{y'=2}][x:=y;]x>=1 *)
lemma "(x \<ge> 0 \<and> y \<ge>1)\<^sub>e \<le> 
  |x ::= x + 1]|LOOP x ::= x + 1 INV (x \<ge> 1) \<sqinter> y ::= x + 1] |{y` = 2}] |x ::= y] 
  (x \<ge> 1)"
  unfolding fbox_kcomp[symmetric]
  apply (subst change_loopI[where I="(1 \<le> x \<and> 1 \<le> y)\<^sub>e"])
  apply symbolic_exec
  by (sequence "1 \<le> x \<and> 1 \<le> y")
    (wlp_full local_flow: local_flow )+

(* using invariants *)
(* x>=0 & y>=1 -> [x:=x+1;][{x:=x+1;}*@invariant(x>=1) ++ y:=x+1;][{y'=2}][x:=y;]x>=1 *)
lemma "(x \<ge> 0 \<and> y \<ge>1)\<^sub>e \<le> 
  |x ::= x + 1]|LOOP x ::= x + 1 INV (x \<ge> 1) \<sqinter> y ::= x + 1] |{y` = 2}] |x ::= y] 
  (x \<ge> 1)"
  unfolding fbox_kcomp[symmetric]
  apply (subst change_loopI[where I="(1 \<le> x \<and> 1 \<le> y)\<^sub>e"])
  apply symbolic_exec
   apply (sequence "1 \<le> x \<and> 1 \<le> y")
    apply wlp_simp
   apply (sequence "1 \<le> x \<and> 1 \<le> y")
    apply dInduct_mega
   apply wlp_simp
  apply subst_eval
  apply postcondition_invariant
   apply dInduct
  by expr_simp


subsubsection \<open> 8. Potentially overwrite dynamics \<close>

(* using the solution *)
(* x>0 & y>0 -> [{x'=5}][{x:=x+3;}*@invariant(x>0) ++ y:=x;](x>0&y>0) *)
lemma "(x > 0 \<and> y > 0)\<^sub>e \<le> |{x` = 5}]|LOOP x::=x+3 INV (x > 0) \<sqinter> y::=x] (x \<ge> 0 \<and> y \<ge> 0)"
  unfolding fbox_kcomp[symmetric]
  apply (subst change_loopI[where I="(0 < $x \<and> 0 < $y)\<^sup>e"])
  apply (sequence "x > 0 \<and> y > 0")
  by (wlp_solve "\<lambda>t. [x \<leadsto> 5 * t + x]")
    (choice; wlp_simp)

(* using invariants *)
(* x>0 & y>0 -> [{x'=5}][{x:=x+3;}*@invariant(x>0) ++ y:=x;](x>0&y>0) *)
lemma "(x > 0 \<and> y > 0)\<^sub>e \<le> |{x` = 5}]|LOOP x::=x+3 INV (x > 0) \<sqinter> y::=x] (x \<ge> 0 \<and> y \<ge> 0)"
  unfolding fbox_kcomp[symmetric]
  apply (subst change_loopI[where I="(0 < $x \<and> 0 < $y)\<^sup>e"])
  apply (sequence "x > 0 \<and> y > 0")
  by dInduct
    (choice; wlp_simp)


subsubsection \<open> 9. Potentially overwrite exponential decay \<close>

(* proof with solutions *)
(* x>0 & y>0 -> [{x'=-x}][{x:=x+3;}*@invariant(x>0) ++ y:=x;](x>0&y>0) *)
lemma "(x > 0 \<and> y > 0)\<^sub>e \<le> |{x` = -x}]|LOOP x ::= x+3 INV (x > 0) \<sqinter> y::=x] (x > 0 \<and> y > 0)"
  unfolding fbox_kcomp[symmetric]
  apply (subst change_loopI[where I="(0 < $x \<and> 0 < $y)\<^sup>e"])
  apply (sequence "0 < x \<and> 0 < y")
  by (wlp_solve "\<lambda>t. [x \<leadsto> x * exp (- t)]")
    (choice; wlp_simp)

lemma exp_ghost_arith: "0 < (a::real) \<longleftrightarrow> (\<exists>b. a * b\<^sup>2 = 1)"
  by (intro iffI exI[where x="1/(sqrt a)"]; clarsimp simp: field_simps)
    (metis less_numeral_extra(1) mult_less_0_iff not_one_less_zero zero_less_mult_iff)

(* proof with ghosts *)
(* x>0 & y>0 -> [{x'=-x}][{x:=x+3;}*@invariant(x>0) ++ y:=x;](x>0&y>0) *)
lemma "(x > 0 \<and> y > 0)\<^sub>e \<le> |{x` = -x}]|LOOP x ::= x+3 INV (x > 0) \<sqinter> y::=x] (x > 0 \<and> y > 0)"
  unfolding fbox_kcomp[symmetric]
  apply (subst change_loopI[where I="(0 < $x \<and> 0 < $y)\<^sup>e"])
  apply (sequence "0 < x \<and> 0 < y")
   apply (dGhost "z" "x*z\<^sup>2 = 1 \<and> y > 0" "1/2")
    apply dInduct_auto
   apply (expr_auto add: exp_ghost_arith)
  by (choice; wlp_simp)

end (* basic_programs *)

end