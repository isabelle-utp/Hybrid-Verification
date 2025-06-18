theory Lics
  imports "Hybrid-Verification.Hybrid_Verification"

begin

subsubsection \<open> 52. LICS: Example 1 Continuous car accelertes forward \<close>

dataspace LICS =
  constants A::real B::real b::real m::real \<epsilon>::real
  variables x::real v::real a::real t::real

context LICS
begin

lemma local_flow_LICS: "local_flow_on [v \<leadsto> $a, x \<leadsto> $v] (x +\<^sub>L v) UNIV UNIV 
  (\<lambda>\<tau>. [x \<leadsto> $a * \<tau>\<^sup>2 / 2 + $v * \<tau> + $x, v \<leadsto> $a * \<tau> + $v])"
  by local_flow_on_auto

(* v>=0 & a>=0 -> [{x'=v, v'=a & v>=0}] v>=0 *)
lemma "(v \<ge> 0 \<and> a \<ge> 0)\<^sub>e \<le> |{x` = v, v` = a | (v \<ge> 0)}] (v \<ge> 0)"
  by (wlp_full local_flow: local_flow_LICS)

end
 

subsubsection \<open> 53. LICS: Example 2 Single car drives forward \<close>

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
  by (wlp_full local_flow: local_flow_LICS)

end


subsubsection \<open> 54. LICS: Example 3a event-triggered car drives forward \<close>

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
  by (wlp_full local_flow: local_flow_LICS)

end


subsubsection \<open> 55. LICS: Example 4a safe stopping of time-triggered car \<close>

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
  by local_flow_on_auto

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
    apply (clarsimp simp add: wlp fbox_g_dL_easiest[OF local_flow_LICS2] 
      unrest_ssubst var_alpha_combine  usubst usubst_eval refine_iff_implies)
    apply expr_simp
  using LICSexample4a_arith[of A b "get\<^bsub>v\<^esub> _" m "get\<^bsub>x\<^esub> _" _ \<epsilon>]
  by powers_simp
    (smt (verit, ccfv_SIG) SEXP_def power2_less_eq_zero_iff 
      sum_power2_eq_zero_iff taut_def zero_compare_simps(4))

end


subsubsection \<open> 56. LICS: Example 4b progress of time-triggered car \<close>  (*N 56 *)

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
    ((\<questiondown>((2*b*(M-x)) \<ge> (v\<^sup>2+(A + b)*(A*\<epsilon>\<^sup>2+2*\<epsilon>* v)))?;a ::= A) \<sqinter> (a ::= -b)); t::=0;
    {x` = v, v` = a, t` = 1 | (v \<ge> 0 \<and> t \<le> \<epsilon>)}
    )\<^sup>*\<rangle>
  (x \<ge> p)))`"
  apply (clarsimp simp: taut_def)
  apply (rule_tac x="M" in exI)
  apply (rule_tac P="\<lambda>r. ($x \<ge> p)\<^sup>e" in fdia_kstar_real_variantI)
    prefer 2
  apply (clarsimp simp: taut_def fdia_skip fdia_abort fdia_test fdia_assign 
      fdia_nondet_assign fdia_choice fdia_kcomp
      fdia_g_ode_frame_flow[OF local_flow_LICS2])
    apply (hol_clarsimp)
  prefer 2 using indeps apply expr_simp
  thm taut_def fdia_skip fdia_abort fdia_test fdia_assign 
      fdia_nondet_assign fdia_choice fdia_kcomp
  thm fdia_g_ode_frame_flow[OF local_flow_LICS2]
  oops (* have not found the witness M *)

(* 
x’=v,v’=a,t’=1 
\<Longrightarrow> v t = a * t + v\<^sub>0 and x t = a * t\<^sup>2 / 2 + v\<^sub>0 * t + x\<^sub>0 and t \<tau> = \<tau> + t\<^sub>0
\<Longrightarrow> (x t - x\<^sub>0) = (v t - v\<^sub>0)\<^sup>2/(2 * a) + v\<^sub>0 * (v t - v\<^sub>0)/a
\<Longrightarrow> 2 * a * (x t - x\<^sub>0) = (v t - v\<^sub>0)\<^sup>2 + 2 * v\<^sub>0 * (v t - v\<^sub>0)
\<Longrightarrow> 2 * a * (x t - x\<^sub>0) = (v t)\<^sup>2 - 2 * v\<^sub>0 * (v t) + v\<^sub>0\<^sup>2 + 2 * v\<^sub>0 * (v t) - 2 * v\<^sub>0\<^sup>2
\<Longrightarrow> 2 * a * (x t - x\<^sub>0) = (v t)\<^sup>2 - v\<^sub>0\<^sup>2

a = - b \<Longrightarrow> p \<le> - b * \<epsilon>\<^sup>2 / 2 + v\<^sub>0 * \<epsilon> + x\<^sub>0 and 
a = A \<Longrightarrow> v\<^sub>0' \<le> v\<^sub>0 \<le> A * \<epsilon> + v\<^sub>0' and  x\<^sub>0' \<le> x\<^sub>0 \<le> A * \<epsilon>\<^sup>2 / 2 + v\<^sub>0 * \<epsilon> + x0'
  \<Longrightarrow> 0 \<le> v\<^sub>0 - v\<^sub>0' \<le> A * \<epsilon> and  0 \<le> x\<^sub>0 - x\<^sub>0' \<le> A * \<epsilon>\<^sup>2 / 2 + v\<^sub>0 * \<epsilon> 
  \<Longrightarrow> 0 \<le> v\<^sub>0 - v\<^sub>0' \<le> A * \<epsilon> and  0 \<le> 2 * (x\<^sub>0 - x\<^sub>0') \<le> A * \<epsilon>\<^sup>2 + 2 * v\<^sub>0 * \<epsilon> 
*)

end


subsubsection \<open> 57. LICS: Example 4c relative safety of time-triggered car \<close>

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
  by local_flow_on_auto

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
lemma "`|{x` = v, v` = -b}] (x\<le>m \<and> v \<ge> 0 \<and> A \<ge> 0 \<and> b > 0) 
  \<longrightarrow> |LOOP ((\<questiondown>(2*b*(m-x) \<ge> v\<^sup>2+(A + b)*(A*\<epsilon>\<^sup>2+2*\<epsilon>* v))?;a ::= A) \<sqinter> (a ::= -b)); t::=0;
  {x` = v, v` = a, t` = 1 | (v \<ge> 0 \<and> t \<le> \<epsilon>)} INV (v\<^sup>2 \<le> 2*b*(m - x))] (x\<le>m)`"
  apply (clarsimp simp: wlp fbox_g_dL_easiest[OF local_flow_LICS3] taut_def)
  apply (rule in_fbox_loopI)
    apply (expr_simp, frule bspec[where x=0]; clarsimp)
    apply (erule_tac x="get\<^bsub>v\<^esub> s/b" in ballE; clarsimp simp: field_simps)
    apply (expr_simp, frule bspec[where x=0]; clarsimp)
  apply (smt (verit, best) zero_le_mult_iff zero_le_power2)
  apply (hoare_wp_auto local_flow: local_flow_LICS2; frule bspec[where x=0]; clarsimp)
  using LICSexample4c_arith1[of "get\<^bsub>v\<^esub> _" b m "get\<^bsub>x\<^esub> _" _ A \<epsilon>]
  by (auto simp: field_simps)

end


subsubsection \<open> 58. LICS: Example 5 Controllability Equivalence \<close>

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
lemma "`v \<ge> 0 \<and> b > 0 \<longrightarrow> (v\<^sup>2 \<le> 2*b*(m-x) \<longleftrightarrow> |{x` = v, v` = -b}] (x\<le>m))`"
  by (clarsimp simp: taut_def wlp fbox_g_dL_easiest[OF local_flow_LICS3]; expr_simp)
    (auto simp: LICSexample5_arith1 LICSexample5_arith2)

end


subsubsection \<open> 59. LICS: Example 6 MPC Acceleration Equivalence \<close>  (*N 59 *)

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
  by local_flow_on_auto

(* v>=0 & b>0 & A>=0 & ep>=0 -> (
    [t:=0; {x'=v, v'=A, t'=1 & t<=ep}][{x'=v, v'=-b}]x<=m
    <->
    2*b*(m-x) >= v^2 + (A + b)*(A*ep^2 + 2*ep*v)
   ) *)
lemma "`v \<ge> 0 \<and> b > 0 \<and> A \<ge> 0 \<and> \<epsilon> \<ge> 0 \<longrightarrow> 
    ( |t::=0; {x` = v, v` = A, t` = 1| (t \<le> \<epsilon>)}]|{x` = v, v` = -b}] (x\<le>m))
    \<longleftrightarrow> 
    2*b*(m-x) \<ge> v\<^sup>2 + (A + b)*(A*\<epsilon>\<^sup>2 + 2*\<epsilon>* v)`"
  apply (clarsimp simp: wlp taut_def fbox_g_dL_easiest[OF local_flow_LICS3] 
      fbox_g_dL_easiest[OF local_flow_LICS4], safe; expr_simp; clarsimp?)
  using LICSexample6_arith1[of "get\<^bsub>v\<^esub> _" b A \<epsilon> "get\<^bsub>x\<^esub> _" m]
   apply (force simp: field_simps)
  apply (frule spec[where x=0]; clarsimp)
  apply (rename_tac s t \<tau>)
  apply powers_simp
  sorry (* verified with the help of a CAS *)

end



subsubsection \<open> 60. LICS: Example 7 Model-Predictive Control Design Car \<close>  (*N 60 *)

lemma LICSexample7_arith: "\<forall>t\<ge>0. v * t - b * t\<^sup>2 / 2 + x \<le> m \<Longrightarrow>
       0 \<le> A \<Longrightarrow>
       0 < b \<Longrightarrow>
       0 \<le> (t::real) \<Longrightarrow>
       \<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> b * \<tau> \<le> v \<and> \<tau> \<le> \<epsilon> \<Longrightarrow>
       0 \<le> \<tau> \<Longrightarrow> (v - b * t) * \<tau> - b * \<tau>\<^sup>2 / 2 + (v * t - b * t\<^sup>2 / 2 + x) \<le> m"
  sorry (* verified with the help of a CAS *)


context LICS
begin

lemma local_flow_LICS7: "local_flow_on [t \<leadsto> 1, v \<leadsto> a, x \<leadsto> $v] (x +\<^sub>L v +\<^sub>L t) UNIV UNIV 
  (\<lambda>\<tau>. [x \<leadsto> a * \<tau>\<^sup>2 / 2 + $v * \<tau> + $x, v \<leadsto> a * \<tau> + $v, t \<leadsto> \<tau> + t])"
  by local_flow_on_auto

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
lemma "`(( |{x` = v, v` = -b}] (x \<le> m))
   \<and> v \<ge> 0
   \<and> A \<ge> 0
   \<and> b > 0)
\<longrightarrow>
  ( | LOOP (
    ((\<questiondown> |t::=0; {x `= v, v `= A, t `= 1 | (v \<ge> 0 \<and> t \<le> \<epsilon>)}] |{x `= v, v `= -b}] (x \<le> m)?; 
        a ::= A) \<sqinter> a ::= -b);
    t ::= 0;
    {x `= v, v `= a, t `= 1 | (v \<ge> 0 \<and> t \<le> \<epsilon>)}
    ) INV ( |{x `= v, v `= -b}] (x \<le> m))
  ] (x \<le> m))`"
  apply (subst impl_eq_leq)
  apply (subst change_loopI[where I="( |{x `= v, v `= -b}] (x \<le> m) \<and> A \<ge> 0 \<and> b > 0)\<^sup>e"])
  apply (rule fbox_loopI)
    apply (clarsimp)
  apply (wlp_flow local_flow: local_flow_LICS3, clarsimp simp: le_fun_def)
   apply (erule_tac x=0 in allE, expr_simp)
  apply (wlp_simp simp: fbox_solve[OF local_flow_LICS7] fbox_solve[OF local_flow_LICS4] 
      fbox_solve[OF local_flow_LICS3], safe; expr_simp?, clarsimp?)
  using LICSexample7_arith[of "get\<^bsub>v\<^esub> _" b]
  by auto

end

end
