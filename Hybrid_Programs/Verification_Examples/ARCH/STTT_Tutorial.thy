theory STTT_Tutorial
  imports "Hybrid-Verification.Hybrid_Verification"
begin


subsubsection \<open> 40. STTT Tutorial: Example 1 \<close>

dataspace STTT =
  constants A::real B::real S::real V::real \<epsilon>::real
  variables x::real v::real a::real c::real

context STTT
begin

lemma "(v \<ge> 0 \<and> A > 0)\<^sub>e \<le> |{x` = v, v` = A}] (v \<ge> 0)"
  by (wlp_solve "\<lambda>t. [x \<leadsto> A * t\<^sup>2 / 2 + $v * t + $x, v \<leadsto> A * t + $v]")

lemma "(v \<ge> 0 \<and> A > 0)\<^sub>e \<le> |{x` = v, v` = A}] (v \<ge> 0)"
  apply (rule diff_cut_on_rule[where C="(0 \<le> A)\<^sup>e"])
   apply (rule hoare_invI[where I="(0 \<le> A)\<^sup>e"])
    apply (diff_inv_on_ineq "(0)\<^sup>e" "(0)\<^sup>e")
    apply vderiv
     apply (expr_simp add: le_fun_def)
  apply (diff_cut_ineq "(0 \<le> v)\<^sup>e" "(0)\<^sup>e" "(A)\<^sup>e")
  by (rule diff_weak_on_rule, expr_auto)

end


subsubsection \<open> 41. STTT Tutorial: Example 2 \<close>

context STTT
begin

lemma local_flow_STTT: "local_flow_on [v \<leadsto> $a, x \<leadsto> $v] (x +\<^sub>L v) UNIV UNIV 
  (\<lambda>t. [x \<leadsto> $a * t\<^sup>2 / 2 + $v * t + $x, v \<leadsto> $a * t + $v])"
  by local_flow_on_auto

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
  by (wlp_full local_flow: local_flow_STTT)

end


subsubsection \<open> 42. STTT Tutorial: Example 3a \<close> (* 37 *)

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
  apply (wlp_flow local_flow: local_flow_STTT; expr_simp)
  apply (expr_auto add: refine_iff_implies STTexample3a_arith)
  by (smt (verit, ccfv_threshold) divide_eq_0_iff divide_pos_pos 
      zero_less_power zero_power2)

end


subsubsection \<open> 43. STTT Tutorial: Example 4a \<close>

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
  by (wlp_full local_flow: local_flow_STTT)

end


subsubsection \<open> 44. STTT Tutorial: Example 4b \<close>

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
  by (wlp_full local_flow: local_flow_STTT)

end
 

subsubsection \<open> 45. STTT Tutorial: Example 4c \<close>

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
  by (wlp_full local_flow: local_flow_STTT)
    expr_auto

end


subsubsection \<open> 46. STTT Tutorial: Example 5 \<close>

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
  by local_flow_on_auto

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
  by (wlp_full local_flow: local_flow_STTT2)
    (smt (verit) divide_nonneg_nonneg zero_le_power)

end


subsubsection \<open> 47. STTT Tutorial: Example 6 \<close>

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
  apply (intro_loops)
    apply (hoare_wp_simp local_flow: local_flow_STTT2; expr_simp)
  prefer 3 subgoal by expr_simp (smt (verit, best) divide_eq_0_iff divide_pos_pos zero_less_power zero_power2)
   prefer 2 subgoal by expr_simp
  apply (expr_simp, clarsimp, intro conjI; clarsimp simp: STTexample3a_arith STTexample6_arith)
  by (rule STTexample6_arith[of A B \<epsilon> "get\<^bsub>v\<^esub> _" _ _ "get\<^bsub>x\<^esub> _" S])
    (auto simp: field_simps)

end

subsubsection \<open> 48. STTT Tutorial: Example 7 \<close>

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


subsubsection \<open> 49. STTT Tutorial: Example 9a \<close>

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
   apply (rule hoare_invI[where I="(c > 0 \<and> Kp = 2 \<and> Kd = 3)\<^sup>e"])
    apply (simp only: expr_defs hoare_diff_inv_on fbox_diff_inv_on)
     apply (intro diff_inv_on_raw_conjI; (diff_inv_on_ineq "(0)\<^sup>e" "(0)\<^sup>e" | diff_inv_on_eq))
     apply (expr_simp add: le_fun_def)
       apply expr_simp
   apply (rule hoare_invI[where I="((5/4)*(x-xr)\<^sup>2 + (x-xr)* v/2 + v\<^sup>2/4 < c)\<^sup>e"])
  prefer 2 apply (expr_simp add: le_fun_def)
   apply (expr_simp add: hoare_diff_inv_on fbox_diff_inv_on)
  apply (diff_inv_on_single_ineq_intro "(10 *(x-xr) * v/4 + v\<^sup>2/2 + (x-xr)*(-Kp * (x-xr) - Kd * v)/2 
  + (v/2) * (-Kp * (x-xr) - Kd * v))\<^sup>e" "(0)\<^sup>e"; 
      expr_simp add: le_fun_def STTexample9a_arith)
  apply (metis indeps(1) lens_plus_def plus_vwb_lens vwbs(1) vwbs(2))
  by (intro vderiv_intros; (rule vderiv_intros)?; force?)
    (auto simp: field_simps)

end


subsubsection \<open> 50. STTT Tutorial: Example 9b \<close> (*N 50 *)

lemma STTT_9b_arith1:
  assumes "0 \<le> (v::real)" and "xm \<le> x" and "xr * 2 = xm + S" 
    and "5 * (x - xr)\<^sup>2 / 4 + (x - xr) * v / 2 + v\<^sup>2 / 4 < ((S - xm) / 2)\<^sup>2" 
  shows "x \<le> S"
  using assms
  apply powers_simp
  sorry (* verified with the help of a CAS *)

dataspace STTT_9b =
  constants S::real Kp::real Kd::real
  variables x::real v::real xm::real xr::real

context STTT_9b
begin

lemma "Kd \<noteq> 0 \<Longrightarrow> Kp \<noteq> 0 \<Longrightarrow> Kd\<^sup>2 \<noteq> Kp * 4 
  \<Longrightarrow> local_flow_on [x \<leadsto> v, v \<leadsto> - Kp * (x - xr) - Kd * v] (x +\<^sub>L v) UNIV UNIV 
  (\<lambda>t. [x \<leadsto> exp(-(t*(Kd - ((Kd\<^sup>2 - 4*Kp) powr (1/2))))/2)
    *(Kd/Kp - (Kd/2 - ((Kd\<^sup>2 - 4*Kp) powr (1/2))/2)/Kp)
    *((Kd * v + 2*Kp*x - 2*Kp*xr - v *((Kd\<^sup>2 - 4*Kp) powr (1/2)))/(2*((Kd\<^sup>2 - 4*Kp) powr (1/2))) 
      + (Kp*xr*exp(-(t*((Kd\<^sup>2 - 4*Kp) powr (1/2)))/2)*exp((Kd*t)/2))/((Kd\<^sup>2 - 4*Kp) powr (1/2))) 
  - exp(-(t*(Kd + ((Kd\<^sup>2 - 4*Kp) powr (1/2))))/2)*(Kd/Kp - (Kd/2 + ((Kd\<^sup>2 - 4*Kp) powr (1/2))/2)/Kp)
    * ((Kd* v + 2*Kp*x - 2*Kp*xr + v *((Kd\<^sup>2 - 4*Kp) powr (1/2)))/(2*((Kd\<^sup>2 - 4*Kp) powr (1/2))) 
      + (Kp*xr*exp((t*((Kd\<^sup>2 - 4*Kp) powr (1/2)))/2)*exp((Kd*t)/2))/((Kd\<^sup>2 - 4*Kp) powr (1/2))), 
  v \<leadsto> exp(-(t*(Kd + ((Kd\<^sup>2 - 4*Kp) powr (1/2))))/2)
  *((Kd * v + 2*Kp*x - 2*Kp*xr + v *((Kd\<^sup>2 - 4*Kp) powr (1/2)))/(2*((Kd\<^sup>2 - 4*Kp) powr (1/2))) 
    + (Kp*xr*exp((t*((Kd\<^sup>2 - 4*Kp) powr (1/2)))/2)*exp((Kd*t)/2))/((Kd\<^sup>2 - 4*Kp) powr (1/2))) 
  - exp(-(t*(Kd - ((Kd\<^sup>2 - 4*Kp) powr (1/2))))/2)
    *((Kd * v + 2*Kp*x - 2*Kp*xr - v *((Kd\<^sup>2 - 4*Kp) powr (1/2)))/(2*((Kd\<^sup>2 - 4*Kp) powr (1/2))) 
    + (Kp*xr*exp(-(t*((Kd\<^sup>2 - 4*Kp) powr (1/2)))/2)*exp((Kd*t)/2))/((Kd\<^sup>2 - 4*Kp) powr (1/2)))])"
  apply (clarsimp simp add: local_flow_on_def)
  apply (unfold_locales; expr_simp)
    prefer 3 subgoal
    by expr_simp (auto simp: fun_eq_iff field_simps exp_minus_inverse)
  subgoal by c1_lipschitz
  apply (intro vderiv_intros; (force intro!: vderiv_intros)?)
(*   apply (auto simp: fun_eq_iff field_split_simps exp_minus_inverse closed_segment_eq_real_ivl split: if_splits)
 *)  oops

(* x' = v, v' = -Kp*(x-xr) - Kd*v with Kp = 2 & Kd = 3*)
lemma local_flow_STTT_9b: "local_flow_on [v \<leadsto> 2 * xr - 2 * x - 3 * v, x \<leadsto> v] (x +\<^sub>L v) UNIV UNIV 
  (\<lambda>t. [x \<leadsto> exp (-2*t) * (xr - 2 * xr * exp t + xr * exp (2 * t) - v + v * exp t - x + 2 * x * exp t), 
  v \<leadsto> exp (-2*t) * (-2 * xr + 2 * xr * exp t + 2 * v - v * exp t + 2 * x - 2 * x * exp t)])"
  apply (clarsimp simp add: local_flow_on_def)
  apply (unfold_locales; expr_simp)
  apply c1_lipschitz
  by (auto intro!: has_derivative_Blinfun derivative_eq_intros vderiv_intros split: if_splits)
    (auto simp: fun_eq_iff field_simps exp_minus_inverse)

lemma STTT_9b_arith:
  assumes "Kp = 2" "Kd = 3" "0 \<le> V" "XM \<le> X" "S + XM = XR * 2"
  shows "X * (XR * 64) \<le> V\<^sup>2 * 32 + (X\<^sup>2 * 32 + XR\<^sup>2 * 32)" (is "?lhs \<le> ?rhs")
proof-
  have hammer_found: "2 * (X * XR) \<le> (V\<^sup>2 + X\<^sup>2 + XR\<^sup>2)"
    using assms
    using is_num_normalize(1)[of "V\<^sup>2" "X\<^sup>2" "XR\<^sup>2"] 
      le_add_same_cancel2[of "X\<^sup>2 + XR\<^sup>2" "V\<^sup>2"] 
      more_arith_simps(11)[of Kp X XR]
      order_trans_rules(23)[of "Kp * (X * XR)" "X\<^sup>2 + XR\<^sup>2" "V\<^sup>2 + (X\<^sup>2 + XR\<^sup>2)"] 
      sum_squares_bound[of X XR] 
    by presburger
  have "?lhs \<le> ?rhs \<longleftrightarrow> 64 * (X * XR) \<le> 32 * (V\<^sup>2 + X\<^sup>2 + XR\<^sup>2)"
    by powers_simp
  moreover have "... \<longleftrightarrow> 2 * (X * XR) \<le> (V\<^sup>2 + X\<^sup>2 + XR\<^sup>2)"
    by force
  ultimately show "?lhs \<le> ?rhs"
    using hammer_found
    by blast
qed

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
    by (simp add: wlp, expr_simp, force)
  subgoal
    using STTT_9b_arith1[of "get\<^bsub>v\<^esub> _" "get\<^bsub>xm\<^esub> _" "get\<^bsub>x\<^esub> _"]
    by (simp add: wlp, expr_simp, force)
  apply (rule_tac C="(xm \<le> x \<and> xr = (xm + S) / 2)\<^sup>e" in diff_cut_on_rule)
  subgoal
    apply (rule_tac a="(xm \<le> x \<and> xr = (xm + S) / 2)\<^sup>e" and b="(v \<ge> 0 \<and> x \<le> S 
  \<and> (5/4)*(x-xr)\<^sup>2 + (x-xr)* v/2 + v\<^sup>2/4 < ((S - xm)/2)\<^sup>2)\<^sup>e" in hoare_conj_preI)
     prefer 2 apply (force simp: fun_eq_iff)
    apply (rule fbox_invs)
     apply (simp only: expr_defs hoare_diff_inv_on fbox_diff_inv_on)?
     apply (diff_inv_on_single_ineq_intro "(0)\<^sup>e" "(v)\<^sup>e"; expr_simp)
    by (auto intro!: vderiv_intros)[1](diff_inv_on_eq)
  apply simp
  apply (rule_tac I="(5 * ($x - $xr)\<^sup>2 / 4 + ($x - $xr) * $v / 2 + ($v)\<^sup>2 / 4 < ((S - $xm) / 2)\<^sup>2)\<^sup>e" in fbox_diff_invI)
    prefer 3 apply expr_auto
   prefer 2 apply expr_auto
  apply powers_simp
  apply dInduct_auto
  apply (subgoal_tac "S = xr<s> * 2 - xm<s>")
  prefer 2 apply simp
   apply (rule subst[of "xr<_> * 2 - xm<_>" S], force)
  apply powers_simp
  using STTT_9b_arith by blast

end


subsubsection \<open> 51. STTT Tutorial: Example 10 \<close> (*N 51 *)

dataspace STTT_10 =
  constants A::real B::real \<epsilon>::real
  variables a::real v::real x::real dx::real y::real dy::real w::real r::real c::real

lemma subst_fbox: "\<sigma> \<dagger> ( |X] Q) = ( |\<sigma> \<dagger> X] (\<sigma> \<dagger> Q))"
  by (expr_simp add: fbox_def)

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
        INV (c \<ge> 0 \<and> dx\<^sup>2+dy\<^sup>2=1 \<and>
          (v'=a \<longrightarrow> v = old(v)+a*c) \<and>
          (v'=a \<longrightarrow> -c*(v-a/2*c) \<le> y - old(y) \<and> y - old(y) \<le> c*(v-a/2*c)) \<and>
          (v'=0 \<longrightarrow> v = old(v)) \<and>
          (v'=0 \<longrightarrow> -c * v \<le> y - old(y) \<and> y - old(y) \<le> c * v)
        )
        )
      ) INV (v \<ge> 0 \<and> dx\<^sup>2+dy\<^sup>2 = 1 \<and> r \<noteq> 0 \<and> \<bar>y - ly\<bar> + v\<^sup>2/(2*b) < lw)
    ] (\<bar>y - ly\<bar> < lw))`"
  apply (subst impl_eq_leq, subst fbox_to_hoare)
  apply (subst change_loopI[where I="(v \<ge> 0 \<and> A > 0 \<and> B \<ge> b \<and> b > 0 \<and> \<epsilon> > 0 \<and> lw > 0 \<and> r \<noteq> 0 
  \<and> dx\<^sup>2+dy\<^sup>2 = 1 \<and> \<bar>y - ly\<bar> + v\<^sup>2/(2*b) < lw)\<^sup>e"])
  apply intro_loops
    prefer 3 subgoal 
    by expr_auto
      (smt (verit, best) divide_eq_0_iff divide_pos_pos zero_less_power zero_power2)
   prefer 2 subgoal by expr_auto
    apply (rule_tac R="(v \<ge> 0 \<and> A > 0 \<and> B \<ge> b \<and> b > 0 \<and> \<epsilon> > 0 \<and> lw > 0 \<and> r \<noteq> 0 \<and> dx\<^sup>2+dy\<^sup>2 = 1 
    \<and> \<bar>y - ly\<bar> + v\<^sup>2/(2*b) < lw \<and> c=0
    \<and> ((\<bar>y - ly\<bar> + v\<^sup>2/(2*b) + (A/b+1)*(A/2*\<epsilon>\<^sup>2+\<epsilon>* v) < lw \<and> -B \<le> a \<and> a \<le> A \<and> w*r = v)
      \<or> (v = 0 \<and> a = 0 \<and> w = 0)
      \<or> (-B \<le> a \<and> a \<le> -b)))\<^sup>e" in hoare_kcomp)
   apply wlp_full
  apply (rule_tac x="v" in hoare_ghost_varI, simp)
  apply (rule_tac x="y" in hoare_ghost_varI, simp)
  apply (rename_tac v0 y0)
  apply (simp only: invar_def)
  subgoal for v0 y0
    apply (dCut "v = a * c + v0")
     apply postcondition_invariant
      apply (dInduct, expr_simp)
    apply (dCut "(c \<ge> 0 \<and> v \<ge> 0 \<and> dx\<^sup>2+dy\<^sup>2 = 1 \<and> A > 0 \<and> B \<ge> b \<and> b > 0 \<and> \<epsilon> > 0 \<and> lw > 0 \<and> r \<noteq> 0)")
     apply postcondition_invariant
      apply dInduct_mega'
      apply (rule nmods_invariant)
      apply (auto intro!: closure, expr_simp)[1]
     apply expr_simp
    apply (dCut "-c * v + a*c\<^sup>2/2 \<le> y - y0 \<and> y - y0 \<le> c * v - a*c\<^sup>2/2")
     apply postcondition_invariant
      apply dInduct_auto
    subgoal for s
      using STTT_10_arith1[where a="a<s>" and c="c<s>" and v="v<s>", of v0 "dx<s>" "dy<s>"]
        power2_eq_square by (auto simp: field_simps)
    subgoal for s
      using STTT_10_arith1[where a="a<s>" and c="c<s>" and v="v<s>", of v0 "dx<s>" "dy<s>"]
        power2_eq_square by (auto simp: field_simps)
    subgoal by expr_simp
    apply (rule_tac b="(\<bar>$y - ly\<bar> + ($v)\<^sup>2 / (2 * b) < lw)\<^sup>e" and
      a="(0 \<le> $v \<and> 0 < A \<and> b \<le> B \<and> 0 < b \<and> 0 < \<epsilon> \<and> 0 < lw \<and> $r \<noteq> 0 \<and> ($dx)\<^sup>2 + ($dy)\<^sup>2 = 1)\<^sup>e" in hoare_conj_posI)
        apply (rule diff_weak_on_rule, expr_simp)
   prefer 2 apply expr_simp
  apply (rule_tac a="(0 \<le> $v \<and> 0 < A \<and> b \<le> B \<and> 0 < b \<and> 0 < \<epsilon> \<and> 0 < lw \<and> $r \<noteq> 0 \<and> $c = 0 \<and> v = v0 \<and> y = y0
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
    subgoal (* SUBGOAL 1*)
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
   prefer 2 subgoal (* SUBGOAL 2*)
    apply (rule_tac C="(\<bar>y0 - ly\<bar> + (v0)\<^sup>2 / (2 * b) + (A / b + 1) * (A / 2 * \<epsilon>\<^sup>2 + \<epsilon> * v0) < lw)\<^sup>e" in diff_cut_on_rule)
    subgoal
      apply (rule_tac I="(\<bar>y0 - ly\<bar> + (v0)\<^sup>2 / (2 * b) + (A / b + 1) * (A / 2 * \<epsilon>\<^sup>2 + \<epsilon> * v0) < lw)\<^sup>e" in fbox_diff_invI)
      by (diff_inv_on_ineq "(0)\<^sup>e" "(0)\<^sup>e") (clarsimp simp: le_fun_def)+
    apply (rule_tac C="(v0 \<ge> 0 \<and> - B \<le> $a \<and> $a \<le> A)\<^sup>e" in diff_cut_on_rule)
    subgoal
      apply (rule_tac I="(v0 \<ge> 0 \<and> - B \<le> $a \<and> $a \<le> A)\<^sup>e" in hoare_invI)
      apply (intro hoare_invs)
      by (diff_inv_on_ineq "(0)\<^sup>e" "(0)\<^sup>e")+ (clarsimp simp: le_fun_def)+
    apply (rule diff_weak_on_rule)
    by expr_auto (rule STTT_10_arith2[of _ \<epsilon> "get\<^bsub>v\<^esub> _"]; assumption)
  subgoal (* SUBGOAL 3 *)
    apply (rule_tac C="(v0 \<ge> 0 \<and> - B \<le> $a \<and> $a \<le> - b)\<^sup>e" in diff_cut_on_rule)
    subgoal
      apply (rule_tac I="(v0 \<ge> 0 \<and> - B \<le> $a \<and> $a \<le> - b)\<^sup>e" in hoare_invI)
        apply (intro hoare_invs)
      by (diff_inv_on_ineq "(0)\<^sup>e" "(0)\<^sup>e")+ (clarsimp simp: le_fun_def)+
    apply (rule_tac C="(\<bar>y0 - ly\<bar> + (v0)\<^sup>2 / (2 * b) < lw)\<^sup>e" in diff_cut_on_rule)
    subgoal
      apply (rule_tac I="(\<bar>y0 - ly\<bar> + (v0)\<^sup>2 / (2 * b) < lw)\<^sup>e" in fbox_diff_invI)
      by (diff_inv_on_ineq "(0)\<^sup>e" "(0)\<^sup>e")+ (clarsimp simp: le_fun_def)+
    apply (rule diff_weak_on_rule)
    by expr_auto (rule STTT_10_arith3[of "get\<^bsub>v\<^esub> _"]; assumption)
  done
  done

end



context STTT
begin

(* { x' = v, v' = -Kp*(x-xr) - Kd*v & v >= 0 } *)
abbreviation "f9 Kd Kp \<equiv> [x \<leadsto> v, v \<leadsto> -Kp * (x - c) - Kd * v, c \<leadsto> 0]"

abbreviation "flow9 \<tau> \<equiv> [
  x \<leadsto> exp ((-2)*\<tau>) * (c - 2 * (exp \<tau>) * c + (exp (2 * \<tau>)) * c - v + (exp \<tau>) * v - x + 2 * (exp \<tau>) * x), 
  v \<leadsto> exp ((-2)*\<tau>) * (-2 * c + 2 * (exp \<tau>) * c + 2 * v - (exp \<tau>) * v + 2* x - 2 * (exp \<tau>) * x),
  c \<leadsto> c]"

lemma 
  assumes "Kp = 2" "Kd = 3"
  shows "local_flow_on (f9 Kd Kp) (x +\<^sub>L v +\<^sub>L c) UNIV UNIV flow9"
  (* apply local_flow_on_auto *)
  apply (unfold local_flow_on_def, clarsimp)
  apply (unfold_locales; clarsimp?)
    apply(expr_simp, rule_tac \<DD>="\<lambda>p. (fst (snd p), -Kp * (fst p - snd (snd p)) - Kd * fst (snd p), 0)" in c1_local_lipschitz; clarsimp?)
    apply (force simp: fun_eq_iff intro!: derivative_eq_intros)
  prefer 2 apply expr_simp
  apply (expr_simp)
  by (intro vderiv_intros; (rule vderiv_intros | force)?)
    (auto simp: assms field_simps exp_minus_inverse)

end


end