theory ETCS
  imports "Hybrid-Verification.Hybrid_Verification"

begin

subsubsection \<open> ETCS \<close>

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

subsubsection \<open> ETCS: Essentials (safety) \<close>

(* HP drive ::= {t := 0;{z'=v, v'=a, t'=1  & v >= 0 & t <= ep} *)
abbreviation "drive \<equiv> (t ::= 0);{z` = v, v` = a, t` = 1 | (v \<ge> 0 \<and> t \<le> \<epsilon>)}"

lemma local_flow_LICS1: "local_flow_on [t \<leadsto> 1, v \<leadsto> $a, z \<leadsto> $v] (z +\<^sub>L v +\<^sub>L t) UNIV UNIV
  (\<lambda>\<tau>. [t \<leadsto> \<tau> + t, z \<leadsto> $a * \<tau>\<^sup>2 / 2 + $v * \<tau> + $z, v \<leadsto> $a * \<tau> + $v])"
  by local_flow_on_auto

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
    apply (wlp_full local_flow: local_flow_LICS1)
  using ETCS_arith1[of b A "get\<^bsub>v\<^esub> _" _ \<epsilon> m "get\<^bsub>z\<^esub> _"]
    apply (clarsimp simp: field_simps)
   apply expr_auto
  apply (expr_auto add: field_simps)
  apply (smt (verit, best) mult_left_le_imp_le zero_le_square)
  done


subsubsection \<open> ETCS: Proposition 1 (Controllability) \<close> (*N 62 *)

(* Bool Assumptions(Real v, Real d) <-> ( v>=0 & d>=0 & b>0 ) *)
abbreviation "Assumptions d \<equiv> (v \<ge> 0 \<and> d \<ge> 0 \<and> b > 0)\<^sub>e"

lemma local_flow_LICS2: "local_flow_on [v \<leadsto> -b, z \<leadsto> $v] (z +\<^sub>L v) UNIV UNIV
  (\<lambda>\<tau>. [z \<leadsto> -b * \<tau>\<^sup>2 / 2 + $v * \<tau> + $z, v \<leadsto> -b * \<tau> + $v])"
  by local_flow_on_auto

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
  apply (clarsimp simp: wlp taut_def fbox_g_dL_easiest[OF local_flow_LICS2], safe; expr_simp)
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
  apply (hol_clarsimp simp: wlp taut_def fbox_g_dL_easiest[OF local_flow_LICS1]; expr_simp)
   apply (safe; clarsimp simp: dlo_simps)
      apply (metis diff_zero)
  sorry  (* could not even prove it with KeYmaera X *)

end

end