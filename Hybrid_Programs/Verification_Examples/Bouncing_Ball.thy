section \<open> Bouncing Ball Proof \<close>

theory Bouncing_Ball
  imports "Hybrid-Verification.Hybrid_Verification"
begin

dataspace bouncing_ball =
  constants 
    H :: real
    g :: real
    e :: real
  assumes e_range: "0 < e" "e \<le> 1" and g_pos: "0 < g" and H_pos: "0 < H"
  variables 
    h :: real 
    v :: real

context bouncing_ball
begin

expression safety is "h \<le> H"

expression invariant is "0 \<le> h \<and> v\<^sup>2 \<le> 2*g*(H - h)"

definition "BBall = (h ::= H ; v ::= 0) ; LOOP ((IF h = 0 \<and> v < 0 THEN v ::= -e * v) ; {h` = v, v` = - g | h \<ge> 0}) INV (0 \<le> h \<and> v\<^sup>2 \<le> 2*g*(H - h))"

lemma ball_flow[local_flow]: "local_flow_on [h \<leadsto> v, v \<leadsto> - g] (h +\<^sub>L v) UNIV UNIV (\<lambda>t. [h \<leadsto> - 1 div 2 * g * t ^ 2 + h + t * v, v \<leadsto> - 1 * g * t + v])" 
  by local_flow_on_auto

text \<open> Proof with differential induction \<close>

lemma bouncing_ball_correct: "H{True} BBall {h \<le> H}"
  unfolding BBall_def 
  apply intro_loops \<comment> \<open> Introduce loop with invariant \<close>
    apply symbolic_exec \<comment> \<open> Execute imperative program operators \<close>
     apply postcondition_invariant \<comment> \<open> Use the postcondition as an invariant \<close>
      apply (smt (verit, ccfv_SIG) Groups.mult_ac(2) bouncing_ball.e_range(1,2) bouncing_ball_axioms more_arith_simps(7) mult_le_cancel_left_pos
      mult_left_le_one_le)
     apply dInduct_mega
    apply postcondition_invariant
    apply dInduct_mega
   apply symbolic_exec
  using H_pos apply linarith
  apply expr_auto
  apply (smt (verit, best) g_pos power2_less_eq_zero_iff zero_compare_simps(4) zero_eq_power2)
  done

text \<open> Proof with ODE solution \<close>

lemma bouncing_ball_correct': "H{True} BBall {h \<le> H}"
  unfolding BBall_def 
  apply intro_loops \<comment> \<open> Introduce loop with invariant \<close>
    apply symbolic_exec \<comment> \<open> Execute imperative program operators \<close>
     apply ode_solve
     apply (smt (z3) Groups.mult_ac(2) bouncing_ball.e_range(1,2)
      bouncing_ball_axioms more_arith_simps(11,7) mult_left_le_one_le
      not_real_square_gt_zero)
    apply (ode_solve_with "(\<lambda>t. [h \<leadsto> - 1 div 2 * g * t ^ 2 + h + t * v, v \<leadsto> - 1 * g * t + v])")
   apply symbolic_exec
  using H_pos apply linarith
  apply expr_auto
  apply (smt (verit, best) g_pos power2_less_eq_zero_iff zero_compare_simps(4) zero_eq_power2)
  done

text \<open> Alternative proof with ODE solution; could interface with CAS \<close>

lemma bouncing_ball_correct'': "H{True} BBall {h \<le> H}"
  unfolding BBall_def 
  apply intro_loops \<comment> \<open> Introduce loop with invariant \<close>
    apply symbolic_exec \<comment> \<open> Execute imperative program operators \<close>
     apply (ode_solve_with "(\<lambda>t. [h \<leadsto> - 1 div 2 * g * t ^ 2 + h + t * v, v \<leadsto> - 1 * g * t + v])")
     apply (smt (z3) Groups.mult_ac(2) bouncing_ball.e_range(1,2)
      bouncing_ball_axioms more_arith_simps(11,7) mult_left_le_one_le
      not_real_square_gt_zero)
    apply (ode_solve_with "(\<lambda>t. [h \<leadsto> - 1 div 2 * g * t ^ 2 + h + t * v, v \<leadsto> - 1 * g * t + v])")
   apply symbolic_exec
  using H_pos apply linarith
  apply expr_auto
  apply (smt (verit, best) g_pos power2_less_eq_zero_iff zero_compare_simps(4) zero_eq_power2)
  done

text \<open> Alternative proof with ODE solution; could interface with CAS \<close>

lemma "H{True} BBall {h \<le> H}"
  unfolding BBall_def 
  apply intro_loops
    apply symbolic_exec
     apply(wlp_full local_flow: ball_flow)
  apply (clarsimp simp: field_simps)
  apply (metis bouncing_ball.e_range(2) bouncing_ball_axioms e_range(1) less_eq_real_def linorder_not_less mult.right_neutral mult_le_cancel_left order_trans)
    apply(wlp_full local_flow: ball_flow)
  apply (clarsimp simp: field_simps)
   apply (use H_pos in wlp_simp, expr_auto)
  by expr_auto
    (smt (verit, best) g_pos realpow_square_minus_le zero_compare_simps(4))


end

end
