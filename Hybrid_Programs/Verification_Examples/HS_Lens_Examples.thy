(*  Title: Examples of hybrid systems verifications *)

subsection \<open> Examples \<close>

text \<open> We prove partial correctness specifications of some hybrid systems with our
verification components.\<close>

theory HS_Lens_Examples
  imports "Hybrid-Verification.Hybrid_Verification"

begin

lemma num2I: "P 1 \<Longrightarrow> P 2 \<Longrightarrow> P j" for j::2
  by (meson forall_2)

lemma num3I: "P 1 \<Longrightarrow> P 2 \<Longrightarrow> P 3 \<Longrightarrow> P j" for j::3
  by (meson forall_3)

lemma num4I: "P 1 \<Longrightarrow> P 2 \<Longrightarrow> P 3 \<Longrightarrow> P 4 \<Longrightarrow> P j" for j::4
  by (meson forall_4)

lemma hoare_cases: "\<^bold>{p \<and> I\<^bold>}S\<^bold>{p \<and> I\<^bold>} \<Longrightarrow> \<^bold>{\<not> p \<and> I\<^bold>}S\<^bold>{\<not> p \<and> I\<^bold>} \<Longrightarrow> \<^bold>{I\<^bold>}S\<^bold>{I\<^bold>}"
  by (auto simp add: fbox_def SEXP_def)

abbreviation (input) real_of_bool :: "bool \<Rightarrow> real" where "real_of_bool \<equiv> of_bool"

declare [[coercion real_of_bool]]

lemma differentiable_of_bool [closure]:
  "\<lbrakk> vwb_lens a; $a \<sharp> (e)\<^sub>e \<rbrakk> \<Longrightarrow> differentiable\<^sub>e (of_bool e) on a"
  by (rule differentiable_discr_expr, simp, unrest)

definition vec_lens :: "'i \<Rightarrow> ('a \<Longrightarrow> 'a^'i)" where
[lens_defs]: "vec_lens k = \<lparr> lens_get = (\<lambda> s. vec_nth s k)
                           , lens_put = (\<lambda> s v. (\<chi> j. ((($) s)(k := v)) j)) \<rparr>"

lemma vec_vwb_lens [simp]: "vwb_lens (vec_lens k)"
  apply (unfold_locales)
  apply (simp_all add: vec_lens_def fun_eq_iff)
  using vec_lambda_unique apply fastforce
  done

lemma vec_lens_indep [simp]: "(i \<noteq> j) \<Longrightarrow> (vec_lens i \<bowtie> vec_lens j)"
  by (simp add: lens_indep_vwb_iff, auto simp add: lens_defs)


subsubsection \<open>Pendulum\<close>

text \<open> The ODEs @{text "x' t = y t"} and {text "y' t = - x t"} describe the circular motion of
a mass attached to a string looked from above. We use @{text "s$1"} to represent the x-coordinate
and @{text "s$2"} for the y-coordinate. We prove that this motion remains circular. \<close>


dataspace pendulum =
  constants r :: real
  variables 
    x :: real 
    y :: real

context pendulum
begin

\<comment> \<open>Verified with annotated dynamics \<close>

abbreviation "pend_flow \<tau> \<equiv> [
  x \<leadsto> x * \<guillemotleft>cos \<tau>\<guillemotright> + y * \<guillemotleft>sin \<tau>\<guillemotright>, 
  y \<leadsto> - x * \<guillemotleft>sin \<tau>\<guillemotright> + y * \<guillemotleft>cos \<tau>\<guillemotright>]"

lemma pendulum_dyn: 
  "\<^bold>{\<guillemotleft>r\<guillemotright>\<^sup>2 = ($x)\<^sup>2 + ($y)\<^sup>2\<^bold>} (EVOL pend_flow G U) \<^bold>{\<guillemotleft>r\<guillemotright>\<^sup>2 = ($x)\<^sup>2 + ($y)\<^sup>2\<^bold>}"
  by (simp add: fbox_g_evol) expr_auto

\<comment> \<open>Verified with lie_derivative \<close>

lemma pendulum_lie: "\<^bold>{\<guillemotleft>r\<guillemotright>\<^sup>2 = x\<^sup>2 + y\<^sup>2\<^bold>} {(x, y)` = (y, -x)} \<^bold>{\<guillemotleft>r\<guillemotright>\<^sup>2 = x\<^sup>2 + y\<^sup>2\<^bold>}"
  by dInduct

\<comment> \<open>Verified with differential invariants as cartesian product \<close>

lemma pendulum_inv: "\<^bold>{\<guillemotleft>r\<guillemotright>\<^sup>2 = x\<^sup>2 + y\<^sup>2\<^bold>} {(x, y)` = (y, -x)} \<^bold>{\<guillemotleft>r\<guillemotright>\<^sup>2 = x\<^sup>2 + y\<^sup>2\<^bold>}"
  apply(simp add: hoare_diff_inv_on')
  apply(rule diff_inv_on_eqI)
  by clarsimp+ (expr_auto, auto intro!: vderiv_intros simp: case_prod_beta)

end

locale pendulum2 =
  fixes x :: "real \<Longrightarrow> real^2"
    and y :: "real \<Longrightarrow> real^2"
  assumes x_def [simp]: "x \<equiv> vec_lens 1"
    and   y_def [simp]: "y \<equiv> vec_lens 2"
begin

\<comment> \<open>Verified with differential invariants in @{text "\<real>\<^sup>2"} \<close>

abbreviation fpend :: "real^2 \<Rightarrow> real^2" ("f") 
  where "fpend \<equiv> [x \<leadsto> y, y \<leadsto> -x]"

lemma pendulum_inv: "\<^bold>{\<guillemotleft>r\<guillemotright>\<^sup>2 = x\<^sup>2 + y\<^sup>2\<^bold>} (x\<acute>= f & G) \<^bold>{\<guillemotleft>r\<guillemotright>\<^sup>2 = x\<^sup>2 + y\<^sup>2\<^bold>}"
  by (simp add: hoare_diff_inv, expr_auto) 
    (auto intro!: diff_inv_rules vderiv_intros)

\<comment> \<open>Verified with the flow in @{text "\<real>\<^sup>2"} \<close>

abbreviation pend_flow2 :: "real \<Rightarrow> real ^ 2 \<Rightarrow> real ^ 2" ("\<phi>")
  where "pend_flow2 \<tau> \<equiv> [
  x \<leadsto> x * \<guillemotleft>cos \<tau>\<guillemotright> + y * \<guillemotleft>sin \<tau>\<guillemotright>, 
  y \<leadsto> - x * \<guillemotleft>sin \<tau>\<guillemotright> + y * \<guillemotleft>cos \<tau>\<guillemotright>]"

lemma local_flow_pend: "local_flow f UNIV UNIV \<phi>"
  apply(unfold_locales, simp_all add: local_lipschitz_def lipschitz_on_def vec_eq_iff, clarsimp)
    apply(rule_tac x="1" in exI, clarsimp, rule_tac x=1 in exI)
    apply(clarsimp, expr_auto, simp add: dist_norm norm_vec_def L2_set_def power2_commute UNIV_2)
   apply(expr_auto, case_tac "i = 1 \<or> i = 2", auto simp: forall_2  intro!: vderiv_intros)
  using exhaust_2 by force expr_auto+

lemma "local_flow f UNIV UNIV \<phi>"
  apply (unfold_locales; expr_auto)
  apply ((rule_tac \<DD>=f in c1_local_lipschitz; expr_auto), fastforce intro: num2I intro!: derivative_intros, 
   fastforce intro: num2I continuous_intros)
   apply(case_tac "i = 1 \<or> i = 2", auto simp: forall_2  intro!: vderiv_intros)
  using exhaust_2 by (auto simp: vec_eq_iff)

lemma pendulum_flow: "\<^bold>{\<guillemotleft>r\<guillemotright>\<^sup>2 = x\<^sup>2 + y\<^sup>2\<^bold>} (x\<acute>= f & G) \<^bold>{\<guillemotleft>r\<guillemotright>\<^sup>2 = x\<^sup>2 + y\<^sup>2\<^bold>}"
  apply(subst local_flow.fbox_g_ode_subset[OF local_flow_pend], simp)
  by (auto, expr_auto)

no_notation fpend ("f")
        and pend_flow2 ("\<phi>")

end


subsubsection \<open> Bouncing Ball \<close>

text \<open> A ball is dropped from rest at an initial height @{text "H"}. The motion is described with
the free-fall equations @{text "y' t = v t"} and @{text "v' t = - g"} where @{text "g"} is the
constant acceleration due to gravity. The bounce is modelled with a variable assignment that
flips the velocity. We prove that the ball remains above ground and below its initial resting 
position. \<close>

locale bouncing_ball =
  fixes g :: real         \<comment> \<open> Gravitational acceleration constant \<close>
    and H :: real         \<comment> \<open> The initial or maximum height of the ball \<close>
    and c :: real         \<comment> \<open> The damping coefficient applied upon rebound \<close>
    and y :: "real \<Longrightarrow> real^2"
    and v :: "real \<Longrightarrow> real^2"
  assumes g_pos: "g > 0"  \<comment> \<open> The gravitational constant should be strictly positive (e.g. 9.81) \<close>
    and c_pos: "c > 0"    \<comment> \<open> The damping coefficient is greater than 0... \<close>
    and c_le_one: "c \<le> 1" \<comment> \<open> ... and no greater than 1, otherwise it increases its bounce. \<close>
    and H_pos: "H \<ge> 0"
    and y_def [simp]: "y \<equiv> vec_lens 1"
    and v_def [simp]: "v \<equiv> vec_lens 2"
begin

abbreviation fball :: "real ^ 2 \<Rightarrow> real ^ 2" ("f")
  where "fball \<equiv> [y \<leadsto> v, v \<leadsto> - \<guillemotleft>g\<guillemotright>]"

abbreviation ball_loop_inv :: "real ^ 2 \<Rightarrow> bool" ("I")
  where "I \<equiv> (v\<^sup>2 \<le> 2 * \<guillemotleft>g\<guillemotright> * (\<guillemotleft>H\<guillemotright> - y))\<^sub>e"

\<comment> \<open>Verified with differential invariants in @{text "\<real>\<^sup>2"} \<close>

abbreviation "BBall_dinv \<equiv> 
  LOOP (
    (x\<acute>= f & (0 \<le> y)\<^sub>e DINV I); 
    IF v = 0 THEN v ::= - \<guillemotleft>c\<guillemotright> * v ELSE skip) 
  INV (0 \<le> y \<and> v\<^sup>2 \<le> 2 * \<guillemotleft>g\<guillemotright> * (\<guillemotleft>H\<guillemotright> - y))"

lemma ball_diff_inv: "\<^bold>{v\<^sup>2 \<le> 2 * \<guillemotleft>g\<guillemotright> * (\<guillemotleft>H\<guillemotright> - y)\<^bold>} (x\<acute>= f & (0 \<le> $y)\<^sub>e) \<^bold>{v\<^sup>2 \<le> 2 * \<guillemotleft>g\<guillemotright> * (\<guillemotleft>H\<guillemotright> - y)\<^bold>}"
  apply(subst hoare_diff_inv)
   apply(rule_tac \<mu>'="(2 * \<guillemotleft>g\<guillemotright> * v)\<^sub>e" and \<nu>'="(2 * \<guillemotleft>g\<guillemotright> * v)\<^sub>e" in diff_inv_leq_law)
      apply (simp_all add: is_interval_def)
  by expr_auto (auto intro!: vderiv_intros)

lemma "\<^bold>{v = 0 \<and> y = \<guillemotleft>H\<guillemotright>\<^bold>} BBall_dinv \<^bold>{0 \<le> y \<and> y \<le> \<guillemotleft>H\<guillemotright>\<^bold>}"
  apply(rule hoare_loopI, simp only: wlp fbox_if_then_else)
    apply(rule hoare_g_odei)
  using ball_diff_inv apply simp
     apply force
    apply expr_auto
   apply(simp add: H_pos)
  by expr_auto (smt g_pos mult_pos_neg zero_le_power2)

\<comment> \<open>Verified with annotated dynamics \<close>

abbreviation ball_flow :: "real \<Rightarrow> real ^ 2 \<Rightarrow> real ^ 2" ("\<phi>")
  where "\<phi> \<tau> \<equiv> [
  y \<leadsto> - \<guillemotleft>g\<guillemotright> * \<guillemotleft>\<tau>\<guillemotright>\<^sup>2 / 2 + v * \<guillemotleft>\<tau>\<guillemotright> + y, 
  v \<leadsto> - \<guillemotleft>g\<guillemotright> * \<guillemotleft>\<tau>\<guillemotright> + v]"

abbreviation "BBall_dyn \<equiv> 
  LOOP (
    (EVOL \<phi> (0 \<le> y)\<^sub>e (\<lambda>s. UNIV)); 
    IF v = 0 THEN v ::= - \<guillemotleft>c\<guillemotright> * v ELSE skip) 
  INV (0 \<le> y \<and> v\<^sup>2 \<le> 2 * \<guillemotleft>g\<guillemotright> * (\<guillemotleft>H\<guillemotright> - y))"

lemma BBall_dyn_arith:
  assumes "g * (2 * x) + x' * x' \<le> H * (g * 2)"
  shows "x \<le> H"
proof-
  have "g * (2 * x) \<le> H * (g * 2)"
    using assms by (metis add.commute le_add_same_cancel2 
        mult_2_right order_trans zero_le_square) 
  hence "2 * g * x \<le> 2 * g * H"
    by (simp add: mult.commute)
  thus "x \<le> H"
    using g_pos by auto
qed

lemma "\<^bold>{v = 0 \<and> y = \<guillemotleft>H\<guillemotright>\<^bold>} BBall_dyn \<^bold>{0 \<le> y \<and> y \<le> \<guillemotleft>H\<guillemotright>\<^bold>}"
  apply(rule hoare_loopI, simp only: wlp fbox_if_then_else fbox_g_evol)
    apply(expr_auto, auto simp: field_simps)
  using c_pos c_le_one H_pos apply expr_auto
    using BBall_dyn_arith by expr_auto

\<comment> \<open>Verified with the flow in @{text "\<real>\<^sup>2"} \<close>

abbreviation "BBall \<equiv> 
  LOOP (
    (x\<acute>= f & (0 \<le> y)\<^sub>e); 
    IF v = 0 THEN v ::= - \<guillemotleft>c\<guillemotright> * v ELSE skip) 
  INV (0 \<le> y \<and> v\<^sup>2 \<le> 2 * \<guillemotleft>g\<guillemotright> * (\<guillemotleft>H\<guillemotright> - y))"

lemma local_flow_ball: "local_flow f UNIV UNIV \<phi>"
  apply(unfold_locales, simp_all add: local_lipschitz_def lipschitz_on_def vec_eq_iff, expr_auto)
    apply(rule_tac x="1/2" in exI, clarsimp, rule_tac x=1 in exI)
    apply(simp add: dist_norm norm_vec_def L2_set_def UNIV_2)
  apply (expr_auto, case_tac "i = 1 \<or> i = 2", auto simp: forall_2 intro!: vderiv_intros )
  using exhaust_2 by force expr_auto+

abbreviation dfball :: "real ^ 2 \<Rightarrow> real ^ 2" ("df")
  where "dfball \<equiv> [y \<leadsto> v, v \<leadsto> 0]"

lemma "local_flow f UNIV UNIV \<phi>"
  apply (unfold_locales; expr_auto)
  apply ((rule_tac \<DD>=df in c1_local_lipschitz; expr_auto), fastforce intro: num2I intro!: derivative_intros, 
   fastforce intro: num2I continuous_intros)
   apply(case_tac "i = 1 \<or> i = 2", auto simp: forall_2  intro!: vderiv_intros)
  using exhaust_2 by (auto simp: vec_eq_iff)

lemma "\<^bold>{v = 0 \<and> y = \<guillemotleft>H\<guillemotright>\<^bold>} BBall \<^bold>{0 \<le> y \<and> y \<le> \<guillemotleft>H\<guillemotright>\<^bold>}"
  apply(rule hoare_loopI, simp only: wlp fbox_if_then_else)
    apply(subst local_flow.fbox_g_ode_subset[OF local_flow_ball], simp)
  using g_pos apply(expr_simp, clarsimp simp: field_simps)
  using c_pos c_le_one H_pos apply expr_auto
  using BBall_dyn_arith
  by (expr_auto, clarsimp simp: field_simps, simp add: mult.commute)

no_notation fball ("f")
        and dfball ("df")
        and ball_flow ("\<phi>")

end

subsubsection \<open> Thermostat \<close>

text \<open> A thermostat has a chronometer, a thermometer and a switch to turn on and off a heater.
At most every @{text "t"} minutes, it sets its chronometer to @{term "0::real"}, it registers
the room temperature, and it turns the heater on (or off) based on this reading. The temperature
follows the ODE @{text "T' = - a * (T - U)"} where @{text "U"} is @{text "L \<ge> 0"} when the heater
is on, and @{text "0"} when it is off. We prove that the thermostat keeps the room's
temperature between @{text "Tmin"} and @{text "Tmax"}. \<close>

lemma temp_dyn_down_real_arith:
  assumes "a > 0" and Thyps: "0 < Tmin" "Tmin \<le> T" "T \<le> Tmax"
    and thyps: "0 \<le> (t::real)" "\<forall>\<tau>\<in>{0..t}. \<tau> \<le> - (ln (Tmin / T) / a) "
  shows "Tmin \<le> exp (-a * t) * T" and "exp (-a * t) * T \<le> Tmax"
proof-
  have "0 \<le> t \<and> t \<le> - (ln (Tmin / T) / a)"
    using thyps by auto
  hence "ln (Tmin / T) \<le> - a * t \<and> - a * t \<le> 0"
    using assms(1) divide_le_cancel by fastforce
  also have "Tmin / T > 0"
    using Thyps by auto
  ultimately have obs: "Tmin / T \<le> exp (-a * t)" "exp (-a * t) \<le> 1"
    using exp_ln exp_le_one_iff by (metis exp_less_cancel_iff not_less, simp)
  thus "Tmin \<le> exp (-a * t) * T"
    using Thyps by (simp add: pos_divide_le_eq)
  show "exp (-a * t) * T \<le> Tmax"
    using Thyps mult_left_le_one_le[OF _ exp_ge_zero obs(2), of T]
      less_eq_real_def order_trans_rules(23) by blast
qed

lemma temp_dyn_up_real_arith:
  assumes "a > 0" and Thyps: "Tmin \<le> T" "T \<le> Tmax" "Tmax < (L::real)"
    and thyps: "0 \<le> t" "\<forall>\<tau>\<in>{0..t}. \<tau> \<le> - (ln ((L - Tmax) / (L - T)) / a) "
  shows "L - Tmax \<le> exp (-(a * t)) * (L - T)"
    and "L - exp (-(a * t)) * (L - T) \<le> Tmax"
    and "Tmin \<le> L - exp (-(a * t)) * (L - T)"
proof-
  have "0 \<le> t \<and> t \<le> - (ln ((L - Tmax) / (L - T)) / a)"
    using thyps by auto
  hence "ln ((L - Tmax) / (L - T)) \<le> - a * t \<and> - a * t \<le> 0"
    using assms(1) divide_le_cancel by fastforce
  also have "(L - Tmax) / (L - T) > 0"
    using Thyps by auto
  ultimately have "(L - Tmax) / (L - T) \<le> exp (-a * t) \<and> exp (-a * t) \<le> 1"
    using exp_ln exp_le_one_iff by (metis exp_less_cancel_iff not_less)
  moreover have "L - T > 0"
    using Thyps by auto
  ultimately have obs: "(L - Tmax) \<le> exp (-a * t) * (L - T) \<and> exp (-a * t) * (L - T) \<le> (L - T)"
    by (simp add: pos_divide_le_eq)
  thus "(L - Tmax) \<le> exp (-(a * t)) * (L - T)"
    by auto
  thus "L - exp (-(a * t)) * (L - T) \<le> Tmax"
    by auto
  show "Tmin \<le> L - exp (-(a * t)) * (L - T)"
    using Thyps and obs by auto
qed

lit_vars

locale thermostat =
    \<comment> \<open> constants \<close>
  fixes a :: real
    and L :: real
    and "T\<^sub>m" :: real
    and "T\<^sub>M" :: real
    \<comment> \<open> variables \<close>
    and \<theta> :: "real \<Longrightarrow> real^4"
    and T :: "real \<Longrightarrow> real^4"
    and t :: "real \<Longrightarrow> real^4"
    and T\<^sub>0 :: "real \<Longrightarrow> real^4"
  assumes T_def [simp]: "T \<equiv> vec_lens 1"
    and t_def [simp]: "t \<equiv> vec_lens 2"
    and theta_def [simp]: "\<theta> \<equiv> vec_lens 3"
    and T0_def [simp]: "T\<^sub>0 \<equiv> vec_lens 4"
    and Tm_nonneg: "0 < T\<^sub>m"
    and Tm_less_TM: "T\<^sub>m + 1 < T\<^sub>M"
    and TM_less_L: "T\<^sub>M < L"
    and a_ge0: "a > 0"
begin

abbreviation therm_vec_field :: "real \<Rightarrow> real^4 \<Rightarrow> real^4" ("f")
  where "f c \<equiv> [T \<leadsto> - a * (T - c), t \<leadsto> 1, \<theta> \<leadsto> 0, T\<^sub>0 \<leadsto> 0]"

abbreviation therm_flow2 :: "real \<Rightarrow> real \<Rightarrow> real^4 \<Rightarrow> real^4" ("\<phi>")
  where "\<phi> c \<tau> \<equiv> [
  T \<leadsto> - exp(-a * \<tau>) * (c - T) + c,
  t \<leadsto> \<tau> + t,
  \<theta> \<leadsto> \<theta>,
  T\<^sub>0 \<leadsto> T\<^sub>0]"

lemma norm_diff_therm_dyn: "\<parallel>f c s\<^sub>1 - f c s\<^sub>2\<parallel> = a * \<bar>s\<^sub>1$1 - s\<^sub>2$1\<bar>"
proof(expr_simp, simp add: norm_vec_def L2_set_def, unfold UNIV_4, simp)
  have f2: "\<And>r ra. \<bar>(r::real) + - ra\<bar> = \<bar>ra + - r\<bar>"
    by (metis abs_minus_commute minus_real_def)
  have "\<And>r ra rb. (r::real) * ra + - (r * rb) = r * (ra + - rb)"
    by (metis minus_real_def right_diff_distrib)
  hence "\<bar>a * (s\<^sub>1$1 + - c) + - (a * (s\<^sub>2$1 + - c))\<bar> = a * \<bar>s\<^sub>1$1 + - s\<^sub>2$1\<bar>"
    using a_ge0 by (simp add: abs_mult)
  thus "\<bar>a * (s\<^sub>2$1 - c) - a * (s\<^sub>1$1 - c)\<bar> = a * \<bar>s\<^sub>1$1 - s\<^sub>2$1\<bar>"
    using f2 minus_real_def by presburger
qed

lemma local_lipschitz_therm_dyn:
  shows "local_lipschitz UNIV UNIV (\<lambda>t::real. f c)"
  using a_ge0 apply(unfold local_lipschitz_def lipschitz_on_def dist_norm)
  apply(clarify, rule_tac x=1 in exI, rule conjI, simp, rule_tac x=a in exI)
  by (simp only: norm_diff_therm_dyn) (metis Finite_Cartesian_Product.norm_nth_le 
      abs_1 abs_ge_zero mult.right_neutral mult_le_cancel_left_pos mult_zero_right 
      real_norm_def vector_minus_component)

lemma local_flow_therm: "local_flow (f c) UNIV UNIV (\<phi> c)"
  using a_ge0 apply unfold_locales
  prefer 6 apply(rule local_lipschitz_therm_dyn)
  apply (simp_all add: forall_4 vec_eq_iff, expr_auto)
  by (auto intro!: vderiv_intros) expr_auto+

abbreviation dftherm :: "real \<Rightarrow> real ^ 4 \<Rightarrow> real ^ 4" ("df")
  where "dftherm c \<equiv> [T \<leadsto> - a * T, t \<leadsto> 0, \<theta> \<leadsto> 0, T\<^sub>0 \<leadsto> 0]"

lemma "local_flow (f c) UNIV UNIV (\<phi> c)"
  apply (unfold_locales)
  prefer 6
    apply (rule_tac \<DD>="df c" in c1_local_lipschitz; expr_auto add: has_derivative_coordinate)
  subgoal for s i
    using exhaust_4[of i] apply safe
    by (auto intro!: derivative_eq_intros)
          apply(fastforce intro: num4I continuous_intros)
         apply (simp_all add: forall_4 vec_eq_iff, expr_auto)
  by (auto intro!: vderiv_intros) expr_auto+

abbreviation "therm_ctrl \<equiv> ((t ::= 0);(T\<^sub>0 ::= T);
    (IF \<theta> = 0 \<and> T\<^sub>0 \<le> T\<^sub>m + 1 THEN (\<theta> ::= 1) ELSE
    (IF \<theta> = 1 \<and> T\<^sub>0 \<ge> T\<^sub>M - 1 THEN (\<theta> ::= 0) ELSE skip)))"

abbreviation "therm_dyn \<equiv> 
    (IF \<theta> = 0 THEN (x\<acute>= f 0 & (t \<le> - (ln (T\<^sub>m/T\<^sub>0))/a)\<^sub>e) ELSE
    (x\<acute>= f L & (t \<le> - (ln ((L - T\<^sub>M)/(L - T\<^sub>0)))/a)\<^sub>e))"

lemmas fbox_therm_dyn = local_flow.fbox_g_ode_subset[OF local_flow_therm]

lemma 
  "\<^bold>{T\<^sub>m \<le> T \<and> T \<le> T\<^sub>M \<and> \<theta> = 0\<^bold>} 
    (LOOP (therm_ctrl; therm_dyn) INV (T\<^sub>m \<le> T \<and> T \<le> T\<^sub>M \<and> (\<theta> = 0 \<or> \<theta> = 1)))
   \<^bold>{T\<^sub>m \<le> T \<and> T \<le> T\<^sub>M\<^bold>}"
  apply(rule hoare_loopI, simp only: wlp fbox_if_then_else)
    apply(subst fbox_therm_dyn, expr_simp)+
  using temp_dyn_up_real_arith[OF a_ge0 _ _ TM_less_L, of "T\<^sub>m"]
    and temp_dyn_down_real_arith[OF a_ge0 Tm_nonneg, of _ "T\<^sub>M"]
  by expr_auto+

end


subsubsection \<open> Tank \<close>

text \<open> A controller turns a water pump on and off to keep the level of water @{text "h"} in a tank
within an acceptable range @{text "H\<^sub>l \<le> h \<le> H\<^sub>u"}. Just like in the previous example, after 
each intervention, the controller registers the current level of water and resets its chronometer,
then it changes the status of the water pump accordingly. The level of water grows linearly 
@{text "h' = k"} at a rate of @{text "k = c\<^sub>i-c\<^sub>o"} if the pump is on, and at a rate of 
@{text "k = -c\<^sub>o"} if the pump is off. We prove that the controller keeps the level of
water between @{text "H\<^sub>l"} and @{text "H\<^sub>u"}. \<close>

lemma tank_arith:
  assumes "0 \<le> (\<tau>::real)" and "0 < c\<^sub>o" and "c\<^sub>o < c\<^sub>i"
  shows "\<forall>\<tau>\<in>{0..\<tau>}. \<tau> \<le> - ((hmin - y) / c\<^sub>o) \<Longrightarrow>  hmin \<le> y - c\<^sub>o * \<tau>"
    and "\<forall>\<tau>\<in>{0..\<tau>}. \<tau> \<le> (hmax - y) / (c\<^sub>i - c\<^sub>o) \<Longrightarrow>  (c\<^sub>i - c\<^sub>o) * \<tau> + y \<le> hmax"
    and "hmin \<le> y \<Longrightarrow> hmin \<le> (c\<^sub>i - c\<^sub>o) * \<tau> + y"
    and "y \<le> hmax \<Longrightarrow> y - c\<^sub>o * \<tau> \<le> hmax"
  apply(simp_all add: field_simps le_divide_eq assms)
  using assms apply (meson add_mono less_eq_real_def mult_left_mono)
  using assms by (meson add_increasing2 less_eq_real_def mult_nonneg_nonneg) 

named_theorems local_flow

dataspace water_tank = 
  constants H\<^sub>l::real H\<^sub>u::real c\<^sub>o::real c\<^sub>i::real
  assumes co: "0 < c\<^sub>o" and ci: "c\<^sub>o < c\<^sub>i"
  variables flw::"bool" h::"real" h\<^sub>m::"real" t::"real"

context water_tank
begin

abbreviation tank_ode :: "real \<Rightarrow> real \<Rightarrow> 'a \<Rightarrow> 'st \<Rightarrow> 'st set"
  where "tank_ode h\<^sub>x k s \<equiv> {h` = k, t` = 1 | t \<le> (h\<^sub>x - h\<^sub>m)/k}"

abbreviation (input) tank_vec_field :: "real \<Rightarrow> 'st \<Rightarrow> 'st" ("f")
  where "tank_vec_field k \<equiv> [h \<leadsto> k, t \<leadsto> 1]"

abbreviation (input) tank_flow :: "real \<Rightarrow> real \<Rightarrow> 'st \<Rightarrow> 'st" ("\<phi>")
  where "tank_flow k \<tau> \<equiv> [h \<leadsto> k * \<tau> + h, t \<leadsto> \<tau> + t]"

lemma lflow_tank [local_flow]: "local_flow_on (f k) (h+\<^sub>Lt) UNIV UNIV (\<phi> k)"
  by local_flow_on_auto

lemma lf: "local_flow_on [h \<leadsto> k, t \<leadsto> 1] (h+\<^sub>Lt) UNIV UNIV (\<lambda>\<tau>. [h \<leadsto> k * \<tau> + h, t \<leadsto> \<tau> + t])"
  by local_flow_on_auto

abbreviation "ctrl \<equiv> (t, h\<^sub>m) ::= (0, h);
     IF \<not>flw \<and> h\<^sub>m \<le> H\<^sub>l + 1 THEN flw ::= True ELSE 
     IF flw \<and> h\<^sub>m \<ge> H\<^sub>u - 1 THEN flw ::= False ELSE skip"

abbreviation "dyn \<equiv> IF flw THEN {h` = c\<^sub>i - c\<^sub>o, t` = 1 | t \<le> (H\<^sub>u - h\<^sub>m)/(c\<^sub>i - c\<^sub>o)} 
     ELSE {h` = - c\<^sub>o, t` = 1 | t \<le> (H\<^sub>l - h\<^sub>m)/(- c\<^sub>o)}"

abbreviation "dyn' \<equiv> {h` = (flw*c\<^sub>i) - c\<^sub>o, t` = 1 | t \<le> ((flw*H\<^sub>u + (\<not>flw)*H\<^sub>l) - h\<^sub>m)/((flw*c\<^sub>i) - c\<^sub>o)}"

lemma nm: "dyn nmods {flw, h\<^sub>m}" by (simp add: closure)

lemma "\<^bold>{flw = F\<^bold>}dyn\<^bold>{flw = F\<^bold>}" by (rule nmods_invariant[OF nm], unrest)

lemma 
  "\<^bold>{H\<^sub>l \<le> h \<and> h \<le> H\<^sub>u\<^bold>} 
    LOOP ctrl ; dyn INV (H\<^sub>l \<le> h \<and> h \<le> H\<^sub>u)
   \<^bold>{H\<^sub>l \<le> h \<and> h \<le> H\<^sub>u\<^bold>}"
  using tank_arith[OF _ co ci]
  by (hoare_wp_auto local_flow: lflow_tank)

lemma "\<^bold>{flw \<and> 0 \<le> t \<and> h = (c\<^sub>i - c\<^sub>o)*t + h\<^sub>m \<and> H\<^sub>l \<le> h \<and> h \<le> H\<^sub>u\<^bold>}
         dyn'
       \<^bold>{flw \<and> 0 \<le> t \<and> h = (c\<^sub>i - c\<^sub>o)*t + h\<^sub>m \<and> H\<^sub>l \<le> h \<and> h \<le> H\<^sub>u\<^bold>}"
  using ci by dInduct_mega'

lemma "\<^bold>{0 \<le> t \<and> h = (c\<^sub>i - c\<^sub>o)*t + h\<^sub>m \<and> H\<^sub>l \<le> h \<and> h \<le> H\<^sub>u\<^bold>}
         {h` = c\<^sub>i - c\<^sub>o, t` = 1 | t \<le> (H\<^sub>u - h\<^sub>m)/(c\<^sub>i - c\<^sub>o)}
       \<^bold>{0 \<le> t \<and> h = (c\<^sub>i - c\<^sub>o)*t + h\<^sub>m \<and> H\<^sub>l \<le> h \<and> h \<le> H\<^sub>u\<^bold>}"
  using ci by dInduct_mega

lemma tank_correct:
  "\<^bold>{t = 0 \<and> h = h\<^sub>m \<and> H\<^sub>l \<le> h \<and> h \<le> H\<^sub>u\<^bold>}
      LOOP ctrl ; dyn INV (0 \<le> t \<and> h = ((flw * c\<^sub>i) - c\<^sub>o)*t + h\<^sub>m \<and> H\<^sub>l \<le> h \<and> h \<le> H\<^sub>u)
   \<^bold>{H\<^sub>l \<le> h \<and> h \<le> H\<^sub>u\<^bold>}"
  using ci co by dProve


(* TODO: Tactic for automated Hoare-style verification. *)
(* named_theorems hoare_intros "introduction rules from Hoare logic"

declare hoare_invs [hoare_intros]
    and hoare_skip [hoare_intros]
    and hoare_test [hoare_intros]
    and H_assign_init [hoare_intros]
    and hoare_if_then_else [hoare_intros]

method body_hoare 
  = (rule hoare_intros,(simp)?; body_hoare?)

method hyb_hoare for P::"'b \<Rightarrow> bool" 
  = (rule hoare_loopI, rule hoare_kcomp[where R=P]; body_hoare?)


lemma tank_diff_inv:
  "\<^bold>{h = k * t + h\<^sub>0 \<and> H\<^sub>l \<le> h \<and> h \<le> H\<^sub>u\<^bold>} 
    {h` = k, t` = 1 | t \<le> (H\<^sub>u - h\<^sub>m)/k}
   \<^bold>{h = k * t + h\<^sub>0 \<and> H\<^sub>l \<le> h \<and> h \<le> H\<^sub>u\<^bold>}"
  apply(subst subst_ode)
  apply(intro hoare_invs)
    apply(dInduct_mega)[1]
   apply(subst hoare_diff_inv_on)
   apply(rule lie_deriv_le_rule)
  sorry



lemma 
  "\<^bold>{H\<^sub>l \<le> h \<and> h \<le> H\<^sub>u\<^bold>} 
    LOOP ctrl ; dyn INV (h = k * t + h\<^sub>0 \<and> H\<^sub>l \<le> h \<and> h \<le> H\<^sub>u)
   \<^bold>{H\<^sub>l \<le> h \<and> h \<le> H\<^sub>u\<^bold>}"
  apply(hyb_hoare "(h = k * t + h\<^sub>0 \<and> H\<^sub>l \<le> h \<and> h \<le> H\<^sub>u)\<^sub>e")
        prefer 4 prefer 5
  using tank_diff_inv 
  apply (rule hoare_loopI)
  apply(rule hoare_loopI)
  apply(hyb_hoare "(H\<^sub>l \<le> $h)\<^sub>e")
    apply (simp only: wp fbox_if_then_else)
  apply clarsimp
  apply (hoare_wp_auto)
  apply (rule hoare_if_then_else_inv)
  using ci apply dInduct_mega
  thm nmods_invariant
      apply (rule_tac nmods_invariant)
       apply (rule nmods_g_orbital_on_discrete')
       apply (simp)
      apply unrest
     apply (dInduct_mega)
  apply (dInduct_auto)
  oops

abbreviation tank_diff_inv :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real^4) upred" ("dI")
  where "dI h\<^sub>l h\<^sub>h k \<equiv> \<^U>(h = k \<cdot> t + h\<^sub>0 \<and> 0 \<le> t \<and> h\<^sub>l \<le> h\<^sub>0 \<and> h\<^sub>0 \<le> h\<^sub>h \<and> (\<pi> = 0 \<or> \<pi> = 1))"

lemma tank_diff_inv:
  "0 \<le> \<tau> \<Longrightarrow> diff_invariant (dI h\<^sub>l h\<^sub>h k) (f k) {0..\<tau>} UNIV 0 Guard"
  apply(pred_simp, intro diff_invariant_conj_rule)
      apply(force intro!: poly_derivatives diff_invariant_rules)
     apply(rule_tac \<nu>'="\<lambda>t. 0" and \<mu>'="\<lambda>t. 1" in diff_invariant_leq_rule, simp_all)
    apply(rule_tac \<nu>'="\<lambda>t. 0" and \<mu>'="\<lambda>t. 0" in diff_invariant_leq_rule, simp_all)
  by (auto intro!: poly_derivatives diff_invariant_rules)

lemma tank_inv_arith1:
  assumes "0 \<le> (\<tau>::real)" and "c\<^sub>o < c\<^sub>i" and b: "h\<^sub>l \<le> y\<^sub>0" and g: "\<tau> \<le> (h\<^sub>h - y\<^sub>0) / (c\<^sub>i - c\<^sub>o)"
  shows "h\<^sub>l \<le> (c\<^sub>i - c\<^sub>o) \<cdot> \<tau> + y\<^sub>0" and "(c\<^sub>i - c\<^sub>o) \<cdot> \<tau> + y\<^sub>0 \<le> h\<^sub>h"
proof-
  have "(c\<^sub>i - c\<^sub>o) \<cdot> \<tau> \<le> (h\<^sub>h - y\<^sub>0)"
    using g assms(2,3) by (metis diff_gt_0_iff_gt mult.commute pos_le_divide_eq) 
  thus "(c\<^sub>i - c\<^sub>o) \<cdot> \<tau> + y\<^sub>0 \<le> h\<^sub>h"
    by auto
  show "h\<^sub>l \<le> (c\<^sub>i - c\<^sub>o) \<cdot> \<tau> + y\<^sub>0"
    using b assms(1,2) by (metis add.commute add_increasing2 diff_ge_0_iff_ge 
        less_eq_real_def mult_nonneg_nonneg) 
qed

lemma tank_inv_arith2:
  assumes "0 \<le> (\<tau>::real)" and "0 < c\<^sub>o" and b: "y\<^sub>0 \<le> h\<^sub>h" and g: "\<tau> \<le> - ((h\<^sub>l - y\<^sub>0) / c\<^sub>o)"
  shows "h\<^sub>l \<le> y\<^sub>0 - c\<^sub>o \<cdot> \<tau>" and "y\<^sub>0 - c\<^sub>o \<cdot> \<tau> \<le> h\<^sub>h"
proof-
  have "\<tau> \<cdot> c\<^sub>o \<le> y\<^sub>0 - h\<^sub>l"
    using g \<open>0 < c\<^sub>o\<close> pos_le_minus_divide_eq by fastforce 
  thus "h\<^sub>l \<le> y\<^sub>0 - c\<^sub>o \<cdot> \<tau>"
    by (auto simp: mult.commute)
  show "y\<^sub>0 - c\<^sub>o \<cdot> \<tau> \<le> h\<^sub>h" 
    using b assms(1,2)
    by (smt mult_sign_intros(1))  
qed

abbreviation tank_dyn_dinv :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real^4) nd_fun" ("dyn")
  where "dyn c\<^sub>i c\<^sub>o h\<^sub>l h\<^sub>h \<tau> \<equiv> IF (\<pi> = 0) THEN 
    x\<acute>= f (c\<^sub>i-c\<^sub>o) & G h\<^sub>h (c\<^sub>i-c\<^sub>o) on {0..\<tau>} UNIV @ 0 DINV (dI h\<^sub>l h\<^sub>h (c\<^sub>i-c\<^sub>o))
  ELSE x\<acute>= f (-c\<^sub>o) & G h\<^sub>l (-c\<^sub>o) on {0..\<tau>} UNIV @ 0 DINV (dI h\<^sub>l h\<^sub>h (-c\<^sub>o))"

abbreviation "tank_dinv c\<^sub>i c\<^sub>o h\<^sub>l h\<^sub>h \<tau> \<equiv> LOOP (ctrl h\<^sub>l h\<^sub>h ; dyn c\<^sub>i c\<^sub>o h\<^sub>l h\<^sub>h \<tau>) INV (I h\<^sub>l h\<^sub>h)"

lemma tank_inv:
  assumes "0 \<le> \<tau>" and "0 < c\<^sub>o" and "c\<^sub>o < c\<^sub>i"
  shows "\<^bold>{I h\<^sub>l h\<^sub>h\<^bold>} tank_dinv c\<^sub>i c\<^sub>o h\<^sub>l h\<^sub>h \<tau> \<^bold>{I h\<^sub>l h\<^sub>h\<^bold>}"
  apply(hyb_hoare "\<^U>(I h\<^sub>l h\<^sub>h \<and> t = 0 \<and> h\<^sub>0 = h)")
            prefer 4 prefer 7 using tank_diff_inv assms apply force+
  using assms tank_inv_arith1 tank_inv_arith2 by (rel_auto' simp: eucl_nth_def) *)


end

locale example_9b = 
  fixes Kp::real 
    and Kd::real
    and x::"real \<Longrightarrow> real^3" 
    and v::"real \<Longrightarrow> real^3" 
    and xr::"real \<Longrightarrow> real^3"
  assumes x_def [simp]: "x \<equiv> vec_lens 1"
    and v_def [simp]: "v \<equiv> vec_lens 2"
    and xr_def [simp]: "xr \<equiv> vec_lens 3"
    and kp_def: "Kp = 2" 
    and kd_def: "Kd = 3 "
begin

(* { x' = v, v' = -Kp*(x-xr) - Kd*v & v >= 0 } *)
abbreviation f9 :: "real ^ 3 \<Rightarrow> real ^ 3" 
  where "f9 \<equiv> [x \<leadsto> v, v \<leadsto> -Kp * (x - xr) - Kd * v, xr \<leadsto> 0]"

lemma local_lipschitz_f9: "local_lipschitz UNIV UNIV (\<lambda>t::real. f9)"
  apply(rule_tac \<DD>=f9 in c1_local_lipschitz; clarsimp)
  apply (expr_auto add: has_derivative_coordinate)
  subgoal for s i
    using exhaust_3[of i]
    by (auto intro!: derivative_eq_intros)
  apply expr_auto
  apply(rule_tac f'="\<lambda>t. f9" in has_derivative_continuous_on)
  apply (expr_auto add: has_derivative_coordinate)
  subgoal for s i
    using exhaust_3[of i]
    by (auto intro!: derivative_eq_intros)
  done

abbreviation "flow9 \<tau> \<equiv> [
  x \<leadsto> exp ((-2)*\<tau>) * (xr - 2 * (exp \<tau>) * xr + (exp (2 * \<tau>)) * xr - v + (exp \<tau>) * v - x + 2 * (exp \<tau>) * x), 
  v \<leadsto> exp ((-2)*\<tau>) * (-2 * xr + 2 * (exp \<tau>) * xr + 2 * v - (exp \<tau>) * v + 2* x - 2 * (exp \<tau>) * x),
  xr \<leadsto> xr]"

lemma "local_flow f9 UNIV UNIV flow9"
  apply(unfold_locales; (rule local_lipschitz_f9)?; clarsimp simp: vec_eq_iff; expr_auto)
  subgoal for t s i
    using exhaust_3[of i] apply (safe; clarsimp simp: kp_def kd_def)
      apply(auto intro!: vderiv_intros)[1]
         apply(force simp: field_simps)+
     prefer 2 apply(rule vderiv_intros)
      apply(auto intro!: vderiv_intros)[1]
    by (auto simp: field_simps exp_minus_inverse)
  done

end

end