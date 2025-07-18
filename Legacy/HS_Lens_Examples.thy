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

text \<open> The ODEs @{text "x' t = y t"} and @{text "y' t = - x t"} describe the circular motion of
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
  x \<leadsto> x * cos \<tau> + y * sin \<tau>, 
  y \<leadsto> - x * sin \<tau> + y * cos \<tau>]"

lemma pendulum_dyn: 
  "H{\<guillemotleft>r\<guillemotright>\<^sup>2 = ($x)\<^sup>2 + ($y)\<^sup>2} (EVOL pend_flow G U) {\<guillemotleft>r\<guillemotright>\<^sup>2 = ($x)\<^sup>2 + ($y)\<^sup>2}"
  by (simp add: fbox_g_evol) expr_auto

\<comment> \<open>Verified with Framed derivatives \<close>

lemma pendulum_lie: "H{\<guillemotleft>r\<guillemotright>\<^sup>2 = x\<^sup>2 + y\<^sup>2} {x` = y, y` = - x} {\<guillemotleft>r\<guillemotright>\<^sup>2 = x\<^sup>2 + y\<^sup>2}"
  by dInduct

\<comment> \<open>Verified with differential invariants as cartesian product \<close>

lemma pendulum_inv: "H{\<guillemotleft>r\<guillemotright>\<^sup>2 = x\<^sup>2 + y\<^sup>2} {(x, y)` = (y, -x)} {\<guillemotleft>r\<guillemotright>\<^sup>2 = x\<^sup>2 + y\<^sup>2}"
  apply(simp add: hoare_diff_inv_on')
  apply(rule diff_inv_on_eqI)
  apply (simp add: var_pair_def)
  apply clarsimp+
  apply expr_simp
  apply (auto intro!: vderiv_intros )
  done

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

lemma ball_diff_inv: "H{v\<^sup>2 \<le> 2 * \<guillemotleft>g\<guillemotright> * (\<guillemotleft>H\<guillemotright> - y)} (x\<acute>= f & (0 \<le> $y)\<^sub>e) {v\<^sup>2 \<le> 2 * \<guillemotleft>g\<guillemotright> * (\<guillemotleft>H\<guillemotright> - y)}"
  apply(subst hoare_diff_inv)
   apply(rule_tac \<mu>'="(2 * \<guillemotleft>g\<guillemotright> * v)\<^sub>e" and \<nu>'="(2 * \<guillemotleft>g\<guillemotright> * v)\<^sub>e" in diff_inv_leq_law)
      apply (simp_all add: is_interval_def)
  by expr_auto (auto intro!: vderiv_intros)

lemma "H{v = 0 \<and> y = \<guillemotleft>H\<guillemotright>} BBall_dinv {0 \<le> y \<and> y \<le> \<guillemotleft>H\<guillemotright>}"
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

lemma "H{v = 0 \<and> y = \<guillemotleft>H\<guillemotright>} BBall_dyn {0 \<le> y \<and> y \<le> \<guillemotleft>H\<guillemotright>}"
  apply(rule hoare_loopI, simp only: wlp fbox_g_evol)
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
  apply ((rule_tac \<DD>=df in c1_local_lipschitz; expr_auto), fastforce intro: num2I intro!: derivative_intros)
   apply(case_tac "i = 1 \<or> i = 2", auto simp: forall_2  intro!: vderiv_intros)
  using exhaust_2 by (auto simp: vec_eq_iff)

lemma "H{v = 0 \<and> y = \<guillemotleft>H\<guillemotright>} BBall {0 \<le> y \<and> y \<le> \<guillemotleft>H\<guillemotright>}"
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

declare [[literal_variables]]

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
  "H{T\<^sub>m \<le> T \<and> T \<le> T\<^sub>M \<and> \<theta> = 0} 
    (LOOP (therm_ctrl; therm_dyn) INV (T\<^sub>m \<le> T \<and> T \<le> T\<^sub>M \<and> (\<theta> = 0 \<or> \<theta> = 1)))
   {T\<^sub>m \<le> T \<and> T \<le> T\<^sub>M}"
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

lemma lflow_tank [local_flow]: 
  "local_flow_on [h \<leadsto> k, t \<leadsto> 1] (h+\<^sub>Lt) UNIV UNIV (\<lambda>\<tau>. [h \<leadsto> k * \<tau> + h, t \<leadsto> \<tau> + t])"
  by local_flow_on_auto

abbreviation "ctrl \<equiv> (t, h\<^sub>m) ::= (0, h);
     IF \<not>flw \<and> h\<^sub>m \<le> H\<^sub>l + 1 THEN flw ::= True ELSE 
     IF flw \<and> h\<^sub>m \<ge> H\<^sub>u - 1 THEN flw ::= False ELSE skip"

abbreviation "dyn \<equiv> IF flw THEN {h` = c\<^sub>i - c\<^sub>o, t` = 1 | t \<le> (H\<^sub>u - h\<^sub>m)/(c\<^sub>i - c\<^sub>o)} 
     ELSE {h` = - c\<^sub>o, t` = 1 | t \<le> (H\<^sub>l - h\<^sub>m)/(- c\<^sub>o)}"

abbreviation "dyn' \<equiv> {h` = (flw*c\<^sub>i) - c\<^sub>o, t` = 1 | t \<le> ((flw*H\<^sub>u + (\<not>flw)*H\<^sub>l) - h\<^sub>m)/((flw*c\<^sub>i) - c\<^sub>o)}"

(* why doesn't this work anymore: by (simp add: closure) *)
lemma "dyn nmods {flw, h\<^sub>m}"
  by (subst closure(4); (subst closure(12))?; expr_auto)

lemma nm: "dyn nmods $flw = F"
  by (subst closure(4); (subst closure(12))?; expr_auto)

lemma "H{flw = F}dyn{flw = F}"
  by (rule nmods_invariant[OF nm])

lemma 
  "H{H\<^sub>l \<le> h \<and> h \<le> H\<^sub>u} 
    LOOP ctrl ; dyn INV (H\<^sub>l \<le> h \<and> h \<le> H\<^sub>u)
   {H\<^sub>l \<le> h \<and> h \<le> H\<^sub>u}"
  apply intro_loops
  using tank_arith[OF _ co ci]
  by (wlp_full local_flow: lflow_tank)
    expr_auto+


lemma "H{flw \<and> 0 \<le> t \<and> h = ((flw*c\<^sub>i) - c\<^sub>o)*t + h\<^sub>m \<and> H\<^sub>l \<le> h \<and> h \<le> H\<^sub>u}
         dyn'
       {flw \<and> 0 \<le> t \<and> h = ((flw*c\<^sub>i) - c\<^sub>o)*t + h\<^sub>m \<and> H\<^sub>l \<le> h \<and> h \<le> H\<^sub>u}"
  using ci
  apply dInduct_mega'
  by (rule nmods_invariant, subst closure; expr_simp)
    dInduct_mega

lemma "H{0 \<le> t \<and> h = (c\<^sub>i - c\<^sub>o)*t + h\<^sub>m \<and> H\<^sub>l \<le> h \<and> h \<le> H\<^sub>u}
         {h` = c\<^sub>i - c\<^sub>o, t` = 1 | t \<le> (H\<^sub>u - h\<^sub>m)/(c\<^sub>i - c\<^sub>o)}
       {0 \<le> t \<and> h = (c\<^sub>i - c\<^sub>o)*t + h\<^sub>m \<and> H\<^sub>l \<le> h \<and> h \<le> H\<^sub>u}"
  using ci by dInduct_mega

lemma tank_correct:
  "H{t = 0 \<and> h = h\<^sub>m \<and> H\<^sub>l \<le> h \<and> h \<le> H\<^sub>u}
      LOOP ctrl ; dyn INV (0 \<le> t \<and> h = ((flw * c\<^sub>i) - c\<^sub>o)*t + h\<^sub>m \<and> H\<^sub>l \<le> h \<and> h \<le> H\<^sub>u)
   {H\<^sub>l \<le> h \<and> h \<le> H\<^sub>u}"
  using ci co
  apply (rule_tac hoare_loop_seqI)
  by hoare_wp_auto
    ((dInduct_mega', (rule nmods_invariant, subst closure; expr_simp)) | (dInduct_mega', auto))+


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
  "{h = k * t + h\<^sub>0 \<and> H\<^sub>l \<le> h \<and> h \<le> H\<^sub>u} 
    {h` = k, t` = 1 | t \<le> (H\<^sub>u - h\<^sub>m)/k}
   {h = k * t + h\<^sub>0 \<and> H\<^sub>l \<le> h \<and> h \<le> H\<^sub>u}"
  apply(subst subst_ode)
  apply(intro hoare_invs)
    apply(dInduct_mega)[1]
   apply(subst hoare_diff_inv_on)
   apply(rule lie_deriv_le_rule)
  sorry



lemma 
  "{H\<^sub>l \<le> h \<and> h \<le> H\<^sub>u} 
    LOOP ctrl ; dyn INV (h = k * t + h\<^sub>0 \<and> H\<^sub>l \<le> h \<and> h \<le> H\<^sub>u)
   {H\<^sub>l \<le> h \<and> h \<le> H\<^sub>u}"
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
  shows "{I h\<^sub>l h\<^sub>h} tank_dinv c\<^sub>i c\<^sub>o h\<^sub>l h\<^sub>h \<tau> {I h\<^sub>l h\<^sub>h}"
  apply(hyb_hoare "\<^U>(I h\<^sub>l h\<^sub>h \<and> t = 0 \<and> h\<^sub>0 = h)")
            prefer 4 prefer 7 using tank_diff_inv assms apply force+
  using assms tank_inv_arith1 tank_inv_arith2 by (rel_auto' simp: eucl_nth_def) *)


end


subsubsection \<open> Rocket \<close>

lemma rocket_arith:
  assumes "(k::real) > 1" and "m\<^sub>0 > k" and "x \<in> {0..}"
  shows "- k*(x\<^sup>3)/6 + m\<^sub>0*(x\<^sup>2)/2 \<le> 2*(m\<^sub>0\<^sup>3)/(3*(k\<^sup>2))" (is "?lhs \<le> _")
proof-
  let ?f = "\<lambda>t. -k*t\<^sup>3/6 + m\<^sub>0*t\<^sup>2/2" 
    and ?f' = "\<lambda>t. -k*t\<^sup>2/2 + m\<^sub>0*t"
    and ?f'' = "\<lambda>t. -k*t + m\<^sub>0"
  have "2*m\<^sub>0\<^sup>3/(3*k\<^sup>2) = -k*(2*m\<^sub>0/k)\<^sup>3/6 + m\<^sub>0*(2*m\<^sub>0/k)\<^sup>2/2" (is "_ = ?rhs")
    by (auto simp: field_simps power3_eq_cube)
  moreover have "?lhs \<le> ?rhs"
  proof(cases "x \<le> 2 * m\<^sub>0 / k")
    case True
    have ge_0_left: "0 \<le> y \<Longrightarrow> y \<le> m\<^sub>0/k \<Longrightarrow> ?f' 0 \<le> ?f' y" for y
      apply (rule has_vderiv_mono_test(1)[of "{0..m\<^sub>0/k}" ?f' ?f'' 0])
      using \<open>k > 1\<close> \<open>m\<^sub>0 > k\<close>
      by (auto intro!: vderiv_intros simp: field_simps)
    moreover have ge_0_right: "m\<^sub>0/k \<le> y \<Longrightarrow> y \<le> 2*m\<^sub>0/k \<Longrightarrow> ?f' (2*m\<^sub>0/k) \<le> ?f' y" for y
      apply(rule has_vderiv_mono_test(2)[of "{m\<^sub>0/k..2*m\<^sub>0/k}" ?f' ?f'' _ "2*m\<^sub>0/k"])
      using \<open>k > 1\<close> \<open>m\<^sub>0 > k\<close>
      by (auto intro!: vderiv_intros simp: field_simps)
    ultimately have ge_0: "\<forall>y\<in>{0..2*m\<^sub>0/k}. 0 \<le> ?f' y"
      using \<open>k > 1\<close> \<open>m\<^sub>0 > k\<close>
      by (fastforce simp: field_simps)
    show ?thesis
      apply (rule has_vderiv_mono_test(1)[of "{0..2*m\<^sub>0/k}" ?f ?f' _ "2*m\<^sub>0/k"])
      using ge_0 True \<open>x \<in> {0..}\<close> \<open>k > 1\<close> \<open>m\<^sub>0 > k\<close>
      by (auto intro!: vderiv_intros simp: field_simps)
  next
    case False
    have "2*m\<^sub>0/k \<le> y \<Longrightarrow> ?f' y \<le> ?f' (2*m\<^sub>0/k)" for y
      apply (rule has_vderiv_mono_test(2)[of "{m\<^sub>0/k..}" ?f' ?f''])
      using \<open>k > 1\<close> \<open>m\<^sub>0 > k\<close> by (auto intro!: vderiv_intros simp: field_simps)
    hence obs: "\<forall>y\<in>{2*m\<^sub>0/k..}. ?f' y \<le> 0"
      using \<open>k > 1\<close> \<open>m\<^sub>0 > k\<close>
      by (clarsimp simp: field_simps)
    show ?thesis
      apply (rule has_vderiv_mono_test(2)[of "{2*m\<^sub>0/k..}" ?f ?f'])
      using False \<open>k > 1\<close> obs
      by (auto intro!: vderiv_intros simp: field_simps)
  qed
  ultimately show ?thesis
    by simp
qed

dataspace rocket = 
  constants k :: real
  assumes k_ge_1: "k > 1" 
  variables v :: real y :: real m :: real t :: real

context rocket
begin

abbreviation "ode \<equiv> {y` = v, v` = m, t` = 1, m` = - k | (t \<ge> 0)}"

abbreviation "flow \<tau> \<equiv> 
  [y \<leadsto> -k*\<tau>\<^sup>3/6 + m*\<tau>\<^sup>2/2 + v *\<tau> + y, 
  v \<leadsto> -k*\<tau>\<^sup>2/2 + m*\<tau> + v, 
  t \<leadsto> \<tau> + t, 
  m \<leadsto> -k*\<tau> + m]"

(* m' = - k
\<Longrightarrow> m = - k * t + m\<^sub>0 is a line s.t. m = 0 \<longleftrightarrow> t = m\<^sub>0/k
\<Longrightarrow> v = - k * t\<^sup>2/2 + m\<^sub>0 * t = t * (- k * t/2 + m\<^sub>0)
  s.t. v = 0 \<longleftrightarrow> t = 0 \<or> t = 2*m\<^sub>0/k
\<Longrightarrow> y = - k * t\<^sup>3/6 + m\<^sub>0 * t\<^sup>2/2 = (t\<^sup>2 / 2) * (-k*t/3 + m\<^sub>0)
  s.t. y = 0 \<longleftrightarrow> t = 0 \<or> t = 3*m\<^sub>0/k
\<Longrightarrow> (v' = m = 0 \<Longrightarrow> t = m\<^sub>0/k \<Longrightarrow> v = m\<^sub>0\<^sup>2/k - m\<^sub>0\<^sup>2/(2*k) = m\<^sub>0\<^sup>2/(2*k))
  \<and> (y' = v = 0 \<Longrightarrow> t = 0 \<or> t = 2*m\<^sub>0/k \<Longrightarrow> y = (2*m\<^sub>0\<^sup>2/k\<^sup>2) * (m\<^sub>0/3) = 2*m\<^sub>0\<^sup>3/(3*k\<^sup>2)
\<Longrightarrow> v is a concave down parabola with maximum at t=m\<^sub>0/k and v=m\<^sub>0\<^sup>2/(2*k)
  and y is a mostly decreasing cubic line with critical points 
  at t=0 with y=0 and t=2*m\<^sub>0/k with max at t=2*m\<^sub>0/k and y=2*m\<^sub>0\<^sup>3/(3*k\<^sup>2) *)

lemma local_flow_on_rocket:
  "local_flow_on [y \<leadsto> $v, v \<leadsto> $m, t \<leadsto> 1, m \<leadsto> - k] (y +\<^sub>L v +\<^sub>L t +\<^sub>L m) UNIV UNIV flow"
  by local_flow_on_auto

lemma "(m = m\<^sub>0 \<and> m\<^sub>0 > k \<and> t = 0 \<and> v = 0 \<and> y = 0)\<^sub>e \<le> |ode] (y \<le> 2*m\<^sub>0\<^sup>3/(3*k\<^sup>2))"
  apply (wlp_solve "flow")
  using k_ge_1 rocket_arith
  by (expr_simp add: le_fun_def)

lemma "(0 \<le> h \<and> h < 2*m\<^sub>0\<^sup>3/(3*k\<^sup>2) \<and> m = m\<^sub>0 \<and> m\<^sub>0 > k \<and> t = 0 \<and> v = 0 \<and> y = 0)\<^sub>e \<le> |ode\<rangle> (y \<ge> h)"
  using k_ge_1
  by (subst fdia_g_ode_frame_flow[OF local_flow_on_rocket]; expr_simp)
    (auto simp: field_simps power3_eq_cube intro!: exI[of _ "2*m\<^sub>0/k"])

end


locale exponential_evol =
  fixes x :: "real \<Longrightarrow> real^1"
  assumes x_def [simp]: "x \<equiv> vec_lens 1"
begin

\<comment> \<open>Verified with annotated dynamics \<close>

abbreviation "exp_f \<equiv> [x \<leadsto> -x]" (* x>0 -> [{x'=-x}](x>0) *)
abbreviation "exp_flow \<tau> \<equiv> [x \<leadsto> x * exp (- \<tau>)]"

lemma "D (\<lambda>t. exp_flow t s) = (\<lambda>t. exp_f (exp_flow t s)) on {0--t}"
  by (expr_auto, auto intro!: vderiv_intros)

lemma "H{x > 0}(EVOL exp_flow G (\<lambda>s. {t. t \<ge> 0})) {x > 0}"
  by (simp add: fbox_g_evol) expr_auto

\<comment> \<open>Verified with the flow \<close>

lemma local_lipschitz_exp_f: "local_lipschitz UNIV UNIV (\<lambda>t::real. exp_f)"
  apply(simp_all add: local_lipschitz_def lipschitz_on_def, clarsimp)
    apply(rule_tac x="1" in exI, clarsimp, rule_tac x=1 in exI)
  by (clarsimp, expr_auto, simp add: dist_norm norm_vec_def)

lemma local_flow_exp_flow: "local_flow exp_f UNIV UNIV exp_flow"
  apply(unfold_locales)
  apply (auto)
  using local_lipschitz_exp_f apply force
   apply (expr_auto, auto simp: vec_eq_iff intro!: vderiv_intros, expr_auto)
  done

(* x>0 -> [{x'=-x}](x>0) *)
lemma "H{x > 0}(x\<acute>= exp_f & G){x > 0}"
  apply (subst local_flow.fbox_g_ode_subset[OF local_flow_exp_flow])
   apply (simp)
  apply (expr_auto)
  done

end


subsubsection \<open> Blood glucose \<close>

dataspace glucose = 
  constants g\<^sub>m :: real g\<^sub>M :: real
  assumes ge_0: "g\<^sub>m > 0" and ge_gm: "g\<^sub>M > g\<^sub>m"
  variables g :: real

context glucose
begin

abbreviation "ctrl \<equiv> IF g \<le> g\<^sub>m THEN g ::= g\<^sub>M ELSE skip"

abbreviation "dyn \<equiv> {g` = -g}"

abbreviation "flow \<tau> \<equiv> [g \<leadsto> g * exp (- \<tau>)]"

abbreviation "blood_sugar \<equiv> LOOP (ctrl; dyn) INV (g \<ge> 0)"

lemma "H{g \<ge> 0} blood_sugar {g \<ge> 0}"
  apply (wlp_simp) \<comment> \<open> @{term "( |dyn] (0 \<le> $g))"} appears\<close>
  apply (subst fbox_solve[where \<phi>=flow])
     apply ((clarsimp simp: local_flow_on_def)?, unfold_locales; clarsimp?)
       apply (rule c1_local_lipschitz)
  oops

lemma "H{g \<ge> 0} blood_sugar {g \<ge> 0}"
  apply (wlp_expr_solve "flow")
  using ge_gm by force

end


subsubsection \<open> Flight collision \<close>

declare [[literal_variables=false]]

lemma diffInvariant:
  assumes "H{I} g_orbital_on a f (G)\<^sub>e (U)\<^sub>e S t\<^sub>0 {I}" "`P \<longrightarrow> I`"
          "H{P} g_orbital_on a f (G \<and> I)\<^sub>e (U)\<^sub>e S t\<^sub>0 {Q}"
  shows "H{P} g_orbital_on a f (G)\<^sub>e (U)\<^sub>e S t\<^sub>0 {Q}"
  apply (rule diff_cut_on_rule[where C=I])
  using assms weaken apply fastforce
  using assms by simp

method dInv for I :: "'s \<Rightarrow> bool" uses facts =
  (rule diffInvariant[where I="I"],
   (dInduct_mega facts: facts)[1],
   (expr_auto)[1])

lemma hoare_disj_split:
  "H{P} F {R} \<Longrightarrow> H{Q} F {R} \<Longrightarrow> H{P \<or> Q} F {R}"
  unfolding fbox_def by (simp add: le_fun_def)

declare [[literal_variables=true]]

dataspace planar_flight =
  constants
    v\<^sub>o :: real (* own_velocity *)
    v\<^sub>i :: real (* intruder velocity *)
  assumes
    v\<^sub>o_pos: "v\<^sub>o > 0" and
    v\<^sub>i_pos: "v\<^sub>i > 0"
  variables (* Coordinates in reference frame of own ship *)
    x :: real (* Intruder x *)
    y :: real (* Intruder y *)
    \<theta> :: real (* Intruder angle *)
    \<omega> :: real (* Angular velocity *)

context planar_flight
begin

abbreviation "I \<equiv> (v\<^sub>i * sin \<theta> * x - (v\<^sub>i * cos \<theta> - v\<^sub>o) * y
                   > v\<^sub>o + v\<^sub>i)\<^sup>e"

abbreviation "J \<equiv> (v\<^sub>i * \<omega> * sin \<theta> * x - v\<^sub>i * \<omega> * cos \<theta> * y 
                  + v\<^sub>o * v\<^sub>i * cos \<theta> 
                  > v\<^sub>o * v\<^sub>i + v\<^sub>i * \<omega>)\<^sup>e"

definition "ctrl \<equiv> (\<omega> ::= 0; \<questiondown>@I?) \<sqinter> (\<omega> ::= 1; \<questiondown>@J?)"

definition "plant \<equiv> {x` = v\<^sub>i * cos \<theta> - v\<^sub>o + \<omega> * y,
                     y` = v\<^sub>i * sin \<theta> - \<omega> * x,
                     \<theta>` = -\<omega>}"


definition "flight \<equiv> (ctrl; plant)\<^sup>*"

lemma flight_safe: "H{x\<^sup>2 + y\<^sup>2 > 0} flight {x\<^sup>2 + y\<^sup>2 > 0}"
proof -
  have ctrl_post: "H{x\<^sup>2 + y\<^sup>2 > 0} ctrl {(\<omega> = 0 \<and> @I) \<or> (\<omega> = 1 \<and> @J)}"
    unfolding ctrl_def by wlp_full

  have plant_safe_I: "H{\<omega> = 0 \<and> @I} plant {x\<^sup>2 + y\<^sup>2 > 0}"
    unfolding plant_def apply (dInv "($\<omega> = 0 \<and> @I)\<^sup>e", dWeaken)
    using v\<^sub>o_pos v\<^sub>i_pos sum_squares_gt_zero_iff by fastforce

  have plant_safe_J: "H{\<omega> = 1 \<and> @J} plant {x\<^sup>2 + y\<^sup>2 > 0}"
    unfolding plant_def apply (dInv "(\<omega>=1 \<and> @J)\<^sup>e", dWeaken)
    by (metis add.right_neutral cos_le_one distrib_left less_add_same_cancel2 
        linorder_not_le linordered_comm_semiring_strict_class.comm_mult_strict_left_mono 
        mult.right_neutral mult_zero_left not_less_iff_gr_or_eq pos_add_strict 
        sum_squares_gt_zero_iff v\<^sub>i_pos v\<^sub>o_pos)
    (* by (smt (z3) cos_le_one mult_if_delta mult_le_cancel_iff2 
          mult_left_le sum_squares_gt_zero_iff v\<^sub>i_pos v\<^sub>o_pos) *)

    show ?thesis
    unfolding flight_def apply (intro hoare_kstar_inv hoare_kcomp[OF ctrl_post])
    by (rule hoare_disj_split[OF plant_safe_I plant_safe_J])
qed

end


subsubsection \<open>???\<close>

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