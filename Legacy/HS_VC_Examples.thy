(*  Title:       Examples of hybrid systems verifications
    Author:      Jonathan Julián Huerta y Munive, 2020
    Maintainer:  Jonathan Julián Huerta y Munive <jonjulian23@gmail.com>
*)

subsection \<open> Examples \<close>

text \<open> We prove partial correctness specifications of some hybrid systems with our
verification components.\<close>

theory HS_VC_Examples
  imports HS_VC_Spartan 
    "Hybrid-Verification.Real_Arith_Tactics"

begin


subsubsection \<open>Pendulum\<close>

text \<open> The ODEs @{text "x' t = y t"} and {text "y' t = - x t"} describe the circular motion of
a mass attached to a string looked from above. We use @{text "s$1"} to represent the x-coordinate
and @{text "s$2"} for the y-coordinate. We prove that this motion remains circular. \<close>

abbreviation fpend :: "real^2 \<Rightarrow> real^2" ("f")
  where "f s \<equiv> (\<chi> i. if i = 1 then s$2 else -s$1)"

abbreviation pend_flow :: "real \<Rightarrow> real^2 \<Rightarrow> real^2" ("\<phi>")
  where "\<phi> t s \<equiv> (\<chi> i. if i = 1 then s$1 * cos t + s$2 * sin t else - s$1 * sin t + s$2 * cos t)"

\<comment> \<open>Verified with annotated dynamics. \<close>

lemma pendulum_dyn: "(\<lambda>s. r\<^sup>2 = (s$1)\<^sup>2 + (s$2)\<^sup>2) \<le> |EVOL \<phi> G T] (\<lambda>s. r\<^sup>2 = (s$1)\<^sup>2 + (s$2)\<^sup>2)"
  by force

\<comment> \<open>Verified with differential invariants. \<close>

lemma pendulum_inv: "(\<lambda>s. r\<^sup>2 = (s$1)\<^sup>2 + (s$2)\<^sup>2) \<le> |x\<acute>= f & G] (\<lambda>s. r\<^sup>2 = (s$1)\<^sup>2 + (s$2)\<^sup>2)"
  by (auto intro!: diff_inv_rules vderiv_intros)

\<comment> \<open>Verified with the flow. \<close>

lemma local_flow_pend: "local_flow f UNIV UNIV \<phi>"
  apply(unfold_locales, simp_all add: local_lipschitz_def lipschitz_on_def vec_eq_iff, clarsimp)
    apply(rule_tac x="1" in exI, clarsimp, rule_tac x=1 in exI)
    apply(simp add: dist_norm norm_vec_def L2_set_def power2_commute UNIV_2)
  by (auto simp: forall_2 intro!: vderiv_intros)

lemma pendulum_flow: "(\<lambda>s. r\<^sup>2 = (s$1)\<^sup>2 + (s$2)\<^sup>2) \<le> |x\<acute>=f & G] (\<lambda>s. r\<^sup>2 = (s$1)\<^sup>2 + (s$2)\<^sup>2)"
  by (force simp: local_flow.fbox_g_ode_subset[OF local_flow_pend])

no_notation fpend ("f")
        and pend_flow ("\<phi>")


subsubsection \<open> Bouncing Ball \<close>

text \<open> A ball is dropped from rest at an initial height @{text "h"}. The motion is described with
the free-fall equations @{text "x' t = v t"} and @{text "v' t = g"} where @{text "g"} is the
constant acceleration due to gravity. The bounce is modelled with a variable assignment that
flips the velocity. That is, we model it as a completely elastic collision with the ground. We use 
@{text "s$1"} to represent the ball's height and @{text "s$2"} for its velocity. We prove that the 
ball remains above ground and below its initial resting position. \<close>

abbreviation fball :: "real \<Rightarrow> real^2 \<Rightarrow> real^2" ("f")
  where "f g s \<equiv> (\<chi> i. if i = 1 then s$2 else g)"

abbreviation ball_flow :: "real \<Rightarrow> real \<Rightarrow> real^2 \<Rightarrow> real^2" ("\<phi>")
  where "\<phi> g t s \<equiv> (\<chi> i. if i = 1 then g * t ^ 2/2 + s$2 * t + s$1 else g * t + s$2)"

\<comment> \<open>Verified with differential invariants. \<close>

named_theorems bb_real_arith "real arithmetic properties for the bouncing ball."

lemma inv_imp_pos_le[bb_real_arith]:
  assumes "0 > g" and inv: "2 * g * x - 2 * g * h = v * v"
  shows "(x::real) \<le> h"
proof-
  have "v * v = 2 * g * x - 2 * g * h \<and> 0 > g"
    using inv and \<open>0 > g\<close> by auto
  hence obs:"v * v = 2 * g * (x - h) \<and> 0 > g \<and> v * v \<ge> 0"
    using left_diff_distrib mult.commute by (metis zero_le_square)
  hence "(v * v)/(2 * g) = (x - h)"
    by auto
  also from obs have "(v * v)/(2 * g) \<le> 0"
    using divide_nonneg_neg by fastforce
  ultimately have "h - x \<ge> 0"
    by linarith
  thus ?thesis by auto
qed

lemma "diff_inv (\<lambda>s. UNIV) S G (\<lambda>t. f g) t\<^sub>0 (\<lambda>s. 2 * g * s$1 - 2 * g * h - s$2 * s$2 = 0)"
  by (auto intro!: vderiv_intros diff_inv_rules)

lemma bouncing_ball_inv: "g < 0 \<Longrightarrow> h \<ge> 0 \<Longrightarrow>
  (\<lambda>s. s$1 = h \<and> s$2 = 0) \<le>
  |LOOP (
    (x\<acute>=(f g) & (\<lambda> s. s$1 \<ge> 0) DINV (\<lambda>s. 2 * g * s$1 - 2 * g * h - s$2 * s$2 = 0)) ;
    (IF (\<lambda> s. s$1 = 0) THEN (2 ::= (\<lambda>s. - s$2)) ELSE skip))
  INV (\<lambda>s. 0 \<le> s$1 \<and> 2 * g * s$1 - 2 * g * h - s$2 * s$2 = 0)]
  (\<lambda>s. 0 \<le> s$1 \<and> s$1 \<le> h)"
  apply(rule fbox_loopI, simp_all, force, force simp: bb_real_arith)
  by (rule fbox_g_odei) (auto intro!: vderiv_intros diff_inv_rules)

\<comment> \<open>Verified with annotated dynamics. \<close>

lemma inv_conserv_at_ground[bb_real_arith]:
  assumes invar: "2 * g * x = 2 * g * h + v * v"
    and pos: "g * \<tau>\<^sup>2 / 2 + v * \<tau> + (x::real) = 0"
  shows "2 * g * h + (g * \<tau> + v) * (g * \<tau> + v) = 0"
proof-
  from pos have "g * \<tau>\<^sup>2  + 2 * v * \<tau> + 2 * x = 0" 
    by auto
  hence "g * (g * \<tau>\<^sup>2  + 2 * v * \<tau> + 2 * x) = 0"
    by auto
  then have "g\<^sup>2 * \<tau>\<^sup>2  + 2 * g * v * \<tau> + 2 * g * x = 0"
    apply -
    by distribute (mon_simp_vars g x)
  hence "g\<^sup>2 * \<tau>\<^sup>2 + 2 * g * v * \<tau> + v\<^sup>2 + 2 * g * h = 0"
    using invar by (simp add: monoid_mult_class.power2_eq_square)
  hence obs: "(g * \<tau> + v)\<^sup>2 + 2 * g * h = 0"
    by bin_unfold
      (metis (no_types, opaque_lifting) add.commute add.left_commute mult.assoc mult.commute)
  thus "2 * g * h + (g * \<tau> + v) * (g * \<tau> + v) = 0"
    by (simp add: add.commute distrib_right power2_eq_square)
qed

lemma inv_conserv_at_air[bb_real_arith]:
  assumes invar: "2 * g * x = 2 * g * h + v * v"
  shows "2 * g * (g * \<tau>\<^sup>2 / 2 + v * \<tau> + (x::real)) =
  2 * g * h + (g * \<tau> + v) * (g * \<tau> + v)" (is "?lhs = ?rhs")
proof-
  have "?lhs = g\<^sup>2 * \<tau>\<^sup>2 + 2 * g * v * \<tau> + 2 * g * x"
    by(auto simp: algebra_simps semiring_normalization_rules(29))
  also have "... = g\<^sup>2 * \<tau>\<^sup>2 + 2 * g * v * \<tau> + 2 * g * h + v * v" (is "... = ?middle")
    by(subst invar, simp)
  finally have "?lhs = ?middle".
  moreover
  {have "?rhs = g * g * (\<tau> * \<tau>) + 2 * g * v * \<tau> + 2 * g * h + v * v"
    by (simp add: Groups.mult_ac(2,3) semiring_class.distrib_left)
  also have "... = ?middle"
    by (simp add: semiring_normalization_rules(29))
  finally have "?rhs = ?middle".}
  ultimately show ?thesis by auto
qed

lemma bouncing_ball_dyn: "g < 0 \<Longrightarrow> h \<ge> 0 \<Longrightarrow>
  (\<lambda>s. s$1 = h \<and> s$2 = 0) \<le>
  |LOOP (
    (EVOL (\<phi> g) (\<lambda> s. s$1 \<ge> 0) T) ;
    (IF (\<lambda> s. s$1 = 0) THEN (2 ::= (\<lambda>s. - s$2)) ELSE skip))
  INV (\<lambda>s. 0 \<le> s$1 \<and>2 * g * s$1 = 2 * g * h + s$2 * s$2)]
  (\<lambda>s. 0 \<le> s$1 \<and> s$1 \<le> h)"
  by (rule fbox_loopI) (auto simp: bb_real_arith)

\<comment> \<open>Verified with the flow. \<close>

lemma local_flow_ball: "local_flow (f g) UNIV UNIV (\<phi> g)"
  apply(unfold_locales, simp_all add: local_lipschitz_def lipschitz_on_def vec_eq_iff, clarsimp)
    apply(rule_tac x="1/2" in exI, clarsimp, rule_tac x=1 in exI)
    apply(simp add: dist_norm norm_vec_def L2_set_def UNIV_2)
  by (auto simp: forall_2 intro!: vderiv_intros)

lemma bouncing_ball_flow: "g < 0 \<Longrightarrow> h \<ge> 0 \<Longrightarrow>
  (\<lambda>s. s$1 = h \<and> s$2 = 0) \<le>
  |LOOP (
    (x\<acute>=(\<lambda>t. f g) & (\<lambda> s. s$1 \<ge> 0) on (\<lambda>s. UNIV) UNIV @ 0) ;
    (IF (\<lambda> s. s$1 = 0) THEN (2 ::= (\<lambda>s. - s$2)) ELSE skip))
  INV (\<lambda>s. 0 \<le> s$1 \<and>2 * g * s$1 = 2 * g * h + s$2 * s$2)]
  (\<lambda>s. 0 \<le> s$1 \<and> s$1 \<le> h)"
  apply(rule fbox_loopI, simp_all add: local_flow.fbox_g_ode_subset[OF local_flow_ball])
  by (auto simp: bb_real_arith)

no_notation fball ("f")
        and ball_flow ("\<phi>")


subsubsection \<open> Thermostat \<close>

text \<open> A thermostat has a chronometer, a thermometer and a switch to turn on and off a heater.
At most every @{text "t"} minutes, it sets its chronometer to @{term "0::real"}, it registers
the room temperature, and it turns the heater on (or off) based on this reading. The temperature
follows the ODE @{text "T' = - a * (T - U)"} where @{text "U"} is @{text "L \<ge> 0"} when the heater
is on, and @{text "0"} when it is off. We use @{term "1::4"} to denote the room's temperature,
@{term "2::4"} is time as measured by the thermostat's chronometer, @{term "3::4"} is the
temperature detected by the thermometer, and @{term "4::4"} states whether the heater is on
(@{text "s$4 = 1"}) or off (@{text "s$4 = 0"}). We prove that the thermostat keeps the room's
temperature between @{text "Tmin"} and @{text "Tmax"}. \<close>

abbreviation temp_vec_field :: "real \<Rightarrow> real \<Rightarrow> real^4 \<Rightarrow> real^4" ("f")
  where "f a L s \<equiv> (\<chi> i. if i = 2 then 1 else (if i = 1 then - a * (s$1 - L) else 0))"

abbreviation temp_flow :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real^4 \<Rightarrow> real^4" ("\<phi>")
  where "\<phi> a L t s \<equiv> (\<chi> i. if i = 1 then - exp(-a * t) * (L - s$1) + L else
  (if i = 2 then t + s$2 else s$i))"

\<comment> \<open>Verified with the flow. \<close>

lemma norm_diff_temp_dyn: "0 < a \<Longrightarrow> \<parallel>f a L s\<^sub>1 - f a L s\<^sub>2\<parallel> = \<bar>a\<bar> * \<bar>s\<^sub>1$1 - s\<^sub>2$1\<bar>"
proof(simp add: norm_vec_def L2_set_def, unfold UNIV_4, simp)
  assume a1: "0 < a"
  have f2: "\<And>r ra. \<bar>(r::real) + - ra\<bar> = \<bar>ra + - r\<bar>"
    by (metis abs_minus_commute minus_real_def)
  have "\<And>r ra rb. (r::real) * ra + - (r * rb) = r * (ra + - rb)"
    by (metis minus_real_def right_diff_distrib)
  hence "\<bar>a * (s\<^sub>1$1 + - L) + - (a * (s\<^sub>2$1 + - L))\<bar> = a * \<bar>s\<^sub>1$1 + - s\<^sub>2$1\<bar>"
    using a1 by (simp add: abs_mult)
  thus "\<bar>a * (s\<^sub>2$1 - L) - a * (s\<^sub>1$1 - L)\<bar> = a * \<bar>s\<^sub>1$1 - s\<^sub>2$1\<bar>"
    using f2 minus_real_def by presburger
qed

lemma local_lipschitz_temp_dyn:
  assumes "0 < (a::real)"
  shows "local_lipschitz UNIV UNIV (\<lambda>t::real. f a L)"
  apply(unfold local_lipschitz_def lipschitz_on_def dist_norm)
  apply(clarsimp, rule_tac x=1 in exI, clarsimp, rule_tac x=a in exI)
  using assms
  apply(simp add: norm_diff_temp_dyn)
  apply(simp add: norm_vec_def L2_set_def, unfold UNIV_4, clarsimp)
  unfolding real_sqrt_abs[symmetric] by (rule real_le_lsqrt) auto

lemma local_flow_temp: "a > 0 \<Longrightarrow> local_flow (f a L) UNIV UNIV (\<phi> a L)"
  by (unfold_locales, auto intro!: vderiv_intros local_lipschitz_temp_dyn simp: forall_4 vec_eq_iff)

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

lemmas fbox_temp_dyn = local_flow.fbox_g_ode_subset[OF local_flow_temp]

lemma thermostat:
  assumes "a > 0" and "0 < Tmin" and "Tmax < L"
  shows "(\<lambda>s. Tmin \<le> s$1 \<and> s$1 \<le> Tmax \<and> s$4 = 0) \<le>
  |LOOP
    \<comment> \<open>control\<close>
    ((2 ::= (\<lambda>s. 0));(3 ::= (\<lambda>s. s$1));
    (IF (\<lambda>s. s$4 = 0 \<and> s$3 \<le> Tmin + 1) THEN (4 ::= (\<lambda>s.1)) ELSE
    (IF (\<lambda>s. s$4 = 1 \<and> s$3 \<ge> Tmax - 1) THEN (4 ::= (\<lambda>s.0)) ELSE skip));
    \<comment> \<open>dynamics\<close>
    (IF (\<lambda>s. s$4 = 0) THEN (x\<acute>= f a 0 & (\<lambda>s. s$2 \<le> - (ln (Tmin/s$3))/a))
    ELSE (x\<acute>= f a L & (\<lambda>s. s$2 \<le> - (ln ((L-Tmax)/(L-s$3)))/a))) )
  INV (\<lambda>s. Tmin \<le>s$1 \<and> s$1 \<le> Tmax \<and> (s$4 = 0 \<or> s$4 = 1))]
  (\<lambda>s. Tmin \<le> s$1 \<and> s$1 \<le> Tmax)"
  apply(rule fbox_loopI, simp_all add: fbox_temp_dyn[OF assms(1)] le_fun_def)
  using temp_dyn_up_real_arith[OF assms(1) _ _ assms(3), of Tmin]
    and temp_dyn_down_real_arith[OF assms(1,2), of _ Tmax] by auto

no_notation temp_vec_field ("f")
        and temp_flow ("\<phi>")

subsubsection \<open> Tank \<close>

text \<open> A controller turns a water pump on and off to keep the level of water @{text "h"} in a tank
within an acceptable range @{text "hmin \<le> h \<le> hmax"}. Just like in the previous example, after 
each intervention, the controller registers the current level of water and resets its chronometer,
then it changes the status of the water pump accordingly. The level of water grows linearly 
@{text "h' = k"} at a rate of @{text "k = c\<^sub>i-c\<^sub>o"} if the pump is on, and at a rate of 
@{text "k = -c\<^sub>o"} if the pump is off. We use @{term "1::4"} to denote the tank's level of water,
@{term "2::4"} is time as measured by the controller's chronometer, @{term "3::4"} is the
level of water measured by the chronometer, and @{term "4::4"} states whether the pump is on
(@{text "s$4 = 1"}) or off (@{text "s$4 = 0"}). We prove that the controller keeps the level of
water between @{text "hmin"} and @{text "hmax"}. \<close>

abbreviation tank_vec_field :: "real \<Rightarrow> real^4 \<Rightarrow> real^4" ("f")
  where "f k s \<equiv> (\<chi> i. if i = 2 then 1 else (if i = 1 then k else 0))"

abbreviation tank_flow :: "real \<Rightarrow> real \<Rightarrow> real^4 \<Rightarrow> real^4" ("\<phi>")
  where "\<phi> k \<tau> s \<equiv> (\<chi> i. if i = 1 then k * \<tau> + s$1 else 
  (if i = 2 then \<tau> + s$2 else s$i))"

abbreviation tank_guard :: "real \<Rightarrow> real \<Rightarrow> real^4 \<Rightarrow> bool" ("G")
  where "G Hm k s \<equiv> s$2 \<le> (Hm - s$3)/k"

abbreviation tank_loop_inv :: "real \<Rightarrow> real \<Rightarrow> real^4 \<Rightarrow> bool" ("I")
  where "I hmin hmax s \<equiv> hmin \<le> s$1 \<and> s$1 \<le> hmax \<and> (s$4 = 0 \<or> s$4 = 1)"

abbreviation tank_diff_inv :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real^4 \<Rightarrow> bool" ("dI")
  where "dI hmin hmax k s \<equiv> s$1 = k * s$2 + s$3 \<and> 0 \<le> s$2 \<and> 
    hmin \<le> s$3 \<and> s$3 \<le> hmax \<and> (s$4 =0 \<or> s$4 = 1)"

lemma local_flow_tank: "local_flow (f k) UNIV UNIV (\<phi> k)"
  apply (unfold_locales, unfold local_lipschitz_def lipschitz_on_def, simp_all, clarsimp)
  apply(rule_tac x="1/2" in exI, clarsimp, rule_tac x=1 in exI)
  apply(simp add: dist_norm norm_vec_def L2_set_def, unfold UNIV_4)
  by (auto intro!: vderiv_intros simp: vec_eq_iff)

lemma tank_arith:
  assumes "0 \<le> (\<tau>::real)" and "0 < c\<^sub>o" and "c\<^sub>o < c\<^sub>i"
  shows "\<forall>\<tau>\<in>{0..\<tau>}. \<tau> \<le> - ((hmin - y) / c\<^sub>o) \<Longrightarrow>  hmin \<le> y - c\<^sub>o * \<tau>"
    and "\<forall>\<tau>\<in>{0..\<tau>}. \<tau> \<le> (hmax - y) / (c\<^sub>i - c\<^sub>o) \<Longrightarrow>  (c\<^sub>i - c\<^sub>o) * \<tau> + y \<le> hmax"
    and "hmin \<le> y \<Longrightarrow> hmin \<le> (c\<^sub>i - c\<^sub>o) * \<tau> + y"
    and "y \<le> hmax \<Longrightarrow> y - c\<^sub>o * \<tau> \<le> hmax"
  apply(simp_all add: field_simps le_divide_eq assms)
  using assms apply (meson add_mono less_eq_real_def mult_left_mono)
  using assms by (meson add_increasing2 less_eq_real_def mult_nonneg_nonneg) 

lemma tank_flow:
  assumes "0 < c\<^sub>o" and "c\<^sub>o < c\<^sub>i"
  shows "I hmin hmax \<le>
  |LOOP 
    \<comment> \<open>control\<close>
    ((2 ::=(\<lambda>s.0));(3 ::=(\<lambda>s. s$1));
    (IF (\<lambda>s. s$4 = 0 \<and> s$3 \<le> hmin + 1) THEN (4 ::= (\<lambda>s.1)) ELSE 
    (IF (\<lambda>s. s$4 = 1 \<and> s$3 \<ge> hmax - 1) THEN (4 ::= (\<lambda>s.0)) ELSE skip));
    \<comment> \<open>dynamics\<close>
    (IF (\<lambda>s. s$4 = 0) THEN (x\<acute>= f (c\<^sub>i-c\<^sub>o) & (G hmax (c\<^sub>i-c\<^sub>o))) 
     ELSE (x\<acute>= f (-c\<^sub>o) & (G hmin (-c\<^sub>o)))) ) INV I hmin hmax]  
  I hmin hmax"
  apply(rule fbox_loopI, simp_all add: le_fun_def)
  apply(clarsimp simp: le_fun_def local_flow.fbox_g_ode_subset[OF local_flow_tank])
  using assms tank_arith[OF _ assms] by auto

no_notation tank_vec_field ("f")
        and tank_flow ("\<phi>")
        and tank_loop_inv ("I")
        and tank_diff_inv ("dI")
        and tank_guard ("G")

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
  have key: "diff_inv (\<lambda>s. UNIV) UNIV G 
  (\<lambda>t s. \<chi> i. if i = 1 then A*(s$1)^2+B*(s$1) else A*(s$2)*(s$1)+B*(s$2)) 0 (\<lambda>s. s$1 + s$2 = 0)"
  proof(clarsimp simp: diff_inv_eq ivp_sols_def forall_2)
    fix X::"real\<Rightarrow>real^2" and t::real
    let "?c" = "(\<lambda>t.  X t$1 + X t$2)"
    assume init: "?c 0 = 0"
      and D1: "D (\<lambda>t. X t$1) = (\<lambda>t. A * (X t$1)\<^sup>2 + B * X t$1) on UNIV"
      and D2: "D (\<lambda>t. X t$2) = (\<lambda>t. A * X t$2 * X t$1 + B * X t$2) on UNIV"
    hence "D ?c = (\<lambda>t. ?c t * (A * (X t$1) + B)) on UNIV"
      by (auto intro!: vderiv_intros simp: field_simps)
    hence "D ?c = (\<lambda>t. (A * X t$1 + B) * (X t$1 + X t$2)) on {0--t}"
      using has_vderiv_on_subset[OF _ subset_UNIV[of "{0--t}"]] by (simp add: mult.commute)
    moreover have "continuous_on UNIV (\<lambda>t. A * (X t$1) + B)"
      apply(rule vderiv_on_continuous_on)
      using D1 by (auto intro!: vderiv_intros simp: field_simps)
    moreover have "D (\<lambda>t. 0) = (\<lambda>t. (A * X t$1 + B) * 0) on {0--t}"
      by (auto intro!: vderiv_intros)
    moreover note picard_lindeloef.ivp_unique_solution[OF 
      picard_lindeloef_first_order_linear[OF UNIV_I open_UNIV is_interval_univ calculation(2)] 
      UNIV_I is_interval_closed_segment_1 subset_UNIV _ 
      ivp_solsI[of ?c]
      ivp_solsI[of "\<lambda>t. 0"], of t "\<lambda>s. 0" 0 "\<lambda>s. t" 0]
    ultimately show "X t$1 + X t$2 = 0"
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

abbreviation darboux_ineq_df :: "real \<times> (real ^ 2) \<Rightarrow> (real ^ 2) \<Rightarrow>\<^sub>L (real ^ 2)" ("df")
  where "df p \<equiv> (case p of (t,x) \<Rightarrow> Blinfun (\<lambda>s. (\<chi> i::2. if i=1 then 2 * (s$1) * (x$1) else 
  x$2 * s$1 + s$2 * x$1 + 2 * s$1 * x$1)))"

thm c1_implies_local_lipschitz c1_local_lipschitz


lemma picard_lindeloef_darboux_ineq: "picard_lindeloef (\<lambda>t. f) UNIV {s. s$1 + s$2 > 0} 0"
  apply(unfold_locales, simp_all)
  prefer 2
   apply(rule_tac f'=df in c1_implies_local_lipschitz)
      apply (clarsimp simp: has_derivative_coordinate)
  subgoal for s i
    apply(cases "i = 1")
     apply clarsimp
     apply(subst Blinfun_inverse, clarsimp)
      apply(subst bounded_linear_coordinate, clarsimp)
    subgoal for j
    using exhaust_2[of j] by (auto intro!: bounded_linear_intros)
      apply(auto intro!: derivative_eq_intros)[1]
  apply(subst Blinfun_inverse, clarsimp)
   apply(subst bounded_linear_coordinate)
   apply (clarsimp simp: has_derivative_coordinate)
 subgoal for j
    using exhaust_2[of j] by (auto intro!: bounded_linear_intros)
  by (auto intro!: derivative_eq_intros)[1]
  apply (auto intro!: continuous_intros)
  sorry

lemma darboux_flow_ivp: "(\<lambda>t. \<phi> t s) \<in> Sols (\<lambda>s. {t. 0 \<le> t \<and> t * s$1 < 1}) UNIV (\<lambda>t. f) 0 s"
  by (rule ivp_solsI) (auto intro!: vderiv_intros 
      simp: forall_2 power2_eq_square add_divide_distrib power_divide vec_eq_iff)

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
      by (metis False add_0 assms(3) less_diff_eq ln_le_zero_iff mult_le_0_iff nle_le)
  qed
  hence "s\<^sub>1 + s\<^sub>2 - s\<^sub>1 * ln (1 - t * s\<^sub>1) \<ge> s\<^sub>1 + s\<^sub>2"
    by linarith
  hence "(s\<^sub>1 + s\<^sub>2 - s\<^sub>1 * ln (1 - t * s\<^sub>1))/(1 - t * s\<^sub>1) \<ge> (s\<^sub>1 + s\<^sub>2)/(1 - t * s\<^sub>1)"
    using \<open>t * s\<^sub>1 < 1\<close> by (simp add: \<open>0 \<le> s\<^sub>1 + s\<^sub>2\<close> divide_le_cancel)
  also have "(s\<^sub>1 + s\<^sub>2)/(1 - t * s\<^sub>1) \<ge> 0"
    using \<open>t * s\<^sub>1 < 1\<close> by (simp add: \<open>0 \<le> s\<^sub>1 + s\<^sub>2\<close>)
  ultimately show ?thesis
    by (metis (full_types) add_diff_eq add_divide_distrib order_trans)
qed

(* x+z>=0 -> [{x'=x^2, z' = z*x+y & y = x^2}] x+z>=0 *)
(* x' + z' \<ge> 0 \<longleftrightarrow> x^2 + z*x + x^2 \<ge> 0*)
lemma "(\<lambda>s::real^2. s$1 + s$2 \<ge> 0) \<le> 
  |EVOL \<phi> (\<lambda>s. y = (s$1)^2) (\<lambda>s. {t. 0 \<le> t \<and> t * s$1 < 1})]
  (\<lambda>s. s$1 + s$2 \<ge> 0)"
  apply(subst fbox_g_evol, simp_all add: le_fun_def)
  using darboux_ineq_arith by smt

no_notation darboux_ineq_flow2 ("\<phi>")
        and darboux_ineq_f ("f")

subsection \<open> Dynamics: Fractional Darboux equality \<close>

(* x+z=0 -> [{x'=(A*y+B()*x)/z^2, z' = (A*x+B())/z & y = x^2 & z^2 > 0}] x+z=0 *)
(* x' + z' = (A*y+B*x)/z^2 + (A*x+B)/z = (A*y+B*x+A*x*z+B*z)/z^2 = (x*(A*x+B)+z*(A*x+B))/z^2 *)
lemma "0 \<le> t \<Longrightarrow> (\<lambda>s::real^3. s$1 + s$3 = 0) \<le>
  |x\<acute>= (\<lambda> s. (\<chi> i::3. if i=1 then (A*(s$2)+B*(s$1))/(s$3)\<^sup>2 else (if i = 3 then (A*(s$1)+B)/s$3 else 0))) & (\<lambda>s. (s$2) = (s$1)^2 \<and> (s$3)^2 > 0)] 
  (\<lambda>s. s$1 + s$3 = 0)"
proof-
  have "diff_inv (\<lambda>s. Collect ((\<le>) 0)) UNIV (\<lambda>s. s$2 = (s$1)\<^sup>2 \<and> s$3 \<noteq> 0) 
  (\<lambda>t s. \<chi> i::3. if i = 1 then (A*(s$2)+B*(s$1))/(s$3)\<^sup>2 else if i = 3 then (A*(s$1)+B)/s$3 else 0) 
  0 (\<lambda>s::real^3. s$1 + s$3 = 0)"
  proof(clarsimp simp: diff_inv_eq ivp_sols_def forall_3)
    fix X::"real\<Rightarrow>real^3" and t::real
    let "?c" = "(\<lambda>t.  X t$1 + X t$3)"
    assume init: "?c 0 = 0" and "t \<ge> 0"
      and guard: "\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> X \<tau>$2 = (X \<tau>$1)\<^sup>2 \<and> X \<tau>$3 \<noteq> 0"
      and D1: "D (\<lambda>t. X t$1) = (\<lambda>t. (A * (X t$2) + B * X t$1)/(X t$3)\<^sup>2) on Collect ((\<le>) 0)"
      and D2: "D (\<lambda>t. X t$2) = (\<lambda>t. 0) on Collect ((\<le>) 0)"
      and D3: "D (\<lambda>t. X t$3) = (\<lambda>t. (A * X t$1 + B)/(X t$3)) on Collect ((\<le>) 0)"
    have "D ?c = (\<lambda>t. (A * (X t$2) + B * X t$1)/(X t$3)\<^sup>2 + (A * X t$1 + B)/(X t$3)) on {0--t}"
      apply(rule_tac S="Collect ((\<le>) 0)" in has_vderiv_on_subset)
      using \<open>t \<ge> 0\<close> by (auto simp: closed_segment_eq_real_ivl intro!: vderiv_intros D1 D3)
    hence "D ?c = (\<lambda>t. (A * X t$1 + B)/(X t$3)\<^sup>2 * ?c t) on {0--t}"
      apply(rule has_vderiv_on_eq_rhs)
      using guard \<open>t \<ge> 0\<close>
      using segment_open_subset_closed
      by (auto simp: field_simps closed_segment_eq_real_ivl)
    moreover have "continuous_on {0--t} (\<lambda>t. (A * X t$1 + B)/(X t$3)\<^sup>2)"
      apply(rule vderiv_on_continuous_on)
      apply(rule vderiv_intros)
      using guard segment_open_subset_closed \<open>t \<ge> 0\<close> apply (force simp: closed_segment_eq_real_ivl)
        apply(intro vderiv_intros, rule vderiv_intros)
      apply(rule has_vderiv_on_subset[OF D1])
      using \<open>t \<ge> 0\<close> apply(simp add: closed_segment_eq_real_ivl subset_eq, force)
         apply(rule vderiv_intros, force)
      apply(rule vderiv_intros,simp)
      apply(rule has_vderiv_on_subset[OF D3])
      using \<open>t \<ge> 0\<close> by (simp_all add: closed_segment_eq_real_ivl subset_eq)
    moreover have "D (\<lambda>t. 0) = (\<lambda>t. (A * X t$1 + B)/(X t$3)\<^sup>2 * 0) on {0--t}"
      by (auto intro!: vderiv_intros)   
    (*moreover note picard_lindeloef.unique_solution_general[OF 
        picard_lindeloef_first_order_linear[OF _ _ _ calculation(2)] _ _ _ _ _ this _ _ calculation(1)]
   *)
    thm picard_lindeloef.unique_solution_closed_ivl
    thm picard_lindeloef.unique_solution[of "(\<lambda>t. (*) ((A * X t$1 + B) / (X t$3)\<^sup>2))" _ _ 0]
    thm picard_lindeloef_first_order_linear[OF _ _ _ calculation(2)]
    moreover note picard_lindeloef.unique_solution_closed_ivl[OF 
        picard_lindeloef_first_order_linear[OF _ _ _ calculation(2)] this _ _ _ calculation(1)]
    ultimately show "X t$1 + X t$3 = 0"
      using init by auto
        (* continuous because of guard need to change assumptions of picard_lindeloef *)
        (* correct interval of existence or differentiabe \<Longrightarrow> lipschitz *)
  qed
  thus ?thesis
    by auto
qed

subsection \<open> STTT Tutorial: Example 9b \<close>

abbreviation f9 :: "real ^ 3 \<Rightarrow> real ^ 3" 
  where "f9 \<equiv> (\<lambda>s. \<chi> i. if i = 1 then s $ 2 else if i = 2 then - 2 * (s $ 1 - s $ 3) - 3 * s $ 2 else 0)"

(* { x' = v, v' = -Kp*(x-xr) - Kd*v & v >= 0 } *)
term "(\<lambda>(t::real) (s::real^3). \<chi> i::3. if i = 1 then s $ 2 else if i = 2 then - 2 * (s $ 1 - s $ 3) - 3 * s $ 2 else 0)"
lemma "local_lipschitz UNIV UNIV (\<lambda>(t::real). f9)"
  apply(rule_tac \<DD>=f9 in c1_local_lipschitz; clarsimp?)
  apply (clarsimp simp: has_derivative_coordinate)
  subgoal for s i
    using exhaust_3[of i]
    by (auto intro!: derivative_eq_intros)
  apply(rule_tac f'="\<lambda>t. f9" in has_derivative_continuous_on, clarsimp)
  apply (clarsimp simp: has_derivative_coordinate)
  subgoal for s i
    using exhaust_3[of i]
    by (auto intro!: derivative_eq_intros)
  done

end