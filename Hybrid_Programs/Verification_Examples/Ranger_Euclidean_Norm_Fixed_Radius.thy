theory Ranger_Euclidean_Norm_Fixed_Radius
  imports "Hybrid-Verification.Hybrid_Verification" (* "Explorer.Explorer" *)
begin

(* setup Explorer_Lib.switch_to_quotes *)

thm snd_lens_plus

method framed_deriv = (simp only: framed_derivs ldifferentiable lens usubst usubst_eval bounded_linear_intros fst_lens_plus snd_lens_plus sublens_refl lens_plus_right_sublens lens_quotient_id lens_comp_left_id plus_vwb_lens SEXP_apply arithmetic_simps of_nat_numeral cont_lens_fst cont_lens_snd cont_lens.bounded_linear_get lens_quotient_plus_den2 plus_pres_lens_indep plus_pres_lens_indep')

unbundle Hybrid_Program_Syntax
unbundle no lattice_syntax

declare [[literal_variables=false]]

declare [[simproc del: ring_le_cancel_numeral_factor]]

lemma cauchy_schwarz_heading_bound:
  fixes v u :: "real^2"
  assumes "\<parallel>u\<parallel> = 1"
  shows "v \<bullet> u \<le> \<parallel>v\<parallel>"
proof -
  have "v \<bullet> u \<le> \<parallel>v\<parallel> * \<parallel>u\<parallel>"
    using norm_cauchy_schwarz by blast
  thus ?thesis using assms by simp
qed

lemma cauchy_schwarz_squared:
  fixes v u :: "real^2"
  assumes "\<parallel>u\<parallel> = 1"
  shows "(v \<bullet> u)\<^sup>2 \<le> \<parallel>v\<parallel>\<^sup>2"
proof -
  have "\<bar>v \<bullet> u\<bar> \<le> \<parallel>v\<parallel> * \<parallel>u\<parallel>" by (rule Cauchy_Schwarz_ineq2)
  hence "\<bar>v \<bullet> u\<bar> \<le> \<parallel>v\<parallel>" using assms by simp
  hence "\<bar>v \<bullet> u\<bar>\<^sup>2 \<le> \<parallel>v\<parallel>\<^sup>2" by (rule power_mono) simp
  thus ?thesis by simp
qed

abbreviation (input) e1 :: "real^2" where "e1 \<equiv> axis 1 1"
abbreviation (input) e2 :: "real^2" where "e2 \<equiv> axis 2 1"

lemma nat_of_2_2 [simp]: "(nat_of (2 :: 2)) = 0"
  by (metis exhaust_2 nat_of_0 rel_simps(93))

definition rot :: "real^2 \<Rightarrow> real^2" where
  "rot v = (inner v e1) *\<^sub>R e2 - (inner v e2) *\<^sub>R e1"  

lemma rot_Vec: "rot (Vector[x, y]) = Vector[y, -x]"
  by (simp add: rot_def axis_Vec inner_Vec scaleR_Vec minus_Vec numeral_2_eq_2 ezlist_def)

lemma rot_Vec': "rot x = Vector[x $ 1, - x $ 0]"
  apply (cases rule: Vec2_caseE[of x])
  apply (simp add: rot_Vec Vec_lookup')
  done

lemma differentiable_Vec2 [ldifferentiable]:
  assumes "differentiable\<^bsub>x\<^esub> expr1" "differentiable\<^bsub>x\<^esub> expr2"
  shows "differentiable\<^bsub>x\<^esub> (Vector[expr1,expr2])"
  apply (rule differentiable_Vec)
  apply simp
   apply (simp add: numerals(2))
  subgoal for i
    apply (subgoal_tac "i = 0 \<or> i = 1")
    apply (insert assms)
     apply auto
    done
  done



lemma linear_right_angle_rotation: "linear rot"
  unfolding rot_def
  by (simp add: inner_left_distrib linearI scaleR_right_diff_distrib vector_space_assms(2))

lemma norm_rot [simp]: "\<parallel>rot x\<parallel> = \<parallel>x\<parallel>"
proof -
  have norm_sq_eq: "(norm x)\<^sup>2 = x \<bullet> x"
    by (simp add: power2_norm_eq_inner)
    
  have rot_norm_sq_eq: "(norm (rot x))\<^sup>2 = (rot x) \<bullet> (rot x)"
    by (simp add: power2_norm_eq_inner)

  have "x \<bullet> x = (x$1)\<^sup>2 + (x$2)\<^sup>2"
    by (simp add: inner_vec_def UNIV_2 power2_eq_square)

  moreover have "(rot x) \<bullet> (rot x) = (x$1)\<^sup>2 + (x$2)\<^sup>2"
    unfolding rot_def inner_vec_def UNIV_2 
    by (simp add: power2_eq_square, simp add:  cart_eq_inner_axis inner_axis_axis)

  ultimately have squared_equal: "(norm (rot x))\<^sup>2 = (norm x)\<^sup>2"
    by (simp add: power2_norm_eq_inner)

  \<comment> \<open>Step 4: Cancel out the squares natively using the non-negativity of norms\<close>
  show ?thesis
    using squared_equal by auto
qed

lemma self_dot_rot [simp]: "x \<bullet> rot(x) = 0" "rot(x) \<bullet> x = 0"
  by (simp_all add: inner_simps(3) inner_commute rot_def)

lemma rot_rot [simp]: "rot (rot x) = -x"
  by (cases rule: Vec2_caseE[of x], simp add: rot_Vec uminus_Vec numeral_2_eq_2 ezlist_simp)

lemma rot_scaleR [simp]: "rot (n *\<^sub>R x) = n *\<^sub>R rot x"
  using linear_cmul linear_right_angle_rotation by blast

lemma rot_skew_sym: "x \<bullet> rot(y) = -rot(x) \<bullet> y"
  by (simp add: inner_commute inner_simps(3) rot_def)

lemma norm_norm_1: "\<parallel>x\<parallel> * \<parallel>x\<parallel> = 1 \<Longrightarrow> \<parallel>x\<parallel> = 1"
  by (metis abs_norm_cancel inner_real_def norm_eq_1 real_norm_def)

lemma Vec2_decomp: "x = Vector[x$0, x$1]"
  by (cases rule: Vec2_caseE[of x], simp add: Vec_lookup')

lemma Vec2_eq_iff: "Vector[x\<^sub>1, x\<^sub>2] = Vector[y\<^sub>1, y\<^sub>2] \<longleftrightarrow> x\<^sub>1 = y\<^sub>1 \<and> x\<^sub>2 = y\<^sub>2"
  by (metis (no_types, opaque_lifting) Vec2_decomp exhaust_2 rel_simps(92)
      vector_2(1,2))
  
lemma differentiable_rot [ldifferentiable]:
  assumes "differentiable\<^bsub>x\<^esub> expr within S when G"  
  shows "differentiable\<^bsub>x\<^esub> (rot expr) within S when G"
  by (simp add: assms rot_def ldifferentiable)

lemma lframeD_rot [framed_derivs]:
  fixes x :: "'c::{real_normed_vector, real_inner} \<Longrightarrow> 'v"
  assumes "vwb_lens x" "differentiable\<^bsub>x\<^esub> expr"
  shows "\<D>\<^bsub>x\<^esub>\<langle>\<sigma>\<rangle> (rot expr) = (rot (\<D>\<^bsub>x\<^esub>\<langle>\<sigma>\<rangle> expr))\<^sub>e"
  using assms by (simp add: rot_def framed_derivs assms ldifferentiable)

lemma algebraic_error_collapse:
  fixes \<theta> \<omega> :: real
  shows "2 * (d$0 - cos \<theta>) * (-\<omega> * d$1 - (-sin \<theta> * \<omega>)) + 
         2 * (d$1 - sin \<theta>) * (\<omega> * d$0 - (cos \<theta> * \<omega>)) = 0"
  by algebra

lemma unicycle_derivative_induction:
  fixes r\<^sub>0 S t \<omega> s :: real
  assumes "s = r\<^sub>0 * \<omega>"                (* Kinematic coupling *)
    and "s \<le> S"                       (* Max speed constraint *)
    and "s \<ge> 0"  "r\<^sub>0 > 0" "t \<ge> 0" (* Non-negative conditions *)
    and "\<parallel>d\<parallel> = 1"                   (* d is a unit vector *)
    and "d\<^sub>0 \<bullet> d\<^sub>0 = 1"                 (* d0 is a unit vector *)
    and "r\<^sub>0 \<le> S * t"                  (* Crossover/Linear distance condition *)
  shows "- (r\<^sub>0\<^sup>2 * (2 * (\<omega> * (rot (d) \<bullet> d\<^sub>0)))) \<le> 2 * S * (t * S)"
proof -
  have rot: "-(rot d \<bullet> d\<^sub>0) = d \<bullet> rot d\<^sub>0"
    by (metis inner_minus_left rot_skew_sym) 

  have d_bound: "d \<bullet> rot d\<^sub>0 \<le> 1"
    by (metis assms(6,7) cauchy_schwarz_heading_bound norm_eq_1 norm_rot)

  have lhs_eq: "- (r\<^sub>0\<^sup>2 * (2 * (\<omega> * (rot (d) \<bullet> d\<^sub>0)))) = 2 * r\<^sub>0 * (r\<^sub>0 * \<omega>) * (- (rot d \<bullet> d\<^sub>0))"
    by (simp add: algebra_simps power2_eq_square)

  also have "... = 2 * r\<^sub>0 * (r\<^sub>0 * \<omega>) * (d \<bullet> rot d\<^sub>0)"
    by (simp add: rot)

  also have "... = 2 * r\<^sub>0 * s * (d \<bullet> rot d\<^sub>0)"
    using assms(1) by simp
  
  also have "... \<le> 2 * r\<^sub>0 * s"
    using assms(3) assms(4) `d \<bullet> rot d\<^sub>0 \<le> 1`
    by (metis assms(5) less_imp_le mult_left_le mult_sign_intros(1) zero_le_numeral) 
    
  also have "... \<le> 2 * (S * t) * S"
    using assms(2) assms(7) assms(3) assms(4)
    by (metis assms(8) less_eq_real_def mult_mono semiring_norm(63)
        zero_le_numeral)
    
  also have "... = S * (S * (t * 2))"
    by (simp add: algebra_simps)

  also have "... = 2 * S * (t * S)"
    by simp

  finally show ?thesis . 
qed

declare [[literal_variables]]

datatype 'st phase = enter 'st | active 'st

datatype state = Moving | Turning

dataspace obstacle_avoidance =
  constants
    A :: real \<comment> \<open> The maximum acceleration \<close>
    b :: real \<comment> \<open> The maximum braking acceleration \<close>
    \<epsilon> :: real \<comment> \<open> The maximum sample period for the dynamics, in seconds. \<close>
    S :: real \<comment> \<open> The maximum speed of the robot \<close>
    \<Omega> :: real
    lv :: real \<comment> \<open> The linear velocity set-point \<close>
    av :: real \<comment> \<open> The angular velocity set-point \<close>
  assumes
    A_min: "A \<ge> 0" and
    b_min: "b > 0" and
    eps_min: "0 < \<epsilon>" and
    eps_max: "\<epsilon> < 1" and
    S_min: "S > 0" and
    \<Omega>_min: "\<Omega> \<ge> 0" 
  variables
    clock :: real \<comment> \<open> A global clock used to time seconds \<close> 
    t :: real \<comment> \<open> The time that elapsed in the previous physical evolution \<close>
    p :: "real ^ 2"
    sp :: real
    a :: real
    \<omega> :: real
    d :: "real ^ 2"
    r :: real
    ob :: "(real ^ 2) ^ ('n::finite)" \<comment> \<open> A vector of obstacle coordinates \<close>
    v :: "real ^ 2"
    rc_st :: state
    MBC :: nat \<comment> \<open> The number of time units that have passed since the clock reset. The time unit is seconds. \<close>
    obstacle :: bool

context obstacle_avoidance
begin

text \<open> The centre of the arc circle \<close>

expression c is "p + r *\<^sub>R rot(d)"

definition ctrl :: "'st prog \<Rightarrow> ('st \<Rightarrow> bool) \<Rightarrow> 'st prog" where
  "ctrl drive safe = 
    (a := -b
     \<sqinter> \<questiondown>sp = 0? ; a := 0 ; \<omega> := 0
     \<sqinter> drive ; \<omega> := ? ; \<questiondown>-\<Omega> \<le> \<omega> \<and> \<omega> \<le> \<Omega>? ; r := ? ; \<questiondown>(r \<noteq> 0 \<longrightarrow> r * \<omega> = sp) \<and> @safe?) ;
    t := 0"

text \<open> The linear velocity can be a minimum of zero, so the robot cannot start reversing. \<close>

definition dyn :: "'st prog" where
"dyn = {clock` = 1, t` = 1, p` = sp *\<^sub>R d, sp` = a, d` = \<omega> *\<^sub>R rot d, \<omega>` = (if r = 0 then 0 else a / r) 
       | 0 \<le> sp \<and> sp \<le> S \<and> t \<le> \<epsilon>}"

(* , \<omega>` = a / r *)

definition "mapping = (IF clock \<ge> 1 THEN MBC := MBC + 1; clock := 0)
                      ; obstacle := (\<exists> i. \<parallel>p - ob $ i\<parallel>\<^sub>\<infinity> \<le> (sp\<^sup>2 / (2*b)) + (a/b + 1) * (a/2 * \<epsilon>\<^sup>2 + \<epsilon> * sp))"

text \<open> The safety condition is used to specify safe velocities. It has two components: 
  (1) the distance travelled when braking from the current speed;
  (2) the maximum distance travelled before the next controller cycle. \<close>

expression safe is "\<forall> i. \<parallel>p - ob $ i\<parallel>\<^sub>\<infinity> > (sp\<^sup>2 / (2*b)) + (a/b + 1) * (a/2 * \<epsilon>\<^sup>2 + \<epsilon> * sp)"

definition "model1 = (ctrl (a := A) safe ; dyn)\<^sup>*"

text \<open> We continue to accelerate until we have passed the velocity set point, or brake if we're going too fast. \<close>

definition "move \<omega>' sp' = (\<omega> := \<omega>'; (IF sp < sp' THEN a := A ELSE IF sp > sp' THEN a := -b ELSE a := 0))"

definition "stop = IF sp > 0 THEN a := -b ELSE sp := 0"

definition ranger_stm :: "'st prog" where
  "ranger_stm = (\<questiondown>rc_st = Moving? ; move lv 0 ; IF obstacle THEN MBC := 0 ; stop ; rc_st := Turning) 
              \<sqinter> (\<questiondown>rc_st = Turning? ; move 0 av ; IF MBC \<ge> pi / av THEN rc_st := Moving)"

definition ctrl_ranger :: "'st prog" where 
  "ctrl_ranger = ranger_stm ; t := 0"

definition "ranger = (ctrl_ranger ; dyn ; mapping)\<^sup>*"

text \<open> The invariant for the dynamics. It sets some healthiness conditions, determines the speed,
  and places a maximum bound on the distance travelled by the robot (@{term "(\<parallel>p - opc\<parallel>\<^sub>\<infinity>)\<^sub>e"}
  during dynamical evolution. 

  We give several versions of this. The first is when the robot is moving in a straight line.
\<close>

definition \<Psi>\<^sub>1 :: "(real ^ 2) \<Rightarrow> (real ^ 2 ^ 'n) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real^2 \<Rightarrow> 'st \<Rightarrow> bool" where
 "\<Psi>\<^sub>1 p\<^sub>0 ob\<^sub>0 a\<^sub>0 s\<^sub>0 od =
  (ob = ob\<^sub>0 \<and> a = a\<^sub>0 \<and> 0 \<le> s\<^sub>0 \<and> r = 0 \<and> \<omega> = 0 \<and> d = od
    \<and> 0 \<le> sp \<and> 0 \<le> t  \<and> \<parallel>d\<parallel>\<^sup>2 = 1 \<and> \<parallel>d\<parallel> = 1 \<and> sp = s\<^sub>0 + a * t
    \<and> p = p\<^sub>0 + (s\<^sub>0 * t + a\<^sub>0 * t\<^sup>2 / 2) *\<^sub>R od
    \<and> \<parallel>p - p\<^sub>0\<parallel> \<le> t * (sp - a * t/2))\<^sup>e"

expr_constructor \<Psi>\<^sub>1 

expression safety_condition is "\<forall> i. \<parallel>p - ob $ i\<parallel> > 0"

notation safety_condition ("\<psi>")

expression loop_invariant is 
  "(\<forall> i. \<parallel>p - ob $ i\<parallel>\<^sub>\<infinity> > sp^2/(2*b)) \<and> 0 \<le> sp \<and> \<parallel>d\<parallel> = 1"

notation loop_invariant ("\<phi>")

expression initial_condition is "sp = 0 \<and> (\<forall> i. \<parallel>p - ob $ i\<parallel>\<^sub>\<infinity> > 0) \<and> \<parallel>d\<parallel> = 1"

notation initial_condition ("\<Phi>")

definition \<Psi>\<^sub>2 :: "(real ^ 2) \<Rightarrow> (real ^ 2 ^ 'n) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real \<Rightarrow> real \<Rightarrow> 'st \<Rightarrow> bool" where
 "\<Psi>\<^sub>2 p\<^sub>0 ob\<^sub>0 a\<^sub>0 sp\<^sub>0 d\<^sub>0 c\<^sub>0 r\<^sub>0 \<omega>\<^sub>0 =
  (ob = ob\<^sub>0 \<and> a = a\<^sub>0 \<and> 0 \<le> sp\<^sub>0 \<and> r = r\<^sub>0 \<and> r\<^sub>0 > 0 \<and> (c\<^sub>0 - p\<^sub>0)\<bullet>(c\<^sub>0 - p\<^sub>0) = r\<^sub>0\<^sup>2 \<and> \<parallel>c\<^sub>0 - p\<^sub>0\<parallel> = r
    \<and> 0 \<le> sp \<and> 0 \<le> t  \<and> \<parallel>d\<parallel>\<^sup>2 = 1 \<and> \<parallel>d\<parallel> = 1 \<and> d\<^sub>0 \<bullet> d\<^sub>0 = 1
    \<and> r * \<omega> = sp
    \<and> (p - c)\<bullet>(p - c) = r\<^sub>0\<^sup>2
    \<and> r\<^sub>0 \<le> S * t 
    \<and> r\<^sub>0\<^sup>2 * (2 - 2*(d \<bullet> d\<^sub>0)) \<le> (t * S)\<^sup>2
    \<and> c = c\<^sub>0
    \<and> \<parallel>p - p\<^sub>0\<parallel> \<le> 2 * r
    \<and> sp = sp\<^sub>0 + a * t
    \<and> c\<^sub>0 - p\<^sub>0 = r\<^sub>0 *\<^sub>R rot(d\<^sub>0)
    \<and> (p - c\<^sub>0) \<bullet> (p\<^sub>0 - c\<^sub>0) = r\<^sub>0\<^sup>2 * (d \<bullet> d\<^sub>0)
    \<and> \<parallel>p - p\<^sub>0\<parallel> = r\<^sub>0 * \<parallel>d - d\<^sub>0\<parallel>
    \<and> \<parallel>p - p\<^sub>0\<parallel> \<le> 2 * S * t )\<^sup>e"

term "((p $ 0 = p\<^sub>0 $ 0 + (sp * sin(\<theta>) - s\<^sub>0 * sin(\<theta>\<^sub>0)) / \<omega>\<^sub>0 + a\<^sub>0*(cos(\<theta>) - cos(\<theta>\<^sub>0)) / \<omega>\<^sub>0\<^sup>2)
    \<and> (p $ 1 = p\<^sub>0 $ 1 - (sp * cos(\<theta>) - s\<^sub>0 * cos(\<theta>\<^sub>0)) / \<omega>\<^sub>0 + a\<^sub>0*(sin(\<theta>) - sin(\<theta>\<^sub>0)) / \<omega>\<^sub>0\<^sup>2))\<^sub>e"

term "(p = p\<^sub>0 + Vector[(sp * sin(\<theta>) - s\<^sub>0 * sin(\<theta>\<^sub>0)) / \<omega>\<^sub>0 + a\<^sub>0*(cos(\<theta>) - cos(\<theta>\<^sub>0)) / \<omega>\<^sub>0\<^sup>2
                     ,-(sp * cos(\<theta>) - s\<^sub>0 * cos(\<theta>\<^sub>0)) / \<omega>\<^sub>0 + a\<^sub>0*(sin(\<theta>) - sin(\<theta>\<^sub>0)) / \<omega>\<^sub>0\<^sup>2])\<^sub>e"

term "(p = p\<^sub>0 + ((sp *\<^sub>R rot(d) - sp\<^sub>0 *\<^sub>R rot(d\<^sub>0)) /\<^sub>R \<omega>\<^sub>0) + ((a\<^sub>0 *\<^sub>R d - a\<^sub>0 *\<^sub>R d\<^sub>0) /\<^sub>R \<omega>\<^sub>0\<^sup>2))\<^sub>e"  

expr_constructor \<Psi>\<^sub>2

declare norm_norm_1 [intro]

lemma dyn_inv_no_rot: "H{\<Psi>\<^sub>1 p\<^sub>0 ob\<^sub>0 a\<^sub>0 s\<^sub>0 d\<^sub>0} dyn {\<Psi>\<^sub>1 p\<^sub>0 ob\<^sub>0 a\<^sub>0 s\<^sub>0 d\<^sub>0}"
  apply (unfold dyn_def \<Psi>\<^sub>1_def)
  apply dCut
  apply dInduct
  apply dCut
  apply dInduct
  apply dCut
  apply dInduct
  apply dCut
  apply dInduct
  apply dCut
  apply dInduct
  apply dCut
  apply dInduct
  apply dCut
  apply dWeaken
  apply dCut
  apply dInduct
  apply dCut
  apply dInduct
  apply dCut
  apply dWeaken
  apply dCut
  apply dInduct
  apply dCut
  apply dInduct
  apply dWeaken
  apply (metis add_sign_intros(4) cross3_simps(12) is_num_normalize(1) 
         mult_2_right mult_sign_intros(1) ring_class.ring_distribs(1))
  done

theorem exists_cos_sin:
  fixes x y :: real
  assumes "x^2 + y^2 = 1"
  shows "\<exists>\<theta>. 0 \<le> \<theta> \<and> \<theta> < 2 * pi \<and> x = cos \<theta> \<and> y = sin \<theta>"
  by (meson assms sincos_total_2pi)

find_theorems cos sin

term frac

declare prime_elem_imp_nonzero [simp del]

declare usubst_upd_idem_sub [usubst del]

declare overrider.ovr_overshadow_left [simp del]

declare overrider.ovr_overshadow_right [simp del]

declare idem_overrider.ovr_idem [simp del]

declare [[simp_trace_depth_limit=10]] 

find_theorems "(\<subseteq>\<^sub>L)" subst_upd

declare [[simproc del: ring_le_cancel_numeral_factor]]

lemma dyn_inv_rot: 
  assumes r_nz: "r\<^sub>0 \<noteq> 0"
  shows "H{\<Psi>\<^sub>2 p\<^sub>0 ob\<^sub>0 a\<^sub>0 s\<^sub>0 d\<^sub>0 c\<^sub>0 r\<^sub>0 \<omega>\<^sub>0} dyn {\<Psi>\<^sub>2 p\<^sub>0 ob\<^sub>0 a\<^sub>0 s\<^sub>0 d\<^sub>0 c\<^sub>0 r\<^sub>0 \<omega>\<^sub>0}"
  apply (unfold dyn_def \<Psi>\<^sub>2_def)
  apply dCut
   apply dInduct
  apply dCut
   apply dInduct
  apply dCut
   apply dInduct
  apply dCut
   apply dInduct
  apply dCut
  apply dInduct
  apply dCut
  apply dInduct
  apply dCut
   apply dWeaken
  apply (metis abs_of_nonneg inner_real_def less_eq_real_def norm_eq
      real_norm_def)
  apply dCut
  apply dWeaken
  apply dCut
   apply dInduct
  apply dCut
   apply dInduct
  apply dCut
  apply dWeaken
  apply dCut
   apply dInduct
  apply dCut
   apply dInduct
  apply dCut
   apply dInduct
  apply dCut
   apply dInduct
  apply dCut
   apply (insert assms)
   apply dInduct
   apply expr_simp
  apply safe[1]
   apply (simp add: unicycle_derivative_induction)
  apply dCut
   apply dInduct
  apply expr_simp
  apply metis
  apply dCut
  apply (dWeaken)
  apply (subgoal_tac "\<parallel>p<s> - c\<^sub>0\<parallel> = r\<^sub>0")
    defer
    apply simp
  defer
   apply (subgoal_tac "\<parallel>c\<^sub>0 - p\<^sub>0\<parallel> = r\<^sub>0")
  defer
    apply simp
  defer
  apply (subgoal_tac "(p<s> - p\<^sub>0) = (p<s> - c\<^sub>0) + (c\<^sub>0 - p\<^sub>0)")
  defer
    apply (metis diff_add_cancel group_cancel.sub1)
  defer
   apply (metis mult_2_right norm_triangle_ineq)
  apply dCut
   apply dInduct
  apply dCut
   apply dInduct

  apply dCut
  apply dInduct
   apply expr_auto
   apply (subgoal_tac "d<s> \<bullet> (p\<^sub>0 - c\<^sub>0) = r<s> * (rot(d<s>) \<bullet> d\<^sub>0)")
    apply (smt (verit) more_arith_simps(11) mult.left_commute power2_eq_square)
   apply (subgoal_tac "p\<^sub>0 - c\<^sub>0 = -r<s> *\<^sub>R rot(d\<^sub>0)")
  apply (subgoal_tac "-r<s> * (d<s> \<bullet> rot(d\<^sub>0)) = r<s> * (rot(d<s>) \<bullet> d\<^sub>0)")
  apply (metis inner_simps(6))
  apply (simp add: rot_skew_sym)
  apply (metis minus_diff_eq scaleR_minus_left)
  apply dCut
  apply dWeaken
  subgoal for s
  proof -
    fix s
    assume r\<^sub>0: "r\<^sub>0 = r<s>"
    and d\<^sub>0_norm: "rot d\<^sub>0 \<bullet> rot d\<^sub>0 = 1" "\<parallel>d\<^sub>0\<parallel> = 1"

    assume  
       "0 < r<s>" 
      "0 \<le> t<s>" "\<parallel>d<s>\<parallel> = 1" "sp<s> = s\<^sub>0 + a<s> * t<s>" "\<omega><s> * r<s> = s\<^sub>0 + a<s> * t<s>"
      "rot (d<s>) \<bullet> rot (d<s>) = 1" "\<parallel>p<s> - p\<^sub>0\<parallel> \<le> r<s> * 2"
      "p<s> + r<s> *\<^sub>R rot (d<s>) = p\<^sub>0 + r<s> *\<^sub>R rot d\<^sub>0"
      

    assume r: "- (r<s> * ((p<s> - (p\<^sub>0 + r<s> *\<^sub>R rot d\<^sub>0)) \<bullet> rot d\<^sub>0)) = r<s> * (r<s> * (d<s> \<bullet> d\<^sub>0))"

    assume c\<^sub>0:"c\<^sub>0 = p\<^sub>0 + r<s> *\<^sub>R rot d\<^sub>0"

    \<comment> \<open> Positions relative to the centre point of the circle \<close>

    let ?a = "p\<^sub>0 - c\<^sub>0"
    let ?b = "p<s> - c\<^sub>0"

    from c\<^sub>0 r\<^sub>0 d\<^sub>0_norm have a: "?a \<bullet> ?a = r\<^sub>0\<^sup>2"
      by (simp add: power2_eq_square)

    have b: "?b \<bullet> ?b = r\<^sub>0\<^sup>2"
      by (smt (z3) Real_Vector_Spaces.real_normed_vector_class.norm_minus_commute
          \<open>p<s> + r<s> *\<^sub>R rot (d<s>) = p\<^sub>0 + r<s> *\<^sub>R rot d\<^sub>0\<close> \<open>rot (d<s>) \<bullet> rot (d<s>) = 1\<close>
          add_diff_cancel_left' c\<^sub>0 inner_real_def inner_simps(5,6) power2_eq_square
          power2_norm_eq_inner r\<^sub>0 real_inner_1_right)

   have norm_d_step: "\<parallel>d<s> - d\<^sub>0\<parallel>\<^sup>2 = 2*(1 -d\<^sub>0\<bullet>d<s>)"
      by (smt (verit, del_insts) \<open>\<parallel>d<s>\<parallel> = 1\<close> d\<^sub>0_norm(2) dot_square_norm inner_commute
          inner_simps(3) norm_eq_1)

    have orient: "?b \<bullet> ?a = r\<^sub>0\<^sup>2 * (d<s> \<bullet> d\<^sub>0)"
      by (simp add: c\<^sub>0 power2_eq_square r r\<^sub>0)

    have "\<parallel>?b - ?a\<parallel>\<^sup>2 = ?b\<bullet>?b - 2*(?a\<bullet>?b) + ?a\<bullet>?a" 
      by (simp add: power2_norm_eq_inner algebra_simps inner_commute)

    also have "... = r\<^sub>0\<^sup>2 - 2*(?a\<bullet>?b) + r\<^sub>0\<^sup>2"
      using a b by presburger

    also from orient have "... = r\<^sub>0\<^sup>2 - 2*r\<^sub>0\<^sup>2*(d\<^sub>0\<bullet>d<s>) + r\<^sub>0\<^sup>2"
      by (simp add: inner_commute)

    also have "... = 2*r\<^sub>0\<^sup>2*(1 - (d<s> \<bullet> d\<^sub>0))"
      by (simp add: inner_commute right_diff_distrib')

    also have "... = r\<^sub>0\<^sup>2*\<parallel>d<s> - d\<^sub>0\<parallel>\<^sup>2"
      by (simp add: inner_commute norm_d_step)

    also have "... = (r\<^sub>0*\<parallel>d<s> - d\<^sub>0\<parallel>)\<^sup>2"
      by (simp add: power_mult_distrib)

    finally have "\<parallel>?b - ?a\<parallel> = r<s> * \<parallel>d<s> - d\<^sub>0\<parallel>"
      using \<open>0 < r<s>\<close> r\<^sub>0 by auto
    
    thus "\<parallel>p<s> - p\<^sub>0\<parallel> = r<s> * \<parallel>d<s> - d\<^sub>0\<parallel>"
      by simp
  qed
  apply dWeaken
  done

lemma ctrl_inv: "H{\<phi>} ctrl (a := A) safe {\<phi> \<and> t = 0}"
  apply (simp add: ctrl_def safe_def loop_invariant_def \<Psi>_def)
  apply wlp_simp
  done

theorem static_safety: "H{\<Phi>} model1 {\<psi>}"
proof (unfold model1_def, kstar "loop_invariant", simp add: ctrl_def loop_invariant_def safe_def, symbolic_exec, simp_all)
  show "H{t = 0 \<and> \<omega> = 0 \<and> a = 0 \<and> (\<forall> i. sp\<^sup>2 / (2 * b) < \<parallel>p - ob $ i\<parallel>\<^sub>\<infinity>) \<and> 0 \<le> sp \<and> \<parallel>d\<parallel> = 1 \<and> sp = 0} 
          dyn 
         {(\<forall> i. sp\<^sup>2 / (2 * b) < \<parallel>p - ob $ i\<parallel>\<^sub>\<infinity>) \<and> 0 \<le> sp \<and> \<parallel>d\<parallel> = 1}"

  \<comment> \<open> For each Hoare triple, we need to drop down into point-wise reasoning, so we can explicitly characterise state changes. \<close>
  proof (rule hoare_fboxI, clarsimp)
    fix s
    assume t_0: "t<s> = 0" and \<omega>_0: "\<omega><s> = 0" and a_0: "a<s> = 0" and sep: "\<forall> i. 0 < \<parallel>p<s> - ob<s> $ i\<parallel>\<^sub>\<infinity>" and d1: "\<parallel>d<s>\<parallel> = 1" and sp_0: "sp<s> = 0"
    \<comment> \<open> We can show that the dynamics invariant holds initially \<close>
    with eps_min have \<Psi>_s: "\<Psi> (p<s>) (ob<s>) (a<s>) (sp<s>) s"
      by (simp add: \<Psi>_def infnorm_0)
    show "( |dyn] ((\<forall> i. sp\<^sup>2 / (2 * b) < \<parallel>p - ob $ i\<parallel>\<^sub>\<infinity>) \<and> 0 \<le> sp \<and> \<parallel>d\<parallel> = 1)) s"
    proof (intro fboxI, simp, safe)
      fix i s'
      assume "s' \<in> dyn s"
      have \<Psi>_s': "\<Psi> (p<s>) (ob<s>) (a<s>) (sp<s>) s'"
        by (smt (verit, best) SEXP_def \<Psi>_s \<open>s' \<in> dyn s\<close> dyn_inv
            fbox_def predicate1D)
      thus "(sp<s'>)\<^sup>2 / (2 * b) < \<parallel>p<s'> - ob<s'> $ i\<parallel>\<^sub>\<infinity>"
        by (simp add: \<Psi>_def, clarify)
           (metis \<open>\<forall> i. 0 < \<parallel>p<s> - ob<s> $ i\<parallel>\<^sub>\<infinity>\<close> \<open>a<s> = 0\<close> \<open>sp<s> = 0\<close> arith_simps(62,63) div_0
            infnorm_pos_lt less_le_not_le nat_arith.rule0 power_zero_numeral
            right_minus_eq)
      from \<Psi>_s' sp_0 a_0 show "0 \<le> sp<s'>"
        by (simp add: \<Psi>_def)
      from \<Psi>_s' show "\<parallel>d<s'>\<parallel> = 1" by (simp add: \<Psi>_def)
      have \<Psi>_s': "\<Psi> (p<s>) (ob<s>) (a<s>) (sp<s>) s'"
        by (smt (verit, best) SEXP_def \<Psi>_s \<open>s' \<in> dyn s\<close> dyn_inv fbox_def predicate1D)
    qed
  qed
next
  show "H{t = 0 \<and> a = - b \<and> (\<forall> i. sp\<^sup>2 / (2 * b) < \<parallel>p - ob $ i\<parallel>\<^sub>\<infinity>) \<and> 0 \<le> sp \<and> \<parallel>d\<parallel> = 1} dyn
         {(\<forall> i. sp\<^sup>2 / (2 * b) < \<parallel>p - ob $ i\<parallel>\<^sub>\<infinity>) \<and> 0 \<le> sp \<and> \<parallel>d\<parallel> = 1}"
  proof (rule hoare_fboxI, clarsimp)
    fix s
    assume t_0: "t<s> = 0" and a_b: "a<s> = - b" and sep: "\<forall> i. (sp<s>)\<^sup>2 / (2 * b) < \<parallel>p<s> - ob<s> $ i\<parallel>\<^sub>\<infinity>" and sp_pos: "0 \<le> sp<s>"
           and d1: "\<parallel>d<s>\<parallel> = 1"
    with eps_min have \<Psi>_s: "\<Psi> (p<s>) (ob<s>) (a<s>) (sp<s>) s"
      by (simp add: \<Psi>_def infnorm_0)
    show "( |dyn] ((\<forall> i. sp\<^sup>2 / (2 * b) < \<parallel>p - ob $ i\<parallel>\<^sub>\<infinity>) \<and> 0 \<le> sp \<and> \<parallel>d\<parallel> = 1)) s"
    proof (intro fboxI, simp, safe)
      fix s' i
      assume "s' \<in> dyn s"
      have \<Psi>_s': "\<Psi> (p<s>) (ob<s>) (a<s>) (sp<s>) s'"
        by (smt (verit, best) SEXP_def \<Psi>_s \<open>s' \<in> dyn s\<close> dyn_inv fbox_def predicate1D)
      have hold: "sp<s> ^ 2 / (2 * b) < infnorm (p<s> - ob<s> $ i)"
        using sep by force
      have hmove: "infnorm (p<s'> - p<s>) \<le> t<s'> * (sp<s> + -(b * t<s'>) - -(b * t<s'>) / 2)"
      proof -
        have hsp_eq: "sp<s'> = sp<s> + -(b * t<s'>)"
          using \<Psi>_def \<Psi>_s' a_b minus_mult_right mult.commute prod.simps(2) by auto
        show ?thesis
          by (smt (verit) \<Psi>_def \<Psi>_s' hsp_eq prod.simps(2))
      qed
      have hgoal: "(sp<s> + -(b * t<s'>)) ^ 2 / (2 * b) < infnorm (p<s'> - ob<s> $ i)"
      proof -
        have "infnorm (p<s> - ob<s> $ i) \<le> infnorm (p<s> - p<s'>) + infnorm (p<s'> - ob<s> $ i)"
          by (metis (no_types, lifting) add_diff_cancel_right diff_add_cancel infnorm_triangle)
        also have "... = infnorm (p<s'> - p<s>) + infnorm (p<s'> - ob<s> $ i)"
          by (simp add: infnorm_sub)
        finally have "sp<s> ^ 2 / (2 * b) < infnorm (p<s'> - p<s>) + infnorm (p<s'> - ob<s> $ i)"
          using hold by linarith
        moreover have "infnorm (p<s'> - p<s>) \<le> t<s'> * sp<s> - b * (t<s'> ^ 2) / 2"
          using hmove by (simp add: field_simps power2_eq_square)
        moreover have "sp<s> ^ 2 / (2 * b) - (t<s'> * sp<s> - b * (t<s'> ^ 2) / 2) = (sp<s> - b * t<s'>) ^ 2 / (2 * b)"
          using b_min by (simp add: field_simps power2_eq_square)
        ultimately show ?thesis
          by simp 
      qed
      thus "(sp<s'>)\<^sup>2 / (2 * b) < \<parallel>p<s'> - ob<s'> $ i\<parallel>\<^sub>\<infinity>"
        using \<Psi>_s' a_b by (auto simp add: \<Psi>_def)
      show "0 \<le> sp<s'>"
        using \<Psi>_s' by (auto simp add: \<Psi>_def)
      show "\<parallel>d<s'>\<parallel> = 1"
        using \<Psi>_s' by (auto simp add: \<Psi>_def)
    qed
  qed
next
  fix \<omega>\<^sub>0 :: real and r\<^sub>0 :: real

  show "H{t = 0 \<and> a = A \<and> (\<forall> i. sp\<^sup>2 / (2 * b) < \<parallel>p - ob $ i\<parallel>\<^sub>\<infinity>) \<and> 0 \<le> sp \<and> \<parallel>d\<parallel> = 1 
         \<and> \<omega> = \<omega>\<^sub>0 \<and> - \<Omega> \<le> \<omega> \<and> \<omega> \<le> \<Omega> \<and> r = r\<^sub>0 \<and> (r \<noteq> 0 \<longrightarrow> r * \<omega> = sp)
         \<and> (\<forall> i. sp\<^sup>2 / (2 * b) + (a / b + 1) * (a * \<epsilon>\<^sup>2 / 2 + \<epsilon> * sp) < \<parallel>p - ob $ i\<parallel>\<^sub>\<infinity>)} 
         dyn 
       {(\<forall> i. sp\<^sup>2 / (2 * b) < \<parallel>p - ob $ i\<parallel>\<^sub>\<infinity>) \<and> 0 \<le> sp \<and> \<parallel>d\<parallel> = 1}"
  proof (rule hoare_fboxI, clarsimp)
    fix s
    assume "t<s> = 0" "A = a<s>" "0 \<le> sp<s>" "\<parallel>d<s>\<parallel> = 1"
       and safe_infl: "\<forall> i. sp<s>^2 / (2 * b) + (a<s> / b + 1) * (a<s> * \<epsilon>\<^sup>2 / 2 + \<epsilon> * sp<s>) < \<parallel>p<s> - ob<s> $ i\<parallel>\<^sub>\<infinity>"
    hence \<Psi>_s: "\<Psi> (p<s>) (ob<s>) (a<s>) (sp<s>) s"
      by (simp add: \<Psi>_def eps_min infnorm_0 less_eq_real_def)
    show "( |dyn] ((\<forall>i. sp\<^sup>2 / (2 * b) < \<parallel>p - ob $ i\<parallel>\<^sub>\<infinity>) \<and> 0 \<le> sp \<and> \<parallel>d\<parallel> = 1)) s"
    proof (intro fboxI, simp, safe)
      fix s' i
      assume s': "s' \<in> dyn s"
      hence \<Psi>_s': "\<Psi> (p<s>) (ob<s>) (a<s>) (sp<s>) s'"
        by (smt (verit, best) SEXP_def \<Psi>_s s' dyn_inv fbox_def predicate1D)
      hence t_bnd: "t<s'> \<le> \<epsilon>" and sp_s': "sp<s'> = sp<s> + A * t<s'>"
        using \<open>A = a<s>\<close> by (auto simp add: \<Psi>_def)
      have "infnorm (p<s> - ob<s> $ i) \<le> infnorm (p<s> - p<s'>) + infnorm (p<s'> - ob<s> $ i)"
        by (smt (verit, best) add_diff_add add_diff_cancel_left' diff_diff_eq2 infnorm_triangle)
      also have "... = infnorm (p<s'> - p<s>) + infnorm (p<s'> - ob<s> $ i)"
        using infnorm_sub by auto
      finally have dist_ineq: "infnorm (p<s> - ob<s> $ i) - infnorm (p<s'> - p<s>) \<le> infnorm (p<s'> - ob<s> $ i)" 
        by linarith
      have "infnorm (p<s'> - p<s>) \<le> t<s'> * sp<s> + A * (t<s'> ^ 2) / 2"
        using \<Psi>_s' \<open>A = a<s>\<close> by (auto simp add: \<Psi>_def field_simps)
      have "infnorm (p<s'> - p<s>) \<le> t<s'> * sp<s> + A * (t<s'> ^ 2) / 2"
        using \<Psi>_s' \<open>A = a<s>\<close> by (auto simp add: \<Psi>_def field_simps)
      also have "... \<le> \<epsilon> * sp<s> + A * (\<epsilon> ^ 2) / 2"
      proof -
        have term1: "t<s'> * sp<s> \<le> \<epsilon> * sp<s>"
          using t_bnd \<open>0 \<le> sp<s>\<close> by (simp add: mult_right_mono)
        
        have t_pos: "0 \<le> t<s'>" 
          using \<Psi>_s' by (auto simp add: \<Psi>_def)
        have t_sq: "t<s'> ^ 2 \<le> \<epsilon> ^ 2"
          by (simp add: power_mono t_bnd t_pos)
        have term2: "A * (t<s'> ^ 2) / 2 \<le> A * (\<epsilon> ^ 2) / 2"
          using t_sq A_min by (simp add: divide_right_mono mult_left_mono)          
        from term1 term2 show ?thesis by linarith
      qed
      finally have "infnorm (p<s'> - p<s>) \<le> \<epsilon> * sp<s> + A * (\<epsilon> ^ 2) / 2" .

      have h_bound: "infnorm (p<s'> - p<s>) \<le> (A * (\<epsilon> \<^sup>2) / 2 + \<epsilon> * sp<s>)"
        using \<open>infnorm (p<s'> - p<s>) \<le> \<epsilon> * sp<s> + A * (\<epsilon> ^ 2) / 2\<close> by (simp add: field_simps)

      from A_min b_min have key_algebraic_bound: "(sp<s> + A * t<s'>)^2 / (2*b) \<le> (sp<s>)^2 / (2*b) + (A/b) * (A * \<epsilon>^2 / 2 + \<epsilon> * sp<s>)"
      proof -
        have "(sp<s> + A * t<s'>)^2 = (sp<s>)^2 + 2 * A * t<s'> * sp<s> + A^2 * (t<s'>)^2"
          by (simp add: algebra_simps power2_eq_square)
        also have "... \<le> (sp<s>)^2 + 2 * A * \<epsilon> * sp<s> + A^2 * \<epsilon>^2"
        proof (intro add_mono)
          show "(sp<s>)\<^sup>2 \<le> (sp<s>)\<^sup>2" by simp
        next
          show "2 * A * t<s'> * sp<s> \<le> 2 * A * \<epsilon> * sp<s>"
            by (simp add: A_min \<open>0 \<le> sp<s>\<close> landau_o.R_mult_right_mono landau_omega.R_mult_left_mono t_bnd)
        next
          have "(t<s'>)^2 \<le> \<epsilon>^2"
            using \<Psi>_def \<Psi>_s' by auto 
          thus "A^2 * (t<s'>)^2 \<le> A^2 * \<epsilon>^2"
            using A_min by (simp add: mult_left_mono power2_eq_square)
        qed
        finally have "(sp<s> + A * t<s'>)^2 \<le> (sp<s>)^2 + 2 * A * \<epsilon> * sp<s> + A^2 * \<epsilon>^2" .
        hence "(sp<s> + A * t<s'>)^2 / (2*b) \<le> ((sp<s>)^2 + 2 * A * \<epsilon> * sp<s> + A^2 * \<epsilon>^2) / (2*b)"
          using b_min by (simp add: divide_right_mono)
        also from b_min have "... = (sp<s>)^2 / (2*b) + (A/b) * (A * \<epsilon>^2 / 2 + \<epsilon> * sp<s>)"
          by (simp add: field_simps)
        finally show ?thesis .
      qed

      show "(sp<s'>)\<^sup>2 / (2 * b) < \<parallel>p<s'> - ob<s'> $ i\<parallel>\<^sub>\<infinity>"
      proof -
        have "ob<s'> = ob<s>" using \<Psi>_s' by (simp add: \<Psi>_def)
        have "(sp<s'>)^2 / (2*b) \<le> (sp<s>)^2 / (2*b) + (A/b) * (A * \<epsilon>^2 / 2 + \<epsilon> * sp<s>)"
          using sp_s' key_algebraic_bound by simp
        also have "... = (sp<s>)^2 / (2*b) + (A/b + 1) * (A * \<epsilon>^2 / 2 + \<epsilon> * sp<s>) - (A * \<epsilon>^2 / 2 + \<epsilon> * sp<s>)"
          by (simp add: algebra_simps)
        also have "... < infnorm (p<s> - ob<s> $ i) - infnorm (p<s'> - p<s>)"
          by (smt (verit, ccfv_threshold) \<open>A = a<s>\<close> h_bound safe_infl)
        also have "... \<le> infnorm (p<s'> - ob<s> $ i)"
          using dist_ineq by linarith
        finally show ?thesis using `ob<s'> = ob<s>` by simp
      qed

      show "0 \<le> sp<s'>" using \<Psi>_s' by (auto simp add: \<Psi>_def)
      show "\<parallel>d<s'>\<parallel> = 1" using \<Psi>_s' by (auto simp add: \<Psi>_def)
    qed
  qed
next
  show "`\<Phi> \<longrightarrow> \<phi>`"
    by expr_simp
next
  show "`\<phi> \<longrightarrow> \<psi>`"
    by expr_simp (metis arith_simps(62) b_min divide_less_eq infnorm_0 power2_less_0 rel_simps(51) verit_minus_simplify(1) zero_compare_simps(6))
qed
  
end

end