section \<open> Autonomous Marine Vehicle \<close>

theory AMV
  imports "Hybrid-Verification.Hybrid_Verification"
begin

subsection \<open> Preliminaries \<close>

no_notation (ASCII)
  comp  (infixl "o" 55)

lemma self_dot [simp]: "\<parallel>v\<parallel> * \<parallel>v\<parallel> = v \<bullet> v"
  by (metis norm_cauchy_schwarz_eq)

lemma orth_mag [simp]: "a \<bullet> b = \<parallel>a\<parallel> * \<parallel>b\<parallel> \<Longrightarrow> \<parallel>a + b\<parallel> = \<parallel>a\<parallel> + \<parallel>b\<parallel>"
  by (simp add: norm_cauchy_schwarz_eq norm_triangle_eq)

lemma orth_mag' [simp]: "b \<bullet> a = \<parallel>b\<parallel> * \<parallel>a\<parallel> \<Longrightarrow> \<parallel>a + b\<parallel> = \<parallel>a\<parallel> + \<parallel>b\<parallel>"
  by (simp add: norm_cauchy_schwarz_eq norm_triangle_eq)

lemma "a \<noteq> 0 \<Longrightarrow> \<parallel>sgn a\<parallel> = 1"
  by (simp add: norm_sgn)

lemma "a \<noteq> 0 \<Longrightarrow> sgn a \<bullet> sgn a = 1"
  by (meson norm_eq_1 norm_sgn)

lemma sgn_self_dot:
  assumes "a \<noteq> 0"
  shows "(sgn a) \<bullet> (sgn a) = 1"
  by (meson assms norm_eq_1 norm_sgn)

lemma "a \<noteq> 0 \<Longrightarrow> (a / \<parallel>a\<parallel>) \<bullet> (a / \<parallel>a\<parallel>) = 1"
  by simp

lemma "\<lbrakk> a \<ge> 0; a\<^sup>2 = b \<rbrakk> \<Longrightarrow> a = sqrt(b)"
  by (simp add: real_sqrt_unique)


lemma 
  assumes "(a::'a::ordered_euclidean_space) \<noteq> 0"
  shows "a \<bullet> b / \<parallel>a\<parallel> = sgn a \<bullet> b"
  by (simp add: divide_inverse_commute sgn_div_norm)

lemma "v \<noteq> 0 \<Longrightarrow> arccos(v \<bullet> v / (\<parallel>v\<parallel> * \<parallel>v\<parallel>)) = 0"
  by (simp)

declare num1_eq1 [simp del]

lemma exhaust_2':
  fixes x :: 2
  shows "x = 0 \<or> x = 1"
  using exhaust_2 by fastforce

lemma forall_2': "(\<forall>i::2. P i) \<longleftrightarrow> P 0 \<and> P 1"
  by (metis exhaust_2')

declare UNIV_1 [simp del]
declare UNIV_2 [simp del]

lemma UNIV_1 [simp]: "(UNIV :: 1 set) = {0}"
  by (metis UNIV_1 num1_eq1)

lemma UNIV_2 [simp]: "(UNIV :: 2 set) = {0,1}"
  by (simp add: UNIV_eq_I exhaust_2')

subsection \<open> Vector Theorems and Simplifications \<close>

lemma vec_norm: "\<parallel>\<^bold>[[x, y]\<^bold>]\<parallel> = sqrt(x\<^sup>2 + y\<^sup>2)"
  by (simp add: norm_vec_def)

lemma vec_simps [simp]: 
  "k *\<^sub>R \<^bold>[[x, y]\<^bold>] = \<^bold>[[k *\<^sub>R x, k *\<^sub>R y]\<^bold>]"
  "\<^bold>[[x\<^sub>1::real, y\<^sub>1]\<^bold>] \<bullet> \<^bold>[[x\<^sub>2, y\<^sub>2]\<^bold>] = x\<^sub>1 * x\<^sub>2 + y\<^sub>1 * y\<^sub>2"
  "\<^bold>[[x\<^sub>1, y\<^sub>1]\<^bold>] + \<^bold>[[x\<^sub>2, y\<^sub>2]\<^bold>] = \<^bold>[[x\<^sub>1 + x\<^sub>2, y\<^sub>1 + y\<^sub>2]\<^bold>]"
  "\<^bold>[[x\<^sub>1, y\<^sub>1]\<^bold>] - \<^bold>[[x\<^sub>2, y\<^sub>2]\<^bold>] = \<^bold>[[x\<^sub>1 - x\<^sub>2, y\<^sub>1 - y\<^sub>2]\<^bold>]"
  "\<^bold>[[0, 0]\<^bold>] = 0"
     apply (subst scaleR_Mat, simp_all)
  apply (simp add: inner_vec_def)
    apply (subst plus_Mat, simp_all)
   apply (subst minus_Mat, simp_all)
   apply (simp add: matrix_eq_iff nat_of_num1_def forall_2')
  done

lemma orient_vec_mag_1 [simp]: "\<parallel>\<^bold>[[sin \<theta> :: real, cos \<theta>]\<^bold>]\<parallel> = 1"
  by (simp add: vec_norm)

lemma orient_vec_mag_n [simp]: 
  assumes "n \<ge> 0"
  shows "\<parallel>\<^bold>[[n * sin \<theta> :: real, n * cos \<theta>]\<^bold>]\<parallel> = n" (is "?P = ?Q")
proof -
  have "?P = \<parallel>\<^bold>[[n *\<^sub>R sin \<theta> :: real, n *\<^sub>R cos \<theta>]\<^bold>]\<parallel>"
    by (metis real_scaleR_def)
  also have "... = \<parallel>n *\<^sub>R \<^bold>[[sin \<theta> :: real, cos \<theta>]\<^bold>]\<parallel>"
    by simp
  also have "... = \<parallel>n\<parallel> * \<parallel>\<^bold>[[sin \<theta> :: real, cos \<theta>]\<^bold>]\<parallel>"
    by (metis norm_scaleR real_norm_def)
  also from assms have "... = n"
    by simp
  finally show ?thesis .
qed

lemma sin_cos_self_dot [simp]: "\<^bold>[[sin(\<theta>::real), cos(\<theta>)]\<^bold>] \<bullet> \<^bold>[[sin(\<theta>), cos(\<theta>)]\<^bold>] = 1"
  by (simp, metis power2_eq_square sin_cos_squared_add)

lemma vector_2_cases [cases type]: 
  fixes x
  assumes "\<And> x\<^sub>1 x\<^sub>2. x = \<^bold>[[x\<^sub>1, x\<^sub>2]\<^bold>] \<Longrightarrow> P"
  shows "P"
proof -
  have "x = \<^bold>[[x$1$0, x$1$1]\<^bold>]"
    by (simp add: matrix_eq_iff nat_of_num1_def forall_2')
  thus ?thesis
    using assms by metis
qed

lemma cos_r1:
  assumes "- 1 \<le> y" "y < 1"
  shows "0 < arccos y"
proof -
  have "arccos 1 < arccos y"
    by (rule arccos_less_arccos, simp_all add: assms)
  thus ?thesis
    by simp
qed

lemma cos_r2:
  assumes "0 < x" "x \<le> 1"
  shows "arccos x * 2 < pi"
proof -
  have "arccos x < arccos 0"
    by (rule arccos_less_arccos, simp_all add: assms)
  thus ?thesis
    by simp
qed


lemma vec_2_eq_iff [simp]: "\<^bold>[[x\<^sub>1, y\<^sub>1]\<^bold>] = \<^bold>[[x\<^sub>2, y\<^sub>2]\<^bold>] \<longleftrightarrow> (x\<^sub>1 = x\<^sub>2 \<and> y\<^sub>1 = y\<^sub>2)"
  by (auto simp add: Mat_eq_iff')

lemma vec_2_eq_zero_off [simp]: "\<^bold>[[x, y]\<^bold>] = 0 \<longleftrightarrow> (x = 0 \<and> y = 0)"
  by (subst vec_simps(5) [THEN sym], simp only: vec_2_eq_iff)

subsection \<open> Angle Calculations \<close>

definition 
  "angOfVec x \<equiv> 
    (let a = vangle \<^bold>[[0::real,1]\<^bold>] x in 
     if (x 0 0 \<ge> 0) then a else (2*pi) - a)"

abbreviation "\<phi>\<^sub>m\<^sub>a\<^sub>x \<equiv> pi / 3"      

definition angDiff :: "real \<Rightarrow> real \<Rightarrow> bool \<Rightarrow> real" where
"angDiff \<phi>\<^sub>A \<phi>\<^sub>B rotRestr \<equiv>
  let dphi =
  (if (abs(\<phi>\<^sub>A - \<phi>\<^sub>B) <= pi) then
    \<phi>\<^sub>A - \<phi>\<^sub>B
  else
    -sgn(\<phi>\<^sub>A - \<phi>\<^sub>B) * (2 * pi - abs(\<phi>\<^sub>A - \<phi>\<^sub>B)))
  in 
  if (rotRestr) then
    -sgn(dphi) * min(abs(dphi)) \<phi>\<^sub>m\<^sub>a\<^sub>x
  else dphi"

lemma "angOfVec (Matrix[[0,1]]) = 0" \<comment> \<open> 0 degree angOfVector \<close>
  by (simp add: angOfVec_def vangle_def vec_norm)

lemma arccos_inv_sqrt2: "arccos (1 / sqrt 2) = pi / 4"
  by (smt arccos_cos arccos_minus_1 arcsin_minus_1 arcsin_plus_arccos arctan arctan_less_pi4_pos arctan_one arctan_zero_zero cos_45 eq_divide_eq mult_cancel_left1 real_div_sqrt real_divide_square_eq)

lemma "angOfVec (Matrix[[1,1]]) = pi / 4" \<comment> \<open> 45 degree angOfVector \<close>
  by (simp add: angOfVec_def vangle_def arccos_inv_sqrt2 vec_norm)

lemma "angOfVec (Matrix[[1,0]]) = pi / 2" \<comment> \<open> 90 degree angOfVector \<close>
  by (simp add: angOfVec_def vangle_def)

lemma "sqrt 2 \<ge> 0"
  by (metis real_sqrt_ge_0_iff zero_le_numeral)

lemma arccos_minus_inv_sqrt2: "arccos (- (1 / sqrt 2)) = 3 * (pi / 4)"
  apply (subst arccos_minus, simp_all add: field_simps)
  apply (metis le_minus_one_simps(2) one_le_numeral order_trans real_sqrt_ge_1_iff)
  apply (metis arccos_inv_sqrt2 divide_cancel_right nonzero_mult_div_cancel_left zero_neq_numeral)
  done

lemma "angOfVec (Matrix[[1,-1]]) = 3 * (pi / 4)" \<comment> \<open> 135 degree angOfVector \<close>
  apply (simp add: angOfVec_def vangle_def vec_norm arccos_minus)
  apply (metis arccos_minus_inv_sqrt2 eq_divide_eq_numeral1(1) times_divide_eq_right zero_neq_numeral)
  done

lemma "angDiff (pi/2) (pi/4) False = pi/4"
  by (simp add: angDiff_def)

lemma "angDiff (pi) (pi/4) False = 3 / 4 * pi"
  by (simp add: angDiff_def)

subsection \<open> AMV Constants \<close>

abbreviation "m \<equiv> 12"            \<comment> \<open> Mass \<close>
abbreviation "S \<equiv> 1.5"           \<comment> \<open> Maximum speed \<close>
definition [expr_defs]: "f\<^sub>m\<^sub>a\<^sub>x \<equiv> 9 * 9.80665" \<comment> \<open> Maximum force \<close>
abbreviation "\<phi>\<^sub>\<epsilon> \<equiv> 0.001"        \<comment> \<open> Angular tolerance \<close>
abbreviation "s\<^sub>\<epsilon> \<equiv> 0.001"        \<comment> \<open> Linear tolerance \<close>

abbreviation "kp\<^sub>g\<^sub>v \<equiv> 5"
abbreviation "kp\<^sub>g\<^sub>r \<equiv> 5"

abbreviation "w\<^sub>\<epsilon> \<equiv> 0.5" \<comment> \<open> Waypoint tolerance \<close>

definition "(\<epsilon>::real) \<equiv> 0.1"

lemma [simp]: "\<epsilon> > 0"
  by (simp add: \<epsilon>_def)

subsection \<open> AMV State Space \<close>

datatype OPMode = OCM | HCM | MOM

alphabet 's AMVs =
  old :: 's
  \<comment> \<open> Continuous Variables \<close>
  p :: "real vec[2]" \<comment> \<open> Position \<close>
  v :: "real vec[2]" \<comment> \<open> Velocity \<close>
  a :: "real vec[2]" \<comment> \<open> Acceleration \<close>
  \<phi> :: "real" \<comment> \<open> Heading \<close>
  s :: "real" \<comment> \<open> Linear Speed \<close>
  t :: "real" \<comment> \<open> Timer \<close>
  \<comment> \<open> Discrete Variables\<close>
  path    :: "(real vec[2]) list" \<comment> \<open> Path of way points \<close>
  nextWP  :: "real vec[2]" \<comment> \<open> Location of next way point \<close>
  obsReg  :: "(real vec[2]) set" \<comment> \<open> Obstacle register \<close>
  rs      :: "real" \<comment> \<open> Requested speed \<close>
  rh      :: "real" \<comment> \<open> Requested heading \<close>
  ft      :: "real" 
  fl      :: "real"
  F       :: "real vec[2]" \<comment> \<open> Force vector \<close>
  mode    :: OPMode \<comment> \<open> LRE Operating Mode \<close>

abbreviation "w\<^sub>x \<equiv> mat_lens 0 0 ;\<^sub>L nextWP"
abbreviation "w\<^sub>y \<equiv> mat_lens 0 1 ;\<^sub>L nextWP"

abbreviation "p\<^sub>x \<equiv> mat_lens 0 0 ;\<^sub>L p"
abbreviation "p\<^sub>y \<equiv> mat_lens 0 1 ;\<^sub>L p"

abbreviation "v\<^sub>x \<equiv> mat_lens 0 0 ;\<^sub>L v"
abbreviation "v\<^sub>y \<equiv> mat_lens 0 1 ;\<^sub>L v"

abbreviation "a\<^sub>x \<equiv> mat_lens 0 0 ;\<^sub>L a"
abbreviation "a\<^sub>y \<equiv> mat_lens 0 1 ;\<^sub>L a"

abbreviation "\<phi>\<^sub>A\<^sub>V \<equiv> (angOfVec v)\<^sub>e"
abbreviation "\<phi>\<^sub>W\<^sub>P \<equiv> (angOfVec (v - nextWP))\<^sub>e"

subsection \<open> AMV Hybrid Model \<close>

abbreviation "\<omega> \<equiv> (if (\<parallel>v\<parallel> = 0) then 0 else arccos((v + a) \<bullet> v / (\<parallel>v + a\<parallel> * \<parallel>v\<parallel>)))\<^sub>e"

subsubsection \<open> AMV Kinematics \<close>

text \<open> Shows the derivative of each continuous variable. \<close>

abbreviation "ax\<^sub>A\<^sub>V \<equiv> (t < \<epsilon> \<and> s *\<^sub>R \<^bold>[[sin(\<phi>), cos(\<phi>)]\<^bold>] = v \<and> 0 \<le> s \<and> s \<le> S)\<^sup>e"

abbreviation "ODE \<equiv>
   { p` = v
   , v` = a
   , a` = 0
   , \<phi>` = @\<omega>
   , s` = if s \<noteq> 0 then (v \<bullet> a) / s else \<parallel>a\<parallel>
   , t` = 1 
   | @ax\<^sub>A\<^sub>V }"

abbreviation "Kinematics \<equiv> t ::= 0 ; ODE"

subsubsection \<open> Navigation System \<close>

abbreviation "atWP \<equiv> (\<parallel>nextWP - p\<parallel> < w\<^sub>\<epsilon>)\<^sup>e"

abbreviation "steerToWP \<equiv> rh ::= angOfVec(nextWP - p)" \<comment> \<open> Calculation of heading \<close>

abbreviation "FullStop \<equiv> (rs ::= 0)"

abbreviation "NextWayPoint \<equiv> 
  (IF (path = []) THEN FullStop ELSE nextWP ::= hd(path); path ::= tl(path); steerToWP)"

abbreviation
  "Navigation \<equiv> (IF @atWP THEN NextWayPoint ELSE steerToWP)"

subsubsection \<open> Last Response Engine \<close>

abbreviation 
  "LRE \<equiv> (\<questiondown>mode = HCM? ; rs ::= 0.1 ; steerToWP)
       \<sqinter> (\<questiondown>mode = OCM? ; skip)
       \<sqinter> (\<questiondown>mode = MOM? ; rs ::= 1 ; steerToWP ;
             IF (\<exists> o. o \<in> obsReg \<and> \<parallel>p - o\<parallel> \<le> 7.5) THEN mode ::= HCM ; rs ::= 0.1 ELSE skip)"

subsubsection \<open> Autopilot \<close>

abbreviation "AP \<equiv> 
  IF \<parallel>rs - s\<parallel> > s\<^sub>\<epsilon>
    THEN ft ::= sgn(rs - s)*min(kp\<^sub>g\<^sub>v * \<parallel>rs - s\<parallel>) f\<^sub>m\<^sub>a\<^sub>x
    ELSE ft ::= 0 ;
  IF \<parallel>rh - \<phi>\<parallel> > \<phi>\<^sub>\<epsilon>
    THEN fl ::= sgn(rh - \<phi>)*min(kp\<^sub>g\<^sub>r * \<parallel>rh - \<phi>\<parallel>) f\<^sub>m\<^sub>a\<^sub>x
    ELSE fl ::= 0 ;
  F ::= fl *\<^sub>R \<^bold>[[cos(\<phi>), sin(\<phi>)]\<^bold>] 
      + ft *\<^sub>R \<^bold>[[sin(\<phi>), cos(\<phi>)]\<^bold>] ;
  a ::= F /\<^sub>R m"

subsubsection \<open> AMV System \<close>

abbreviation "AMV \<equiv> (Navigation ; LRE ; AP ; Kinematics)\<^sup>*"

subsection \<open> Structural Properties \<close>

lemma AP_nmods: "AP nmods (p, v, s, \<phi>, t)"
  by (auto intro!: closure; subst_eval)

lemma LRE_nmods: "LRE nmods (p, v, a, s, \<phi>, t)"
  by (auto intro!: closure; subst_eval)

lemma axAV_LRE_inv: "H{@ax\<^sub>A\<^sub>V}LRE{@ax\<^sub>A\<^sub>V}"
  apply (rule nmods_invariant)
  by (auto intro!: closure; subst_eval)

lemma axAV_AP_inv: "H{@ax\<^sub>A\<^sub>V}AP{@ax\<^sub>A\<^sub>V}"
  apply (rule nmods_invariant)
  by (auto intro!: closure; subst_eval)

subsection \<open> Invariants \<close>

lemma time_pos:
"H{t \<ge> 0} ODE {t \<ge> 0}"
  by (dInduct)

lemma "H{s = \<parallel>v\<parallel>} ODE {s = \<parallel>v\<parallel>}"
  by (rule diff_weak_on_rule, expr_auto)

lemma "H{rs = s \<and> rh = \<phi>} AP {a = 0}"
  by hoare_wp_simp

lemma AP_no_accel_lemma: "H{\<parallel>rs - s\<parallel> \<le> s\<^sub>\<epsilon> \<and> rh = \<phi>}AP{a = 0}"
  by hoare_wp_simp

lemma AP_no_accel: "H{s \<in> {rs - s\<^sub>\<epsilon>..rs + s\<^sub>\<epsilon>} \<and> rh = \<phi>}AP{a = 0}"
  using AP_no_accel_lemma
  by (rule hoare_conseq, simp_all add: abs_diff_le_iff[THEN sym] abs_minus_commute)
    
lemma "H{rs < s - s\<^sub>\<epsilon> \<and> rh = \<phi>}AP{\<parallel>a\<parallel> > 0}"
  using sin_zero_abs_cos_one by (hoare_wp_auto, fastforce)

declare vec_simps [simp del]

lemma collinear_AP: 
  "H{s \<ge> 0 \<and> rs \<ge> s \<and> v = s *\<^sub>R \<^bold>[[sin(\<phi>),cos(\<phi>)]\<^bold>] \<and> \<parallel>rh - \<phi>\<parallel> < \<phi>\<^sub>\<epsilon>}
   AP
   {a \<bullet> v = \<parallel>a\<parallel> * \<parallel>v\<parallel>}"
  by hoare_wp_auto

declare vec_simps [simp]

lemma "H{path = [] \<and> @atWP} Navigation {path = [] \<and> rs = 0 \<and> @atWP}"
  by (hoare_wp_simp)

text \<open> If the LRE is in MOM, the way point is in the north-east quadrant wrt. the AMV, and there
  are no nearby obstacles, then the LRE will stay in MOM and request maximum velocity and heading
  within the north-east quadrant. \<close>

lemma LRE_quad1_heading:
  "H{mode = MOM \<and> w\<^sub>x > p\<^sub>x \<and> w\<^sub>y > p\<^sub>y \<and> (\<forall> o. o \<in> obsReg \<longrightarrow> \<parallel>p - o\<parallel> > 7.5)}
  LRE
  {mode = MOM \<and> rs = 1 \<and> rh \<in> {0<..<pi / 2}}"
  apply hoare_wp_auto
   apply (rename_tac p w r)
   apply (case_tac p rule: vector_2_cases)
   apply (simp)
   apply (case_tac w rule: vector_2_cases)
   apply (simp)
   apply (auto simp add: angOfVec_def vangle_def vec_norm)
  apply (rule cos_r1)
   apply (rename_tac x\<^sub>1 x\<^sub>2 x\<^sub>1' x\<^sub>2')
   apply (subgoal_tac "0 \<le> (100 * x\<^sub>2' - 100 * x\<^sub>2)")
  apply (subgoal_tac "0 \<le> (100 * sqrt ((x\<^sub>1' - x\<^sub>1)\<^sup>2 + (x\<^sub>2' - x\<^sub>2)\<^sup>2))")
  apply (smt divide_nonneg_nonneg mult_nonneg_nonneg norm_ge_zero vec_simps(2) vec_simps(4))
    apply (simp_all add: vec_simps)
  apply (subst divide_less_eq_1_pos)
  apply (simp_all)
  apply (simp add: sum_power2_gt_zero_iff)
  apply (smt sqrt_le_D zero_less_power)
   apply (rename_tac p w r)
   apply (case_tac p rule: vector_2_cases)
   apply (simp)
   apply (case_tac w rule: vector_2_cases)
   apply (simp)
   apply (auto simp add: vangle_def)
  apply (rule cos_r2)
    apply (simp_all add: vec_norm)
   apply (rename_tac x\<^sub>1 x\<^sub>2 x\<^sub>1' x\<^sub>2')
   apply (subgoal_tac "0 < (100 * x\<^sub>2' - 100 * x\<^sub>2)")
  apply (subgoal_tac "0 < (100 * sqrt ((x\<^sub>1' - x\<^sub>1)\<^sup>2 + (x\<^sub>2' - x\<^sub>2)\<^sup>2))")
  apply simp
  apply (simp add: power2_eq_square sum_squares_gt_zero_iff)
    apply (simp_all)
  apply (smt divide_le_eq_1_pos real_le_rsqrt zero_less_power)
  done

lemma LRE_HCM:
  "H{mode = MOM \<and> (\<exists> o. o \<in> obsReg \<and> \<parallel>p - o\<parallel> \<le> 7.5) \<and> \<parallel>angOfVec(nextWP - p) - \<phi>\<parallel> < \<phi>\<^sub>\<epsilon>}
     LRE
   {mode = HCM \<and> rs = 0.1 \<and> \<parallel>rh - \<phi>\<parallel> < \<phi>\<^sub>\<epsilon>}"
  by hoare_wp_simp

lemma 
  "H{rs = s \<and> \<phi> = 0 \<and> rh = pi}
    AP
   {a = \<^bold>[[kp\<^sub>g\<^sub>r * pi / m, 0]\<^bold>]}"
proof -
  have 1: "(kp\<^sub>g\<^sub>r * pi) < (1765197 / 20000)"
    by (approximation 20)
  show ?thesis 
    apply hoare_wp_auto
    using "1" apply linarith
    using pi_gt3 apply auto
    done
qed

lemma "H{t = 0 \<and> v = $old:v}ODE{v = $old:v + t *\<^sub>R a}"
proof -
  have 1: "H{v = $old:v + t *\<^sub>R a}ODE{v = $old:v + t *\<^sub>R a}"
    by (dInduct)
  thus ?thesis
    by (rule hoare_conseq, simp_all)
qed

text \<open> If the AMV is accelerating in the same direction as the velocity, then it will continue
  to do so. \<close>

lemma collinear_vector_accel:
  "H{a \<bullet> v = \<parallel>a\<parallel> * \<parallel>v\<parallel>}
    ODE
   {a \<bullet> v = \<parallel>a\<parallel> * \<parallel>v\<parallel>}"
proof -
  have "H{a \<bullet> v \<ge> 0 \<and> (a \<bullet> v)\<^sup>2 = (a \<bullet> a) * (v \<bullet> v)}
        ODE
       {a \<bullet> v \<ge> 0 \<and> (a \<bullet> v)\<^sup>2 = (a \<bullet> a) * (v \<bullet> v)}"
    apply (dInduct_mega)
    using inner_commute by blast
  hence "H{a \<bullet> v \<ge> 0 \<and> a \<bullet> v = \<parallel>a\<parallel> * \<parallel>v\<parallel>}
          ODE
         {a \<bullet> v \<ge> 0 \<and> a \<bullet> v = \<parallel>a\<parallel> * \<parallel>v\<parallel>}"
    apply (rule hoare_conseq)
    apply (expr_auto)
     apply (simp add: power2_norm_eq_inner power_mult_distrib)
    apply (expr_auto)
    apply (metis Cauchy_Schwarz_eq2_iff Cauchy_Schwarz_eq_iff abs_of_nonneg)
    done

  thus ?thesis
    by (rule hoare_conseq; expr_auto)
qed

text \<open> Collinearity of the acceleration and velocity implies no rotational velocity \<close>

lemma "`a \<bullet> v = \<parallel>a\<parallel> * \<parallel>v\<parallel> \<longrightarrow> @\<omega> = 0`"
  apply (simp add: expr_defs lens_defs alpha_splits)
  apply (simp add: algebra_simps)
  by (smt inner_gt_zero_iff mult_nonneg_nonneg norm_ge_zero)

lemma "H{(a \<bullet> v = \<parallel>a\<parallel> * \<parallel>v\<parallel> \<and> s = \<parallel>v\<parallel>) \<and> t \<ge> 0 \<and> t < \<epsilon> \<and> 
        v = t *\<^sub>R a + $old:v \<and>
        p = (t\<^sup>2 * 0.5) *\<^sub>R a + t *\<^sub>R $old:v + $old:p}
        ODE
       {t \<ge> 0 \<and> t < \<epsilon> \<and> 
        v = t *\<^sub>R a + $old:v \<and>
        p = (t\<^sup>2 * 0.5) *\<^sub>R a + t *\<^sub>R $old:v + $old:p}"
  by (dInduct_mega facts: collinear_vector_accel)

lemma "H{a = 0 \<and> v = V}ODE{a = 0 \<and> v = V}"
  by (dInduct_mega)

declare eq_divide_eq_numeral1 [simp del]

lemma [simp]: "sqrt (1/100) = 1/10"
  by (rule real_sqrt_unique, simp_all add: field_simps)

lemma [simp]: "sqrt (9 / 64) = 0.375"
  by (rule real_sqrt_unique, simp_all add: field_simps)

text \<open> If the AMV is on course then the calculate acceleration vector is always
  collinear with the velocity vector. \<close>

lemma "H{s \<ge> 0 \<and> rs > s \<and> \<phi> = pi / 2 \<and> rh = pi / 2 
        \<and> v = s *\<^sub>R \<^bold>[[sin(\<phi>),cos(\<phi>)]\<^bold>]}
        AP
       {a \<bullet> v = \<parallel>a\<parallel> * \<parallel>v\<parallel>}"
  apply (hoare_wp_auto)
  apply (rename_tac s rs)
  apply (simp add: vec_norm)
  done

declare vec_simps [simp del]

lemma vs1: "\<^bold>[[k * x, k * y]\<^bold>] = k *\<^sub>R \<^bold>[[x, y]\<^bold>]"
  by (simp add: vec_simps(1))

lemma "H{s \<ge> 0 \<and> rs > s \<and> \<parallel>rh - \<phi>\<parallel> < \<phi>\<^sub>\<epsilon>
        \<and> v = s *\<^sub>R \<^bold>[[sin(\<phi>),cos(\<phi>)]\<^bold>]}
        AP
       {a \<bullet> v = \<parallel>a\<parallel> * \<parallel>v\<parallel>}"
  by (hoare_wp_auto)

text \<open> If the AMV is accelerating towards its orientation then the speed increases. \<close>


lemma 
  "H{(a \<bullet> v = \<parallel>a\<parallel> * \<parallel>v\<parallel> \<and> (a \<bullet> a) > 0) \<and> s \<ge> $old:s}
    ODE
   {s \<ge> $old:s}"
  by (dInduct_mega facts: collinear_vector_accel, simp add: inner_commute)

lemma no_turn_no_accel:
"H{(a = 0 \<and> s > 0) \<and> \<phi> = X} ODE {\<phi> = X}"
  by (dInduct_mega)

lemma no_turn_when_straight:
 "H{a \<bullet> v = \<parallel>a\<parallel> * \<parallel>v\<parallel> \<and> \<phi> = X} ODE {\<phi> = X}"
  apply (dInduct_mega facts: collinear_vector_accel)
  oops

text \<open> Link with CyPhyCircus. Differentiation on a domain. Unit vector d? DAEs via unknowns in ODE? \<close>

lemma "\<lbrakk> \<And> x y. P \<^bold>[[x, y]\<^bold>] \<rbrakk> \<Longrightarrow> P X"
  by (metis vector_2_cases)

lemma translational_speed: "H{s\<^sup>2 = (v \<bullet> v)}  ODE {s\<^sup>2 = (v \<bullet> v)}" by (dWeaken)

lemma "`s > 0 \<and> s\<^sup>2 = (v \<bullet> v) \<longrightarrow> s = \<parallel>v\<parallel>`"
  by (expr_simp, metis less_eq_real_def norm_eq_square)

find_theorems "(differentiable)" norm

lemma "\<lbrakk> (x::real) \<ge> 0; y \<ge> 0 \<rbrakk> \<Longrightarrow> x < y \<longleftrightarrow> x\<^sup>2 < y\<^sup>2"
  by (smt power2_le_imp_le)

lemma "0 \<le> arccos x \<longleftrightarrow> (-1 \<le> x \<and> x \<le> 1)"
  oops

lemma "H{True} AP {ft \<le> f\<^sub>m\<^sub>a\<^sub>x}"
  apply (simp add: wlp usubst_eval)
  oops

(*
lemma "{\<parallel>a\<parallel> \<le> f\<^sub>m\<^sub>a\<^sub>x / m} AP {\<parallel>a\<parallel> \<le> f\<^sub>m\<^sub>a\<^sub>x / m}"
  apply (hoare_wp_auto)
*)

lemma "H{\<parallel>a\<parallel> \<le> f\<^sub>m\<^sub>a\<^sub>x / m} ODE {\<parallel>a\<parallel> \<le> f\<^sub>m\<^sub>a\<^sub>x / m}"
  oops

lemma "H{\<phi> \<ge> 0} ODE {\<phi> \<ge> 0}"
  apply (dInduct)
  apply (expr_auto)
   apply (auto intro!: arccos_lbound)
  oops

lemma "H{ (\<parallel>angOfVec(nextWP - p) - \<phi>\<parallel>)\<^sup>2 < \<phi>\<^sub>\<epsilon>\<^sup>2 } ODE { (\<parallel>angOfVec(nextWP - p) - \<phi>\<parallel>)\<^sup>2 < \<phi>\<^sub>\<epsilon>\<^sup>2 }"
  apply (subst hoare_diff_inv_on')
  apply (subgoal_tac "(Collect ((\<le>) 0))\<^sub>e = ({t. t \<ge> 0})\<^sub>e")
   prefer 2 apply simp
  apply simp
  apply (rule_tac lderiv_rules)
     apply (simp_all add: ldifferentiable closure)
   apply (rule ldifferentiable, simp, expr_simp)
  oops

lemma "H{ \<parallel>angOfVec(nextWP - p) - \<phi>\<parallel> < \<phi>\<^sub>\<epsilon> } ODE { \<parallel>angOfVec(nextWP - p) - \<phi>\<parallel> < \<phi>\<^sub>\<epsilon> }"
  apply (dInduct)
  oops

end
