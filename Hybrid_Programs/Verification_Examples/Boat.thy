theory Boat
  imports "Hybrid-Verification.Hybrid_Verification"
begin

subsection \<open> Preliminaries \<close>

lit_vars

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

find_theorems vangle

abbreviation "angOfVec \<equiv> vangle \<^bold>[[0::real,100]\<^bold>]"

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
  by (simp add: vangle_def vec_norm)

lemma "angOfVec (Matrix[[1,0]]) = pi / 2" \<comment> \<open> 90 degree angOfVector \<close>
  by (simp add: vangle_def)

lemma arccos_inv_sqrt2: "arccos (1 / sqrt 2) = pi / 4"
  by (smt arccos_cos arccos_minus_1 arcsin_minus_1 arcsin_plus_arccos arctan arctan_less_pi4_pos arctan_one arctan_zero_zero cos_45 eq_divide_eq mult_cancel_left1 real_div_sqrt real_divide_square_eq)

lemma "angOfVec (Matrix[[1,1]]) = pi / 4" \<comment> \<open> 45 degree angOfVector \<close>
  by (simp add: vangle_def arccos_inv_sqrt2 vec_norm)

lemma "angDiff (pi/2) (pi/4) False = pi/4"
  by (simp add: angDiff_def)

lemma "angDiff (pi) (pi/4) False = 3 / 4 * pi"
  by (simp add: angDiff_def)

datatype OPMode = OCM | HCM | MOM | CAM

dataspace AMV =
  constants
    S    :: real
    f\<^sub>m\<^sub>a\<^sub>x  :: real
  assumes
    f\<^sub>m\<^sub>a\<^sub>x: "f\<^sub>m\<^sub>a\<^sub>x \<ge> 0"
  variables
    \<comment> \<open> Continuous Variables \<close>
    p :: "real vec[2]" \<comment> \<open> Position \<close>
    v :: "real vec[2]" \<comment> \<open> Velocity \<close>
    a :: "real vec[2]" \<comment> \<open> Acceleration \<close>
    \<phi> :: "real" \<comment> \<open> Heading \<close>
    s :: "real" \<comment> \<open> Linear Speed \<close>
    \<comment> \<open> Discrete Variables\<close>
    wps :: "(real vec[2]) list" \<comment> \<open> Path of way points \<close>
    org :: "(real vec[2]) set" \<comment> \<open> Obstacle register \<close>
    rs      :: "real" \<comment> \<open> Requested speed \<close>
    rh      :: "real" \<comment> \<open> Requested heading \<close>

context AMV
begin

abbreviation "ax \<equiv> (s *\<^sub>R \<^bold>[[sin(\<phi>), cos(\<phi>)]\<^bold>] = v \<and> 0 \<le> s \<and> s \<le> S)\<^sup>e"

abbreviation "\<omega> \<equiv> (if (\<parallel>v\<parallel> = 0) then 0 else arccos((v + a) \<bullet> v / (\<parallel>v + a\<parallel> * \<parallel>v\<parallel>)))\<^sub>e"

abbreviation "ODE \<equiv>
   { p` = v
   , v` = a
   , a` = 0
   , \<phi>` = @\<omega>
   , s` = if s \<noteq> 0 then (v \<bullet> a) / s else \<parallel>a\<parallel>
   | @ax }"

text \<open> Heavily simplified for the purpose of example \<close>

abbreviation "Autopilot \<equiv> rs ::= 1; rs ::= 0"

lemma "ODE nmods (rs, rh, wps, org)" 
  by (auto intro!: closure; subst_eval)

lemma "Autopilot nmods (p, a, v, s)"
  by (auto intro!: closure; subst_eval)

lemma "\<^bold>{s\<^sup>2 = v \<bullet> v\<^bold>} ODE \<^bold>{s\<^sup>2 = v \<bullet> v\<^bold>}"
  by (dWeaken, metis orient_vec_mag_n self_dot)

lemma "\<^bold>{a = 0 \<and> v = V\<^bold>} ODE \<^bold>{a = 0 \<and> v = V\<^bold>}" by dInduct_mega

lemma "\<^bold>{(a = 0 \<and> s > 0) \<and> \<phi> = X\<^bold>} ODE \<^bold>{\<phi> = X\<^bold>}" by dInduct_mega

lemma "\<^bold>{a \<bullet> v \<ge> 0 \<and> (a \<bullet> v)\<^sup>2 = (a \<bullet> a) * (v \<bullet> v)\<^bold>}
        ODE
       \<^bold>{a \<bullet> v \<ge> 0 \<and> (a \<bullet> v)\<^sup>2 = (a \<bullet> a) * (v \<bullet> v)\<^bold>}"
  by (dInduct_mega, metis inner_commute)

end

end