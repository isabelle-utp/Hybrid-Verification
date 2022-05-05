section \<open> Lie Derivatives \<close>

theory HS_Lie_Derivatives
  imports HS_Lens_Spartan
begin

subsection \<open> Differentiability \<close>

definition expr_differentiable_when_on ::
  "('a::real_normed_vector, 's) expr \<Rightarrow> ('c::real_normed_vector \<Longrightarrow> 's) \<Rightarrow> (bool, 's) expr \<Rightarrow> bool"
  where [expr_defs]: "expr_differentiable_when_on f a d = (\<forall> s. (\<forall> v. d (put\<^bsub>a\<^esub> s v)) \<longrightarrow> (\<lambda> x. f (put\<^bsub>a\<^esub> s x)) differentiable (at (get\<^bsub>a\<^esub> s)))"

syntax 
  "_expr_differentiable_when_on" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("differentiable\<^sub>e _ on _ when _" [0, 0, 100] 100)
  "_expr_differentiable_on" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("differentiable\<^sub>e _ on _" [0, 100] 100)

translations 
  "differentiable\<^sub>e f on a when d" == "CONST expr_differentiable_when_on (f)\<^sub>e a (d)\<^sub>e"
  "differentiable\<^sub>e f on a" == "CONST expr_differentiable_when_on (f)\<^sub>e a (CONST True)\<^sub>e"

abbreviation expr_differentiable ("differentiable\<^sub>e") where
"expr_differentiable f \<equiv> differentiable\<^sub>e f on id_lens"

lemma differentiable_number [closure]:
  "differentiable\<^sub>e 0 on a when p" "differentiable\<^sub>e 1 on a when p" "differentiable\<^sub>e (numeral \<guillemotleft>n\<guillemotright>) on a when p"
  by (simp_all add: expr_defs)

lemma differentiable_lit [closure]:
  "differentiable\<^sub>e \<guillemotleft>x\<guillemotright> on a when p"
  by (simp_all add: expr_defs)

lemma has_derivative_discr_expr:
  "\<lbrakk> vwb_lens a; $a \<sharp> (e)\<^sub>e \<rbrakk> \<Longrightarrow> ((\<lambda>x. e (put\<^bsub>a\<^esub> s x)) has_derivative (\<lambda> x. 0)) (at (get\<^bsub>a\<^esub> s))"
  by (expr_auto)

lemma differentiable_discr_expr [closure]:
  "\<lbrakk> vwb_lens a; $a \<sharp> (e)\<^sub>e \<rbrakk> \<Longrightarrow> differentiable\<^sub>e e on a"
  using differentiable_def has_derivative_discr_expr
  by (fastforce simp add: expr_differentiable_when_on_def)

lemma differentiable_plus [closure]:
  assumes "differentiable\<^sub>e e on a when p" "differentiable\<^sub>e f on a when p"
  shows "differentiable\<^sub>e (e + f) on a when p"
  using assms by (simp add: expr_defs)

lemma differentiable_minus [closure]:
  assumes "differentiable\<^sub>e e on a when p" "differentiable\<^sub>e f on a when p"
  shows "differentiable\<^sub>e (e - f) on a when p"
  using assms by (simp add: expr_defs)

lemma differentiable_times [closure]:
  fixes e f :: "'a \<Rightarrow> 'b::real_normed_field"
  assumes "differentiable\<^sub>e e on a when p" "differentiable\<^sub>e f on a when p"
  shows "differentiable\<^sub>e (e * f) on a when p"
  using assms by (simp add: expr_defs)

lemma differentiable_inverse [closure]:
  fixes e f :: "'a \<Rightarrow> 'b::real_normed_field"
  assumes "`p \<longrightarrow> e \<noteq> 0`" "differentiable\<^sub>e e on a when p"
  shows "differentiable\<^sub>e (inverse e) on a when p"
  using assms by (auto simp add: expr_defs)

lemma differentiable_divide [closure]:
  fixes e f :: "'a \<Rightarrow> 'b::real_normed_field"
  assumes "`p \<longrightarrow> f \<noteq> 0`" "differentiable\<^sub>e e on a when p" "differentiable\<^sub>e f on a when p"
  shows "differentiable\<^sub>e (e / f) on a when p"
  using assms by (auto simp add: expr_defs)

find_theorems "(has_derivative)" "inverse"

lemma differentiable_inner [closure]:
  assumes "differentiable\<^sub>e e on a when p" "differentiable\<^sub>e f on a when p"
  shows "differentiable\<^sub>e (e \<bullet> f) on a when p"
  using assms by (simp add: expr_defs)

lemma differentiable_scaleR [closure]:
  assumes "differentiable\<^sub>e e on a when p" "differentiable\<^sub>e f on a when p"
  shows "differentiable\<^sub>e (e *\<^sub>R f) on a when p"
  using assms by (simp add: expr_defs)

lemma differentiable_power [closure]:
  fixes e :: "'a \<Rightarrow> 'b::real_normed_field"
  assumes "differentiable\<^sub>e e on a when p"
  shows "differentiable\<^sub>e (e^\<guillemotleft>n\<guillemotright>) on a when p"
  using assms by (simp add: expr_defs)

lemma sublens_obs_create: "\<lbrakk> mwb_lens X; Y \<subseteq>\<^sub>L X \<rbrakk> \<Longrightarrow> get\<^bsub>Y\<^esub> (put\<^bsub>X\<^esub> v s) = get\<^bsub>Y\<^esub> (create\<^bsub>X\<^esub> s)"
  by (simp add: lens_create_def sublens_obs_get)

lemma differentiable_cvar [closure]:
  assumes "vwb_lens a" "x \<subseteq>\<^sub>L a" "bounded_linear (get\<^bsub>x /\<^sub>L a\<^esub>)"
  shows "differentiable\<^sub>e $x on a when p"
  using assms apply (auto simp add: expr_defs lens_quotient_def sublens_obs_create)
  using bounded_linear_imp_differentiable by blast

lemma differentiable_dvar [closure]:
  assumes "x \<bowtie> a"
  shows "differentiable\<^sub>e $x on a when p"
  using assms by (auto simp add: expr_defs)

text \<open> The following simplification rules help with automating Lie derivatives \<close>

declare lens_plus_right_sublens [simp] 

subsection \<open> Lie Derivatives \<close>

definition lie_deriv_on :: 
  "('s \<Rightarrow> 's) \<Rightarrow> ('s \<Rightarrow> 'a::real_normed_vector) \<Rightarrow> ('c::real_normed_vector \<Longrightarrow> 's) \<Rightarrow> ('s \<Rightarrow> 'a)"
  where [expr_defs]: "lie_deriv_on \<sigma> f a = (\<lambda> s. frechet_derivative (\<lambda> x. f (put\<^bsub>a\<^esub> s x)) (at (get\<^bsub>a\<^esub> s)) (get\<^bsub>a\<^esub> (\<sigma> s)))"

expr_ctr lie_deriv_on

syntax
  "_lie_deriv_on" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"  ("\<L>\<^bsub>_\<^esub> _ on _" [0, 0, 100] 100)
  "_lie_deriv"    :: "logic \<Rightarrow> logic \<Rightarrow> logic"  ("\<L>\<^bsub>_\<^esub> _ " [0, 100] 100)

translations
  "_lie_deriv_on \<sigma> f a" == "CONST lie_deriv_on \<sigma> (f)\<^sub>e a"
  "_lie_deriv \<sigma> f" == "CONST lie_deriv_on \<sigma> (f)\<^sub>e (CONST id_lens)"

named_theorems lie_deriv

lemma lie_deriv_zero [lie_deriv]: "\<L>\<^bsub>F\<^esub> 0 on a = (0)\<^sub>e"
  by (simp add: expr_defs)

lemma lie_deriv_one [lie_deriv]: "\<L>\<^bsub>F\<^esub> 1 on a = (0)\<^sub>e"
  by (simp add: expr_defs)

lemma lie_deriv_numeral [lie_deriv]: "\<L>\<^bsub>F\<^esub> numeral \<guillemotleft>n\<guillemotright> on a = (0)\<^sub>e"
  by (simp add: expr_defs)

lemma lie_deriv_lit [lie_deriv]: "\<L>\<^bsub>F\<^esub> \<guillemotleft>n\<guillemotright> on a = (0)\<^sub>e"
  by (simp add: expr_defs)

lemma lie_deriv_discr_expr [lie_deriv]:
  "\<lbrakk> vwb_lens a; $a \<sharp> (e)\<^sub>e \<rbrakk> \<Longrightarrow> \<L>\<^bsub>f\<^esub> e on a = (0)\<^sub>e"
  by (expr_simp)

lemma lie_deriv_plus [lie_deriv]:
  "\<lbrakk> differentiable\<^sub>e e on a ; differentiable\<^sub>e f on a \<rbrakk> 
  \<Longrightarrow> \<L>\<^bsub>F'\<^esub> e + f on a = (\<L>\<^bsub>F'\<^esub> e on a + \<L>\<^bsub>F'\<^esub> f on a)\<^sub>e"
  by (simp add: expr_defs fun_eq_iff frechet_derivative_plus)

lemma lie_deriv_minus [lie_deriv]:
  "\<lbrakk> differentiable\<^sub>e e on a ; differentiable\<^sub>e f on a \<rbrakk> 
  \<Longrightarrow> \<L>\<^bsub>F'\<^esub> e - f on a = (\<L>\<^bsub>F'\<^esub> e on a - \<L>\<^bsub>F'\<^esub> f on a)\<^sub>e"
  by (simp add: expr_defs fun_eq_iff frechet_derivative_minus)

lemma lie_deriv_times [lie_deriv]:
  fixes f g :: "'a \<Rightarrow> 'b::real_normed_field"
  assumes "vwb_lens a" "differentiable\<^sub>e e on a" "differentiable\<^sub>e f on a"
  shows "\<L>\<^bsub>F'\<^esub> (e * f) on a = (e * \<L>\<^bsub>F'\<^esub> f on a + \<L>\<^bsub>F'\<^esub> e on a * f)\<^sub>e"
  using assms by (simp add: expr_defs fun_eq_iff frechet_derivative_mult assms)

lemma lie_deriv_inner [lie_deriv]:
  fixes a :: "'c::{real_normed_vector, real_inner} \<Longrightarrow> 'a"
  assumes "vwb_lens a" "differentiable\<^sub>e e on a" "differentiable\<^sub>e f on a"
  shows "\<L>\<^bsub>F'\<^esub> (e \<bullet> f) on a = (e \<bullet> \<L>\<^bsub>F'\<^esub> f on a + \<L>\<^bsub>F'\<^esub> e on a \<bullet> f)\<^sub>e"
  using assms by (simp add: expr_defs fun_eq_iff frechet_derivative_inner)

lemma lie_deriv_scaleR [lie_deriv]:
  fixes a :: "'c::{real_normed_vector} \<Longrightarrow> 'a"
  assumes "vwb_lens a" "differentiable\<^sub>e e on a" "differentiable\<^sub>e f on a"
  shows "\<L>\<^bsub>F'\<^esub> (e *\<^sub>R f) on a = (e *\<^sub>R \<L>\<^bsub>F'\<^esub> f on a + \<L>\<^bsub>F'\<^esub> e on a *\<^sub>R f)\<^sub>e"
  using assms by (simp add: expr_defs fun_eq_iff frechet_derivative_scaleR)

lemma lie_deriv_inverse [lie_deriv]:
  fixes a :: "'c::real_normed_vector \<Longrightarrow> 'a" and e :: "'a \<Rightarrow> 'b::real_normed_div_algebra"
  assumes  "vwb_lens a" "differentiable\<^sub>e e on a" "`e \<noteq> 0`"
  shows "\<L>\<^bsub>F'\<^esub> (inverse e) on a = (- (inverse e * \<L>\<^bsub>F'\<^esub> e on a * inverse e))\<^sub>e"
  using assms by (simp add: expr_defs fun_eq_iff frechet_derivative_inverse)

lemma lie_deriv_divide [lie_deriv]:
  fixes a :: "'c::real_normed_vector \<Longrightarrow> 'a" and e :: "'a \<Rightarrow> 'b::real_normed_field"
  assumes  "vwb_lens a" "differentiable\<^sub>e e on a" "differentiable\<^sub>e f on a" "`f \<noteq> 0`"
  shows "\<L>\<^bsub>F'\<^esub> (e / f) on a = (\<L>\<^bsub>F'\<^esub> e on a / f - e * (\<L>\<^bsub>F'\<^esub> f on a / f\<^sup>2))\<^sub>e"
  using assms by (simp add: expr_defs fun_eq_iff frechet_derivative_divide)

lemma lie_deriv_power [lie_deriv]:
  fixes e :: "'s \<Rightarrow> 'a::{ordered_euclidean_space, real_normed_field}"
  and a :: "'c::ordered_euclidean_space \<Longrightarrow> 's"
  assumes "vwb_lens a" "differentiable\<^sub>e e on a"
  shows "\<L>\<^bsub>F'\<^esub> (e ^ \<guillemotleft>n\<guillemotright>) on a = (of_nat \<guillemotleft>n\<guillemotright> * \<L>\<^bsub>F'\<^esub> e on a * e ^ (\<guillemotleft>n\<guillemotright> - 1))\<^sub>e"
  using assms by (simp add: expr_defs fun_eq_iff frechet_derivative_power)

lemma lie_deriv_ln [lie_deriv]:
  fixes e :: "'s \<Rightarrow> real"
  and a :: "'c::{banach, real_normed_algebra_1} \<Longrightarrow> 's"
  assumes "vwb_lens a" "differentiable\<^sub>e e on a" "`e > 0`"
  shows "\<L>\<^bsub>F'\<^esub> (ln e) on a = (\<L>\<^bsub>F'\<^esub> e on a / e)\<^sub>e"
  using assms by (simp add: expr_defs frechet_derivative_ln divide_inverse)
  
lemma lie_deriv_sin [lie_deriv]:
  fixes e :: "'s \<Rightarrow> real"
  assumes "vwb_lens a" "differentiable\<^sub>e e on a"
  shows "\<L>\<^bsub>F'\<^esub> (sin e) on a = (\<L>\<^bsub>F'\<^esub> e on a * cos e)\<^sub>e"
  using assms by (simp add: expr_defs fun_eq_iff frechet_derivative_sin)

declare lens_quotient_plus_den1 [simp]
declare lens_quotient_plus_den2 [simp]

lemma lie_deriv_cont_var [lie_deriv]:
  assumes "vwb_lens a" "x \<subseteq>\<^sub>L a" "bounded_linear (get\<^bsub>x /\<^sub>L a\<^esub>)"
  shows "\<L>\<^bsub>F'\<^esub> $x on a = \<langle>F'\<rangle>\<^sub>s x"
  using assms
  apply (auto simp add: expr_defs lens_quotient_def fun_eq_iff)
  apply (rename_tac xa)
  apply (subgoal_tac "(\<lambda>xb. get\<^bsub>x\<^esub> (put\<^bsub>a\<^esub> xa xb)) = (\<lambda> xb. get\<^bsub>x\<^esub> (create\<^bsub>a\<^esub> xb))")
  defer
   apply (metis lens_create_def sublens_obs_get vwb_lens_mwb)
  apply (simp)
  apply (metis bounded_linear_imp_has_derivative frechet_derivative_at sublens'_prop2 sublens_implies_sublens' sublens_pres_vwb)
  done

text \<open> Discrete variables are constant during evolution, and so their derivative is 0 \<close>

lemma lie_deriv_disc_var [lie_deriv]:
  assumes "vwb_lens a" "x \<bowtie> a"
  shows "\<L>\<^bsub>F'\<^esub> $x on a = (0)\<^sub>e"
  using assms
  by (auto simp add: expr_defs lens_quotient_def fun_eq_iff)

(* FIXME: To support unique solutions, we need a way of taking the derivative of a substitution. *)

definition differentiable_subst :: "('a::real_normed_vector \<Longrightarrow> 's) \<Rightarrow> ('s \<Rightarrow> 's) \<Rightarrow> 'a set \<Rightarrow> bool" where
"differentiable_subst a \<sigma> T = (\<forall> s. \<forall> t\<in>T. (\<lambda> c. get\<^bsub>a\<^esub> (\<sigma> (put\<^bsub>a\<^esub> s c))) differentiable (at t))"

definition frechet_derivative_subst :: "('a::real_normed_vector \<Longrightarrow> 's) \<Rightarrow> ('s \<Rightarrow> 's) \<Rightarrow> ('s \<Rightarrow> 's)" ("\<partial>\<^sub>s") where
"frechet_derivative_subst a \<sigma> = (\<lambda> s. put\<^bsub>a\<^esub> s (frechet_derivative (\<lambda> c. get\<^bsub>a\<^esub> (\<sigma> (put\<^bsub>a\<^esub> s c))) (at (get\<^bsub>a\<^esub> s)) (get\<^bsub>a\<^esub> s)))"

thm continuous_rhs_def
(* continuous_subst_on :: "('a::real_normed_vector \<Longrightarrow> 's) \<Rightarrow> ('s \<Rightarrow> 's) \<Rightarrow> 'a set \<Rightarrow> bool" where *)
definition continuous_subst_on :: "('a::real_normed_vector \<Longrightarrow> 's::topological_space) \<Rightarrow> ('s \<Rightarrow> 's) \<Rightarrow> 'a set \<Rightarrow> 's set \<Rightarrow> bool" where
"continuous_subst_on a \<sigma> T S = continuous_rhs T S (\<lambda>c s. get\<^bsub>a\<^esub> (\<sigma> (put\<^bsub>a\<^esub> s c)))"

lemma frechet_derivative_subst_id_subst:
  "vwb_lens a \<Longrightarrow> \<partial>\<^sub>s a [\<leadsto>] = [\<leadsto>]"
  by (simp add: frechet_derivative_subst_def subst_id_def)

lemma frechet_derivative_on_singleton:
  "vwb_lens x \<Longrightarrow> \<partial>\<^sub>s x [x \<leadsto> e] = [x \<leadsto> \<L>\<^bsub>[\<leadsto>]\<^esub> e on x]"
  by (simp add: frechet_derivative_subst_def expr_defs fun_eq_iff)


lemma c1_local_lipschitz_on:
  fixes a :: "('a::{heine_borel,banach,euclidean_space, times}) \<Longrightarrow> 's"
  assumes "vwb_lens a" "differentiable_subst a \<sigma> UNIV" 
    "\<forall>z s. continuous_on UNIV (\<lambda>(t::real,p:: 'a). \<partial> (\<lambda>c. get\<^bsub>a\<^esub> (\<sigma> (put\<^bsub>a\<^esub> s c))) (at p) z)"
  shows "local_lipschitz_on a (UNIV :: real set) UNIV \<sigma>"
proof (unfold local_lipschitz_on_def, clarify)
  fix s
  from assms(1,2)
  have 1:"\<forall>c'. D (\<lambda>c. get\<^bsub>a\<^esub> (\<sigma> (put\<^bsub>a\<^esub> s c))) \<mapsto> \<partial> (\<lambda>c. get\<^bsub>a\<^esub> (\<sigma> (put\<^bsub>a\<^esub> s c))) (at c') at c'"
    by (simp add: differentiable_subst_def frechet_derivative_works)

  have obs: "\<forall>t. \<exists>f'. (D (\<lambda>c. get\<^bsub>a\<^esub> (\<sigma> (put\<^bsub>a\<^esub> s c))) \<mapsto> f' (at t))"
  using assms(2) unfolding differentiable_def differentiable_subst_def by clarsimp

  show "local_lipschitz UNIV UNIV (\<lambda>t::real. \<lambda> c. get\<^bsub>a\<^esub> (\<sigma> (put\<^bsub>a\<^esub> s c)))"
    apply(rule c1_implies_local_lipschitz[where (* second attempt *)
          f'="\<lambda>(t, c'). Blinfun (\<partial> (\<lambda>c. get\<^bsub>a\<^esub> (\<sigma> (put\<^bsub>a\<^esub> s c))) (at c'))"])
       apply simp_all
     apply(subst Blinfun_inverse)
    using "1" apply blast
    using 1 apply blast
    apply(rule continuous_on_blinfun_componentwise)
    apply (simp add: prod.case_eq_if)
    apply(subst bounded_linear_Blinfun_apply, clarsimp)
    using obs apply(erule_tac x=b in allE, clarsimp)
     apply(erule_tac x=b in allE, clarsimp)
    using has_derivative_unique 1 apply blast 
    using assms(1,3) unfolding continuous_subst_on_def 
      frechet_derivative_subst_def continuous_rhs_def
    by (clarsimp simp: prod.case_eq_if)
qed

lemma c1_local_lipschitz_on:
  fixes a :: "('a::{heine_borel,banach,euclidean_space, times}) \<Longrightarrow> 's"
  assumes "vwb_lens a" "differentiable_subst a \<sigma> UNIV" "continuous_subst_on a (\<partial>\<^sub>s a \<sigma>) UNIV"
    "\<exists> f. \<forall> x s. \<partial> (\<lambda>c. get\<^bsub>a\<^esub> (\<sigma> (put\<^bsub>a\<^esub> s c))) (at x) = f" 
  shows "local_lipschitz_on a (UNIV :: real set) UNIV \<sigma>"
proof (unfold local_lipschitz_on_def, clarify)
  fix s
  from assms 
  have 1:"\<forall>c'. D (\<lambda>c. get\<^bsub>a\<^esub> (\<sigma> (put\<^bsub>a\<^esub> s c))) \<mapsto> \<partial> (\<lambda>c. get\<^bsub>a\<^esub> (\<sigma> (put\<^bsub>a\<^esub> s c))) (at c') at c'"
    by (simp add: differentiable_subst_def frechet_derivative_works)

  obtain f where f: "\<And> x s. \<partial> (\<lambda>c. get\<^bsub>a\<^esub> (\<sigma> (put\<^bsub>a\<^esub> s c))) (at x) = f" "bounded_linear f"
    using "1" assms(4) by force

  have 2:"\<And> c'. bounded_linear (\<partial> (\<lambda>c. get\<^bsub>a\<^esub> (\<sigma> (put\<^bsub>a\<^esub> s c))) (at c'))"
    using "1" by blast

  hence 3: "\<And> S c'. continuous_on S (\<partial> (\<lambda>c. get\<^bsub>a\<^esub> (\<sigma> (put\<^bsub>a\<^esub> s c))) (at c'))"
    by (simp add: linear_continuous_on)

  show "local_lipschitz UNIV UNIV (\<lambda>t::real. \<lambda> c. get\<^bsub>a\<^esub> (\<sigma> (put\<^bsub>a\<^esub> s c)))"
    apply(rule c1_implies_local_lipschitz[where (* second attempt *)
          f'="\<lambda>(t, c'). Blinfun (\<partial> (\<lambda>c. get\<^bsub>a\<^esub> (\<sigma> (put\<^bsub>a\<^esub> s c))) (at c'))"])
       apply simp_all
     apply(subst Blinfun_inverse)
    using "1" apply blast
    using 1 apply blast
    apply(rule continuous_on_blinfun_componentwise)
    apply (simp add: prod.case_eq_if bounded_linear_Blinfun_apply 2 f)
    done
qed



subsection \<open> Lie Derivative Invariants \<close>

lemma derivation_lemma1:
  fixes a :: "'c::real_normed_vector \<Longrightarrow> 's" and F' :: "'s \<Rightarrow> 's"
  assumes "vwb_lens a" "differentiable\<^sub>e e on a" "(F has_vector_derivative get\<^bsub>a\<^esub> (F' (put\<^bsub>a\<^esub> s (F t)))) (at t within A)"
  shows "((\<lambda>x. e (put\<^bsub>a\<^esub> s x)) \<circ> F has_vector_derivative (\<L>\<^bsub>F'\<^esub> e on a) (put\<^bsub>a\<^esub> s (F t))) (at t within A)"
  using assms
  apply (simp add: lens_defs expr_defs frechet_derivative_works)
  apply (rule vector_derivative_diff_chain_within)
   apply blast
  apply (rule has_derivative_at_withinI)
  apply (drule_tac x="put\<^bsub>a\<^esub> s (F t)" in spec)
  apply (simp)
  done

thm expr_differentiable_when_on_def

lemma lie_diff_inv_on_eq:
  fixes e :: "'s \<Rightarrow> _::real_inner" and a :: "'c::real_normed_vector \<Longrightarrow> 's"
  assumes "vwb_lens a" "differentiable\<^sub>e e on a" "`B \<longrightarrow> \<L>\<^bsub>F\<^esub> e on a = 0`"
  shows "diff_inv_on (e = 0)\<^sub>e a (\<lambda> _. F) ({t. t \<ge> 0})\<^sub>e UNIV 0 (B)\<^sub>e"
  using assms apply(simp_all add: diff_inv_on_eq ivp_sols_def)
proof(auto simp: lens_defs expr_defs)
  fix t :: real and X :: "real \<Rightarrow> 'c" and s :: "'s"
  assume a1:"\<forall>s. (\<lambda>x. e (put\<^bsub>a\<^esub> s x)) differentiable at (get\<^bsub>a\<^esub> s)" and a2: "0 \<le> t" 
    and a3: "(X has_vderiv_on (\<lambda>x. get\<^bsub>a\<^esub> (F (put\<^bsub>a\<^esub> s (X x))))) (Collect ((\<le>) 0))" 
    "\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> B (put\<^bsub>a\<^esub> s (X \<tau>))" and a5: "X 0 = get\<^bsub>a\<^esub> s" and a6: "e s = 0"
    and a4: "\<forall>s. B s \<longrightarrow> \<partial> (\<lambda>x. e (put\<^bsub>a\<^esub> s x)) (at (get\<^bsub>a\<^esub> s)) (get\<^bsub>a\<^esub> (F s)) = 0"
  show "(\<lambda>x. e (put\<^bsub>a\<^esub> s x)) (X t) = 0"
  proof (cases "t = 0")
    case True
    then show ?thesis
      using a5 a6 assms(1) by auto
  next
    case False
    hence t: "t > 0"
      using a2 by linarith
    have g: "\<forall>t\<in>{0..t}. B (put\<^bsub>a\<^esub> s (X t))"
      by (simp add: a3(2))
    hence d0: "\<forall>t\<in>{0..t}. \<partial> (\<lambda>x. e (put\<^bsub>a\<^esub> s x)) (at (X t)) (get\<^bsub>a\<^esub> (F (put\<^bsub>a\<^esub> s (X t)))) = 0"
      using a4 by (auto simp add: assms(1))
    from a1 have dE: "\<forall>\<tau>\<in>{0..t}. ((\<lambda>x. e (put\<^bsub>a\<^esub> s x)) has_derivative \<partial> (\<lambda>x. e (put\<^bsub>a\<^esub> s x)) (at (X \<tau>))) (at (X \<tau>))"
      by (auto simp add: frechet_derivative_works, drule_tac x="put\<^bsub>a\<^esub> s (X \<tau>)" in spec, simp add: assms)
    have d1: "\<forall>\<tau>\<in>{0..t}. ((\<lambda>x. e (put\<^bsub>a\<^esub> s x)) \<circ> X has_vector_derivative (\<L>\<^bsub>F\<^esub> e on a) (put\<^bsub>a\<^esub> s (X \<tau>))) (at \<tau> within {0..t})"
      using a3 apply(clarsimp simp: has_vderiv_on_def)
      apply (rule derivation_lemma1[OF assms(1,2)], simp add: has_vector_derivative_def)
      by (rule has_derivative_subset[of _ _ _ "Collect ((\<le>) 0)"], auto)
    hence d2: "\<forall>\<tau>\<in>{0..t}. ((\<lambda>x. e (put\<^bsub>a\<^esub> s x)) \<circ> X has_vector_derivative 0) (at \<tau> within {0..t})"
      using a4 g apply(subst (asm) lie_deriv_on_def)
      by (metis SEXP_def)
    have c: "continuous_on {0..t} ((\<lambda>x. e (put\<^bsub>a\<^esub> s x)) \<circ> X)"
      using continuous_on_vector_derivative d2 by fastforce
    have d3: "(\<And>x. 0 < x \<Longrightarrow> x < t \<Longrightarrow> D ((\<lambda>x. e (put\<^bsub>a\<^esub> s x)) \<circ> X) \<mapsto> (\<lambda>x. 0) at x)"
      by (metis atLeastAtMost_iff at_within_Icc_at d2 frechet_derivative_at has_derivative_const has_vector_derivative_const has_vector_derivative_def less_eq_real_def)
    have "\<parallel>((\<lambda>x. e (put\<^bsub>a\<^esub> s x)) \<circ> X) t - ((\<lambda>x. e (put\<^bsub>a\<^esub> s x)) \<circ> X) 0\<parallel> \<le> \<parallel>0\<parallel>"
      using mvt_general[OF t c d3] by auto
    hence "((\<lambda>x. e (put\<^bsub>a\<^esub> s x)) \<circ> X) t - ((\<lambda>x. e (put\<^bsub>a\<^esub> s x)) \<circ> X) 0 = 0" by simp
    thus "(\<lambda>x. e (put\<^bsub>a\<^esub> s x)) (X t) = 0"
      by (simp add: a6 a5 assms(1))
  qed
qed

lemma lie_diff_inv_simple:
  fixes e :: "'s::real_normed_vector \<Rightarrow> real"
  assumes "differentiable\<^sub>e e" "`B \<longrightarrow> \<L>\<^bsub>F\<^esub> e = 0`"
  shows "diff_inv ({t. t \<ge> 0})\<^sub>e UNIV (B)\<^sub>e (\<lambda> _. F) 0 (e = 0)\<^sub>e "
  apply (simp add: diff_inv_on_id_lens[THEN sym])
  apply (rule lie_diff_inv_on_eq)
    apply (simp_all add: assms)
  done

lemma lie_diff_inv_on_le_less:
  fixes e :: "'s \<Rightarrow> real" and a :: "'c::real_normed_vector \<Longrightarrow> 's"
  assumes "vwb_lens a" "differentiable\<^sub>e e on a" "`B \<longrightarrow> \<L>\<^bsub>F\<^esub> e on a \<ge> 0`"
  shows lie_diff_inv_on_leq: "diff_inv_on (e \<ge> 0)\<^sub>e a (\<lambda> _. F) ({t. t \<ge> 0})\<^sub>e UNIV 0 (B)\<^sub>e"
    and lie_diff_inv_on_less: "diff_inv_on (e > 0)\<^sub>e a (\<lambda> _. F) ({t. t \<ge> 0})\<^sub>e UNIV 0 (B)\<^sub>e"
  using assms apply(simp_all add: diff_inv_on_eq ivp_sols_def)
proof(auto simp: lens_defs expr_defs)
  fix t :: real and X :: "real \<Rightarrow> 'c" and s :: "'s"
  assume a1:"\<forall>s. (\<lambda>x. e (put\<^bsub>a\<^esub> s x)) differentiable at (get\<^bsub>a\<^esub> s)" and a2: "0 \<le> t" 
    and a3: "(X has_vderiv_on (\<lambda>x. get\<^bsub>a\<^esub> (F (put\<^bsub>a\<^esub> s (X x))))) (Collect ((\<le>) 0))" 
    "\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> B (put\<^bsub>a\<^esub> s (X \<tau>))" and a5: "X 0 = get\<^bsub>a\<^esub> s"
    and a4: "\<forall>s. B s \<longrightarrow> 0 \<le> \<partial> (\<lambda>x. e (put\<^bsub>a\<^esub> s x)) (at (get\<^bsub>a\<^esub> s)) (get\<^bsub>a\<^esub> (F s))"
  have g: "\<forall>t\<in>{0..t}. B (put\<^bsub>a\<^esub> s (X t))"
    by (simp add: a3(2))
  hence d0: "\<forall>t\<in>{0..t}. 0 \<le> \<partial> (\<lambda>x. e (put\<^bsub>a\<^esub> s x)) (at (X t)) (get\<^bsub>a\<^esub> (F (put\<^bsub>a\<^esub> s (X t))))"
    using a4 by (auto simp: assms(1))
  from a1 have dE: "\<forall>\<tau>\<in>{0..t}. ((\<lambda>x. e (put\<^bsub>a\<^esub> s x)) has_derivative \<partial> (\<lambda>x. e (put\<^bsub>a\<^esub> s x)) (at (X \<tau>))) (at (X \<tau>))"
    by (auto simp add: frechet_derivative_works, drule_tac x="put\<^bsub>a\<^esub> s (X \<tau>)" in spec, simp add: assms)
  have d1: "\<forall>\<tau>\<in>{0..t}. ((\<lambda>x. e (put\<^bsub>a\<^esub> s x)) \<circ> X has_vector_derivative (\<L>\<^bsub>F\<^esub> e on a) (put\<^bsub>a\<^esub> s (X \<tau>))) (at \<tau> within {0..t})"
    using a3 apply(clarsimp simp: has_vderiv_on_def)
    apply (rule derivation_lemma1[OF assms(1,2)], simp add: has_vector_derivative_def)
    by (rule has_derivative_subset[of _ _ _ "Collect ((\<le>) 0)"], auto)
  hence "\<forall>\<tau>\<in>{0..t}. ((\<lambda>x. e (put\<^bsub>a\<^esub> s x)) \<circ> X has_derivative (\<lambda>x. x *\<^sub>R (\<L>\<^bsub>F\<^esub> e on a) (put\<^bsub>a\<^esub> s (X \<tau>)))) (at \<tau> within {0..t})"
    unfolding has_vector_derivative_def by simp
  hence "\<exists>x\<in>{0..t}. ((\<lambda>x. e (put\<^bsub>a\<^esub> s x)) \<circ> X) t - ((\<lambda>x. e (put\<^bsub>a\<^esub> s x)) \<circ> X) 0 = (t - 0) *\<^sub>R (\<L>\<^bsub>F\<^esub> e on a) (put\<^bsub>a\<^esub> s (X x))"
    using mvt_very_simple[OF a2, of "(\<lambda>x. e (put\<^bsub>a\<^esub> s x)) \<circ> X" "\<lambda>\<tau> t. t *\<^sub>R (\<L>\<^bsub>F\<^esub> e on a) (put\<^bsub>a\<^esub> s (X \<tau>))"]
    using atLeastAtMost_iff by blast
  then obtain \<tau> where final: "0 \<le> \<tau>" "\<tau> \<le> t" 
    "0 \<le> \<partial> (\<lambda>x. e (put\<^bsub>a\<^esub> s x)) (at (X \<tau>)) (get\<^bsub>a\<^esub> (F (put\<^bsub>a\<^esub> s (X \<tau>))))"
    "e (put\<^bsub>a\<^esub> s (X t)) - e (put\<^bsub>a\<^esub> s (X 0)) = t * (\<L>\<^bsub>F\<^esub> e on a) (put\<^bsub>a\<^esub> s (X \<tau>))"
    using lie_deriv_on_def[of F e a] d0 by auto
  thus "0 \<le> e s \<Longrightarrow> 0 \<le> e (put\<^bsub>a\<^esub> s (X t))"
    using assms(1) a5 apply(clarsimp simp: lie_deriv_on_def)
    by (smt split_mult_pos_le)
  show "0 < e s \<Longrightarrow> 0 < e (put\<^bsub>a\<^esub> s (X t))"
    using final assms(1) a5 apply(clarsimp simp: lie_deriv_on_def)
    by (smt split_mult_pos_le)
qed

lemma lie_deriv_eq_rule:
  fixes e :: "'s \<Rightarrow> 'a::real_inner" and a :: "'c::real_normed_vector \<Longrightarrow> 's"
  assumes "vwb_lens a" "differentiable\<^sub>e e on a" "differentiable\<^sub>e f on a"
  shows lie_deriv_eq: "`B \<longrightarrow> \<L>\<^bsub>F\<^esub> e on a = \<L>\<^bsub>F\<^esub> f on a` \<Longrightarrow> diff_inv_on (e = f)\<^sub>e a (\<lambda> _. F) ({t. t \<ge> 0})\<^sub>e UNIV 0 (B)\<^sub>e" (is "_ \<Longrightarrow> ?thesis1")
proof -
  have "`B \<longrightarrow> \<L>\<^bsub>F\<^esub> e on a = \<L>\<^bsub>F\<^esub> f on a` \<Longrightarrow> diff_inv_on (e - f = 0)\<^sub>e a (\<lambda> _. F) ({t. t \<ge> 0})\<^sub>e UNIV 0 (B)\<^sub>e"
    by (rule lie_diff_inv_on_eq, simp_all add: lie_deriv closure assms)
  moreover have "(e - f = 0)\<^sub>e = (e = f)\<^sub>e"
    by (simp add: expr_defs)
  ultimately show "`B \<longrightarrow> \<L>\<^bsub>F\<^esub> e on a = \<L>\<^bsub>F\<^esub> f on a` \<Longrightarrow> ?thesis1"
    by simp
qed

lemma lie_deriv_le_rule:
  fixes e :: "'s \<Rightarrow> real" and a :: "'c::real_normed_vector \<Longrightarrow> 's"
  assumes "vwb_lens a" "differentiable\<^sub>e e on a" "differentiable\<^sub>e f on a"
  shows lie_deriv_le: "`B \<longrightarrow> \<L>\<^bsub>F\<^esub> f on a \<le> \<L>\<^bsub>F\<^esub> e on a` \<Longrightarrow> diff_inv_on (e \<ge> f)\<^sub>e a (\<lambda> _. F) ({t. t \<ge> 0})\<^sub>e UNIV 0 (B)\<^sub>e" (is "_ \<Longrightarrow> ?thesis2")
proof -
  have "`B \<longrightarrow> \<L>\<^bsub>F\<^esub> f on a \<le> \<L>\<^bsub>F\<^esub> e on a` \<Longrightarrow> diff_inv_on (e - f \<ge> 0)\<^sub>e a (\<lambda> _. F) ({t. t \<ge> 0})\<^sub>e UNIV 0 (B)\<^sub>e"
    by (rule lie_diff_inv_on_leq, simp_all add: lie_deriv closure assms)
  moreover have "(e - f \<ge> 0)\<^sub>e = (e \<ge> f)\<^sub>e"
    by (simp add: expr_defs)
  ultimately show "`B \<longrightarrow> \<L>\<^bsub>F\<^esub> f on a \<le> \<L>\<^bsub>F\<^esub> e on a` \<Longrightarrow> ?thesis2"
    by simp
qed

lemma lie_deriv_less_rule:
  fixes e :: "'s \<Rightarrow> real" and a :: "'c::real_normed_vector \<Longrightarrow> 's"
  assumes "vwb_lens a" "differentiable\<^sub>e e on a" "differentiable\<^sub>e f on a"
  shows lie_deriv_less: "`B \<longrightarrow> \<L>\<^bsub>F\<^esub> f on a \<le> \<L>\<^bsub>F\<^esub> e on a` \<Longrightarrow> diff_inv_on (e > f)\<^sub>e a (\<lambda> _. F) ({t. t \<ge> 0})\<^sub>e UNIV 0 (B)\<^sub>e" (is "_ \<Longrightarrow> ?thesis2")
proof -
  have "`B \<longrightarrow> \<L>\<^bsub>F\<^esub> f on a \<le> \<L>\<^bsub>F\<^esub> e on a` \<Longrightarrow> diff_inv_on (e - f > 0)\<^sub>e a (\<lambda> _. F) ({t. t \<ge> 0})\<^sub>e UNIV 0 (B)\<^sub>e"
    by (rule lie_diff_inv_on_less, simp_all add: lie_deriv closure assms)
  moreover have "(e - f \<ge> 0)\<^sub>e = (e \<ge> f)\<^sub>e"
    by (simp add: expr_defs)
  ultimately show "`B \<longrightarrow> \<L>\<^bsub>F\<^esub> f on a \<le> \<L>\<^bsub>F\<^esub> e on a` \<Longrightarrow> ?thesis2"
    by simp
qed

lemmas lie_deriv_rules = lie_deriv_eq_rule lie_deriv_le_rule lie_deriv_less_rule

thm lie_deriv_rules

method dInduct = (subst hoare_diff_inv_on fbox_diff_inv_on2; rule_tac lie_deriv_rules; simp add: lie_deriv closure usubst unrest_ssubst unrest usubst_eval)
method dInduct_auto = (dInduct; expr_simp; auto simp add: field_simps)
method dWeaken = (rule_tac diff_weak_on_rule; expr_simp; auto simp add: field_simps)

text \<open> A first attempt at a high-level automated proof strategy using differential induction.
  A sequence of commands is tried as alternatives, one by one, and the method then iterates. \<close>

method dInduct_mega uses facts = 
  ( fact facts \<comment> \<open> (1) Try any facts we have provided \<close>
  | (dWeaken ; force) \<comment> \<open> (2) Try differential weakening \<close>
  | rule_tac diff_cut_on_split' | rule_tac diff_cut_on_split \<comment> \<open> (4) Try differential cut (two options) \<close>
  | rule_tac hoare_if_then_else_inv
  | (dInduct_auto) \<comment> \<open> (5) Try differential induction \<close>
  )+


method dInduct_mega' uses facts = 
  ( fact facts \<comment> \<open> (1) Try any facts we have provided \<close>
  | (dWeaken ; force) \<comment> \<open> (2) Try differential weakening \<close>
  | rule_tac diff_cut_on_split' | rule_tac diff_cut_on_split \<comment> \<open> (4) Try differential cut (two options) \<close>
  | rule_tac hoare_if_then_else_inv
  | (dDiscr ; force) \<comment> \<open> (3) Try proving as a discrete invariant \<close>
  | (dInduct_auto) \<comment> \<open> (5) Try differential induction \<close>
  )+

text \<open> First attempt at a system level prover \<close>

method dProve = (rule_tac hoare_loop_seqI, hoare_wp_auto, dInduct_mega', (expr_auto)+)

end