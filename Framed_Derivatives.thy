
theory Framed_Derivatives
  imports "Framed_ODEs.Framed_Dyn_Sys"
begin

subsection \<open> framed differentiation \<close>

definition ldifferentiable_expr :: "('c::real_normed_vector \<Longrightarrow> 's) \<Rightarrow> 'c set
  \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 'v::real_normed_vector) \<Rightarrow> bool"
  where [expr_defs]: "ldifferentiable_expr x S G expr 
  \<longleftrightarrow> (\<forall>s. (\<forall> v. (G\<down>\<^sub>F\<^bsub>x\<^esub> s) v) \<longrightarrow> expr\<down>\<^sub>F\<^bsub>x\<^esub> s differentiable (at (get\<^bsub>x\<^esub> s) within S))"

syntax 
  "_differentiable_expr_within_when" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" 
    ("differentiable\<index> _ within _ when _" [0,0,100] 100)
  "_differentiable_expr" :: "logic \<Rightarrow> logic \<Rightarrow> logic" 
    ("differentiable\<index> _ " [100] 100)
  "_expr_differentiable_when_on" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" 
    ("differentiable\<^sub>e _ on _ when _" [0, 0, 100] 100)
  "_expr_differentiable_on" :: "logic \<Rightarrow> logic \<Rightarrow> logic" 
    ("differentiable\<^sub>e _ on _" [0, 100] 100)

translations 
  "differentiable\<^bsub>x\<^esub> expr within S when G" == "CONST ldifferentiable_expr x S G (expr)\<^sub>e"
  "differentiable\<^bsub>x\<^esub> expr" == "CONST ldifferentiable_expr x (CONST UNIV) (CONST True)\<^sub>e (expr)\<^sub>e"
  "differentiable\<^sub>e f on a when d" == "CONST ldifferentiable_expr a (CONST UNIV) (d)\<^sub>e (f)\<^sub>e"
  "differentiable\<^sub>e f on a" == "CONST ldifferentiable_expr a (CONST UNIV) (CONST True)\<^sub>e (f)\<^sub>e"

abbreviation expr_differentiable ("differentiable\<^sub>e") 
  where "expr_differentiable f \<equiv> differentiable\<^sub>e f on id_lens"

named_theorems ldifferentiable

lemma differentiable_number [ldifferentiable]:
  "differentiable\<^bsub>x\<^esub> 0 within S when G" 
  "differentiable\<^bsub>x\<^esub> 1 within S when G" 
  "differentiable\<^bsub>x\<^esub> (numeral \<guillemotleft>n\<guillemotright>) within S when G"
  by (simp_all add: expr_defs)

lemma differentiable_const [ldifferentiable]:
  "differentiable\<^bsub>x\<^esub> \<guillemotleft>k\<guillemotright> within S when G"
  by (simp_all add: expr_defs)

lemma has_derivative_discr_expr: "\<lbrakk>vwb_lens x; $x \<sharp> (expr)\<^sub>e\<rbrakk> 
  \<Longrightarrow> ((\<lambda>c. expr (put\<^bsub>x\<^esub> s c)) has_derivative (\<lambda>c. 0)) (at (get\<^bsub>x\<^esub> s) within S)"
  by expr_auto

lemma differentiable_plus [ldifferentiable]:
  assumes "differentiable\<^bsub>x\<^esub> expr1 within S when G" 
    and "differentiable\<^bsub>x\<^esub> expr2 within S when G"
  shows "differentiable\<^bsub>x\<^esub> (expr1 + expr2) within S when G"
  using assms by (simp add: expr_defs)

lemma differentiable_minus [ldifferentiable]:
  assumes "differentiable\<^bsub>x\<^esub> expr1 within S when G" 
    and "differentiable\<^bsub>x\<^esub> expr2 within S when G"
  shows "differentiable\<^bsub>x\<^esub> (expr1 - expr2) within S when G"
  using assms by (simp add: expr_defs)

lemma differentiable_times [ldifferentiable]:
  fixes expr1 expr2 :: "'s \<Rightarrow> 'v::real_normed_algebra"
  assumes "differentiable\<^bsub>x\<^esub> expr1 within S when G"  
    and "differentiable\<^bsub>x\<^esub> expr2 within S when G"
  shows "differentiable\<^bsub>x\<^esub> (expr1 * expr2) within S when G"
  using assms by (simp add: expr_defs)

lemma differentiable_inverse [ldifferentiable]:
  fixes expr :: "'s \<Rightarrow> 'v::real_normed_field"
  assumes "`expr \<noteq> 0`"  
    and "differentiable\<^bsub>x\<^esub> expr within S when G"
  shows "differentiable\<^bsub>x\<^esub> (inverse expr) within S when G"
  using assms by (auto simp add: expr_defs)

lemma differentiable_divide [ldifferentiable]:
  fixes expr1 expr2 :: "'s \<Rightarrow> 'v::real_normed_field"
  assumes "`expr2 \<noteq> 0`"  
    and "differentiable\<^bsub>x\<^esub> expr1 within S when G"  
    and "differentiable\<^bsub>x\<^esub> expr2 within S when G"
  shows "differentiable\<^bsub>x\<^esub> (expr1 / expr2) within S when G"
  using assms by (auto simp add: expr_defs)

lemma differentiable_inner [ldifferentiable]:
  assumes "differentiable\<^bsub>x\<^esub> expr1 within S when G"  
    and "differentiable\<^bsub>x\<^esub> expr2 within S when G"
  shows "differentiable\<^bsub>x\<^esub> (expr1 \<bullet> expr2) within S when G"
  using assms by (simp add: expr_defs)

lemma differentiable_scaleR [ldifferentiable]:
  assumes "differentiable\<^bsub>x\<^esub> r within S when G"  
    and "differentiable\<^bsub>x\<^esub> expr within S when G"
  shows "differentiable\<^bsub>x\<^esub> (r *\<^sub>R expr) within S when G"
  using assms by (simp add: expr_defs)

lemma differentiable_power [ldifferentiable]:
  fixes expr :: "'s \<Rightarrow> 'v::real_normed_field"
  assumes "differentiable\<^bsub>x\<^esub> expr within S when G"
  shows "differentiable\<^bsub>x\<^esub> (expr^\<guillemotleft>n\<guillemotright>) within S when G"
  using assms by (simp add: expr_defs)

lemma sublens_obs_create: "\<lbrakk> mwb_lens X; Y \<subseteq>\<^sub>L X \<rbrakk> 
  \<Longrightarrow> get\<^bsub>Y\<^esub> (put\<^bsub>X\<^esub> v s) = get\<^bsub>Y\<^esub> (create\<^bsub>X\<^esub> s)"
  by (simp add: lens_create_def sublens_obs_get)

lemma differentiable_cvar [ldifferentiable]:
  assumes "vwb_lens X" "x \<subseteq>\<^sub>L X" "bounded_linear (get\<^bsub>x /\<^sub>L X\<^esub>)"
  shows "differentiable\<^bsub>X\<^esub> $x within S when G"
  using assms apply (clarsimp simp add: expr_defs lens_quotient_def sublens_obs_create)
  using bounded_linear_imp_differentiable by blast

lemma differentiable_dvar [ldifferentiable]:
  assumes "x \<bowtie> y"
  shows "differentiable\<^bsub>y\<^esub> $x within S when G"
  using assms by (auto simp add: expr_defs)

lemma differentiable_discr_expr [ldifferentiable]:
  "\<lbrakk> vwb_lens x; $x \<sharp> (expr)\<^sub>e \<rbrakk> \<Longrightarrow> differentiable\<^bsub>x\<^esub> expr within S when G"
  using differentiable_def has_derivative_discr_expr
  unfolding ldifferentiable_expr_def lframe_fun_def
  by fastforce

declare lens_plus_right_sublens [simp] 

(* should we generalise and make it "at (get\<^bsub>x\<^esub> s) within S"? It does not seem 
  necessary for open sets (c.f. thm at_within_open at_within_open_subset at_within_Icc_at). 
  But what about closed sets (c.f. darboux competition example)? *)
(* What benefits can we get by making the substitution time-dependent? *)
definition lframe_frechetD :: "('c::real_normed_vector \<Longrightarrow> 's)
  \<Rightarrow> ('s \<Rightarrow> 's) \<Rightarrow> ('s \<Rightarrow> 'v::real_normed_vector) \<Rightarrow> 's \<Rightarrow> 'v" 
  where "lframe_frechetD x \<sigma> expr s = \<partial> (expr\<down>\<^sub>F\<^bsub>x\<^esub> s) (at (get\<^bsub>x\<^esub> s)) (get\<^bsub>x\<^esub> (\<sigma> s))"

lemma lframe_frechetD_alt [expr_defs]: "lframe_frechetD x \<sigma> expr 
  = (\<lambda>s. frechet_derivative (\<lambda>c. expr (put\<^bsub>x\<^esub> s c)) (at (get\<^bsub>x\<^esub> s)) (get\<^bsub>x\<^esub> (\<sigma> s)))"
  by (simp add: expr_defs lframe_frechetD_def fun_eq_iff)

expr_constructor lframe_frechetD

syntax
  "_lframeD"  :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"  ("\<D>\<index>\<langle>_\<rangle> _" [0, 100] 100)

translations
  "_lframeD x \<sigma> expr" == "CONST lframe_frechetD x \<sigma> (expr)\<^sub>e"

named_theorems framed_derivs

lemma lframeD_zero [framed_derivs]: "\<D>\<^bsub>x\<^esub>\<langle>\<sigma>\<rangle> 0 = (0)\<^sub>e"
  by (simp add: expr_defs)

lemma lframeD_one [framed_derivs]: "\<D>\<^bsub>x\<^esub>\<langle>\<sigma>\<rangle> 1 = (0)\<^sub>e"
  by (simp add: expr_defs)

lemma lframeD_numeral [framed_derivs]: "\<D>\<^bsub>x\<^esub>\<langle>\<sigma>\<rangle> numeral \<guillemotleft>n\<guillemotright> = (0)\<^sub>e"
  by (simp add: expr_defs)

lemma lframeD_const [framed_derivs]: "\<D>\<^bsub>x\<^esub>\<langle>\<sigma>\<rangle> \<guillemotleft>k\<guillemotright> = (0)\<^sub>e"
  by (simp add: expr_defs)

lemma lframeD_plus [framed_derivs]:
  "\<lbrakk>differentiable\<^bsub>x\<^esub> expr1 ; differentiable\<^bsub>x\<^esub> expr2\<rbrakk> 
  \<Longrightarrow> \<D>\<^bsub>x\<^esub>\<langle>\<sigma>\<rangle> (expr1 + expr2) = (\<D>\<^bsub>x\<^esub>\<langle>\<sigma>\<rangle> expr1 + \<D>\<^bsub>x\<^esub>\<langle>\<sigma>\<rangle> expr2)\<^sub>e"
  by (simp add: expr_defs fun_eq_iff frechet_derivative_plus)

lemma lframeD_minus [framed_derivs]:
  "\<lbrakk>differentiable\<^bsub>x\<^esub> expr1 ; differentiable\<^bsub>x\<^esub> expr2 \<rbrakk> 
  \<Longrightarrow> \<D>\<^bsub>x\<^esub>\<langle>\<sigma>\<rangle> (expr1 - expr2) = (\<D>\<^bsub>x\<^esub>\<langle>\<sigma>\<rangle> expr1 - \<D>\<^bsub>x\<^esub>\<langle>\<sigma>\<rangle> expr2)\<^sub>e"
  by (simp add: expr_defs fun_eq_iff frechet_derivative_minus)

lemma lframeD_times [framed_derivs]:
  fixes expr1 expr2 :: "'s \<Rightarrow> 'v::real_normed_algebra"
  assumes "vwb_lens x" "differentiable\<^bsub>x\<^esub> expr1" "differentiable\<^bsub>x\<^esub> expr2"
  shows "\<D>\<^bsub>x\<^esub>\<langle>\<sigma>\<rangle> (expr1 * expr2) = (expr1 * \<D>\<^bsub>x\<^esub>\<langle>\<sigma>\<rangle> expr2 + \<D>\<^bsub>x\<^esub>\<langle>\<sigma>\<rangle> expr1 * expr2)\<^sub>e"
  using assms by (simp add: expr_defs fun_eq_iff frechet_derivative_mult assms)

lemma lframeD_inner [framed_derivs]:
  fixes x :: "'c::{real_normed_vector, real_inner} \<Longrightarrow> 'v"
  assumes "vwb_lens x" "differentiable\<^bsub>x\<^esub> expr1" "differentiable\<^bsub>x\<^esub> expr2"
  shows "\<D>\<^bsub>x\<^esub>\<langle>\<sigma>\<rangle> (expr1 \<bullet> expr2) = (expr1 \<bullet> \<D>\<^bsub>x\<^esub>\<langle>\<sigma>\<rangle> expr2 + \<D>\<^bsub>x\<^esub>\<langle>\<sigma>\<rangle> expr1 \<bullet> expr2)\<^sub>e"
  using assms by (simp add: expr_defs fun_eq_iff frechet_derivative_inner)

lemma lframeD_scaleR [framed_derivs]:
  fixes a :: "'c::{real_normed_vector} \<Longrightarrow> 'v"
  assumes "vwb_lens x" "differentiable\<^bsub>x\<^esub> expr1" "differentiable\<^bsub>x\<^esub> expr2"
  shows "\<D>\<^bsub>x\<^esub>\<langle>\<sigma>\<rangle> (expr1 *\<^sub>R expr2) = (expr1 *\<^sub>R \<D>\<^bsub>x\<^esub>\<langle>\<sigma>\<rangle> expr2 + \<D>\<^bsub>x\<^esub>\<langle>\<sigma>\<rangle> expr1 *\<^sub>R expr2)\<^sub>e"
  using assms by (simp add: expr_defs fun_eq_iff frechet_derivative_scaleR)

lemma lframeD_inverse [framed_derivs]:
  fixes x :: "'c::real_normed_vector \<Longrightarrow> 's" 
    and expr :: "'s \<Rightarrow> 'v::real_normed_div_algebra"
  assumes  "vwb_lens x" "differentiable\<^bsub>x\<^esub> expr" "`expr \<noteq> 0`"
  shows "\<D>\<^bsub>x\<^esub>\<langle>\<sigma>\<rangle> (inverse expr) = (- (inverse expr * \<D>\<^bsub>x\<^esub>\<langle>\<sigma>\<rangle> expr * inverse expr))\<^sub>e"
  using assms by (simp add: expr_defs fun_eq_iff frechet_derivative_inverse)

lemma lframeD_divide [framed_derivs]:
  fixes x :: "'c::real_normed_vector \<Longrightarrow> 's" 
    and expr1 :: "'s \<Rightarrow> 'v::real_normed_field"
  assumes  "vwb_lens x" "differentiable\<^bsub>x\<^esub> expr1" "differentiable\<^bsub>x\<^esub> expr2" "`expr2 \<noteq> 0`"
  shows "\<D>\<^bsub>x\<^esub>\<langle>\<sigma>\<rangle> (expr1 / expr2) = (\<D>\<^bsub>x\<^esub>\<langle>\<sigma>\<rangle> expr1 / expr2 - expr1 * (\<D>\<^bsub>x\<^esub>\<langle>\<sigma>\<rangle> expr2 / expr2\<^sup>2))\<^sub>e"
  using assms by (simp add: expr_defs fun_eq_iff frechet_derivative_divide)

lemma lframeD_power [framed_derivs]:
  fixes x :: "'c::ordered_euclidean_space \<Longrightarrow> 's"
    and expr :: "'s \<Rightarrow> 'v::{ordered_euclidean_space, real_normed_field}"
  assumes "vwb_lens x" "differentiable\<^bsub>x\<^esub> expr"
  shows "\<D>\<^bsub>x\<^esub>\<langle>\<sigma>\<rangle> (expr ^ \<guillemotleft>n\<guillemotright>) = (of_nat \<guillemotleft>n\<guillemotright> * \<D>\<^bsub>x\<^esub>\<langle>\<sigma>\<rangle> expr * expr ^ (\<guillemotleft>n\<guillemotright> - 1))\<^sub>e"
  using assms by (simp add: expr_defs fun_eq_iff frechet_derivative_power)

lemma lframeD_ln [framed_derivs]:
  fixes x :: "'c::{banach, real_normed_algebra_1} \<Longrightarrow> 's" 
    and expr :: "'s \<Rightarrow> real"
  assumes "vwb_lens x" "differentiable\<^bsub>x\<^esub> expr" "`expr > 0`"
  shows "\<D>\<^bsub>x\<^esub>\<langle>\<sigma>\<rangle> (ln expr) = (\<D>\<^bsub>x\<^esub>\<langle>\<sigma>\<rangle> expr / expr)\<^sub>e"
  using assms by (simp add: expr_defs frechet_derivative_ln divide_inverse)

lemma lframeD_sin [framed_derivs]:
  fixes expr :: "'s \<Rightarrow> real"
  assumes "vwb_lens x" "differentiable\<^bsub>x\<^esub> expr"
  shows "\<D>\<^bsub>x\<^esub>\<langle>\<sigma>\<rangle> (sin expr) = (\<D>\<^bsub>x\<^esub>\<langle>\<sigma>\<rangle> expr * cos expr)\<^sub>e"
  using assms by (simp add: expr_defs fun_eq_iff frechet_derivative_sin)

lemma lframeD_cos [framed_derivs]:
  fixes expr :: "'s \<Rightarrow> real"
  assumes "vwb_lens x" "differentiable\<^bsub>x\<^esub> expr"
  shows "\<D>\<^bsub>x\<^esub>\<langle>\<sigma>\<rangle> (cos expr) = (\<D>\<^bsub>x\<^esub>\<langle>\<sigma>\<rangle> expr * - sin expr)\<^sub>e"
  using assms by (simp add: expr_defs fun_eq_iff frechet_derivative_cos)

lemma lframeD_pair [framed_derivs]:
  fixes x :: "'c::real_normed_vector \<Longrightarrow> 's" 
    and expr1 :: "'s \<Rightarrow> 'v::real_normed_field"
    and expr2 :: "'s \<Rightarrow> 'v::real_normed_field"
  assumes  "vwb_lens x" "differentiable\<^bsub>x\<^esub> expr1" "differentiable\<^bsub>x\<^esub> expr2"
  shows "\<D>\<^bsub>x\<^esub>\<langle>\<sigma>\<rangle> (expr1, expr2) = ((\<D>\<^bsub>x\<^esub>\<langle>\<sigma>\<rangle> expr1 , \<D>\<^bsub>x\<^esub>\<langle>\<sigma>\<rangle> expr2))\<^sub>e"
  using assms by (simp add: expr_defs fun_eq_iff frechet_derivative_Pair)

lemma lframeD_fst [framed_derivs]:
  fixes x :: "'c::real_normed_vector \<Longrightarrow> 's" 
    and expr :: "'s \<Rightarrow> ('v1::real_normed_field) \<times> ('v2::real_normed_field)"
  assumes  "vwb_lens x" "vwb_lens y" "differentiable\<^bsub>x +\<^sub>L y\<^esub> expr"
  shows "\<D>\<^bsub>x\<^esub>\<langle>\<sigma>\<rangle> (fst expr) = (fst (\<D>\<^bsub>x\<^esub>\<langle>\<sigma>\<rangle> expr))\<^sub>e"
  using assms 
  using frechet_derivative_fst
  (* by (simp add: expr_defs fun_eq_iff frechet_derivative_fst) *)
  oops

lemma lframeD_snd [framed_derivs]:
  fixes x :: "'c::real_normed_vector \<Longrightarrow> 's" 
    and expr :: "'s \<Rightarrow> ('v1::real_normed_field) \<times> ('v2::real_normed_field)"
  assumes  "vwb_lens x" "vwb_lens y" "differentiable\<^bsub>x +\<^sub>L y\<^esub> expr"
  shows "\<D>\<^bsub>x\<^esub>\<langle>\<sigma>\<rangle> (snd expr) = (snd (\<D>\<^bsub>x\<^esub>\<langle>\<sigma>\<rangle> expr))\<^sub>e"
  using assms 
  using frechet_derivative_snd
  (* by (simp add: expr_defs fun_eq_iff frechet_derivative_snd) *)
  oops

declare lens_quotient_plus_den1 [simp]
declare lens_quotient_plus_den2 [simp]

lemma lframeD_cont_var [framed_derivs]:
  assumes "vwb_lens X" "x \<subseteq>\<^sub>L X" "bounded_linear (get\<^bsub>x /\<^sub>L X\<^esub>)"
  shows "\<D>\<^bsub>X\<^esub>\<langle>\<sigma>\<rangle> $x = \<langle>\<sigma>\<rangle>\<^sub>s x"
  using assms
  apply (clarsimp simp add: expr_defs lens_quotient_def fun_eq_iff)
  apply (rename_tac s)
  apply (subgoal_tac "(\<lambda>c. get\<^bsub>x\<^esub> (put\<^bsub>X\<^esub> s c)) = (\<lambda>c. get\<^bsub>x\<^esub> (create\<^bsub>X\<^esub> c))", simp)
  apply (metis bounded_linear_imp_has_derivative frechet_derivative_at sublens'_prop2 sublens_implies_sublens' sublens_pres_vwb)
  apply (metis lens_create_def sublens_obs_get vwb_lens_mwb)
  done

(* is this a partial derivative? *)
lemma lframeD_disc_var [framed_derivs]:
  assumes "vwb_lens y" "x \<bowtie> y"
  shows "\<D>\<^bsub>y\<^esub>\<langle>\<sigma>\<rangle> $x = (0)\<^sub>e"
  using assms
  by (auto simp add: expr_defs lens_quotient_def fun_eq_iff)

lemma lframeD_discr_expr [framed_derivs]:
  "\<lbrakk> vwb_lens x; $x \<sharp> (expr)\<^sub>e \<rbrakk> \<Longrightarrow> \<D>\<^bsub>x\<^esub>\<langle>\<sigma>\<rangle> expr = (0)\<^sub>e"
  by expr_simp


subsection \<open> framed differential invariants revisited \<close>

lemma has_vector_derivative_expr_sol:
  fixes x :: "'c::real_normed_vector \<Longrightarrow> 's"
    and expr :: "'s \<Rightarrow> 'v::real_normed_vector"
    and \<sigma> :: "'s \<Rightarrow> 's"
    and \<phi> :: "real \<Rightarrow> 'c"
  assumes "vwb_lens x" "differentiable\<^bsub>x\<^esub> expr" 
    and "(\<phi> has_vector_derivative (\<sigma> \<down>\<^sub>S\<^sub>u\<^sub>b\<^sub>s\<^sub>t\<^bsub>x\<^esub> s) (\<phi> t)) (at t within A)"
  shows "((expr\<down>\<^sub>F\<^bsub>x\<^esub> s) \<circ> \<phi> has_vector_derivative (\<D>\<^bsub>x\<^esub>\<langle>\<sigma>\<rangle> expr) (put\<^bsub>x\<^esub> s (\<phi> t))) (at t within A)"
  using assms
  apply (simp add: lens_defs expr_defs frechet_derivative_works)
  apply (rule vector_derivative_diff_chain_within)
   apply blast
  apply (rule has_derivative_at_withinI)
  apply (drule_tac x="put\<^bsub>x\<^esub> s (\<phi> t)" in spec)
  apply (simp)
  done

(* TODO: generalise to match thm diff_inv_on_eq0I *)
lemma ldiff_inv_on_eq:
  fixes e :: "'s \<Rightarrow> _::real_inner" 
    and x :: "'c::real_normed_vector \<Longrightarrow> 's"
  assumes "vwb_lens x" 
    and "differentiable\<^bsub>x\<^esub> e" 
    and "`G \<longrightarrow> \<D>\<^bsub>x\<^esub>\<langle>F\<rangle> e = 0`"
  shows "diff_inv_on x (\<lambda> _. F) (G)\<^sub>e ({t. t \<ge> 0})\<^sub>e UNIV 0 (e = 0)\<^sub>e"
  using assms apply(simp_all add: diff_inv_on_eq ivp_sols_def tsubst2vecf_eq)
proof(auto simp: lens_defs expr_defs)
  fix t :: real and X :: "real \<Rightarrow> 'c" and s :: "'s"
  assume a1:"\<forall>s. (\<lambda>c. e (put\<^bsub>x\<^esub> s c)) differentiable at (get\<^bsub>x\<^esub> s)" and a2: "0 \<le> t" 
    and a3: "(X has_vderiv_on (\<lambda>t. get\<^bsub>x\<^esub> (F (put\<^bsub>x\<^esub> s (X t))))) (Collect ((\<le>) 0))" 
    "\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> G (put\<^bsub>x\<^esub> s (X \<tau>))" and a5: "X 0 = get\<^bsub>x\<^esub> s" and a6: "e s = 0"
    and a4: "\<forall>s. G s \<longrightarrow> \<partial> (\<lambda>c. e (put\<^bsub>x\<^esub> s c)) (at (get\<^bsub>x\<^esub> s)) (get\<^bsub>x\<^esub> (F s)) = 0"
  show "(\<lambda>c. e (put\<^bsub>x\<^esub> s c)) (X t) = 0"
  proof (cases "t = 0")
    case True
    then show ?thesis
      using a5 a6 assms(1) by auto
  next
    case False
    hence t: "t > 0"
      using a2 by linarith
    have g: "\<forall>t\<in>{0..t}. G (put\<^bsub>x\<^esub> s (X t))"
      by (simp add: a3(2))
    hence d0: "\<forall>t\<in>{0..t}. \<partial> (\<lambda>c. e (put\<^bsub>x\<^esub> s c)) (at (X t)) (get\<^bsub>x\<^esub> (F (put\<^bsub>x\<^esub> s (X t)))) = 0"
      using a4 by (auto simp add: assms(1))
    from a1 have dE: "\<forall>\<tau>\<in>{0..t}. ((\<lambda>c. e (put\<^bsub>x\<^esub> s c)) 
      has_derivative \<partial> (\<lambda>c. e (put\<^bsub>x\<^esub> s c)) (at (X \<tau>))) (at (X \<tau>))"
      by (clarsimp simp add: frechet_derivative_works) 
        (drule_tac x="put\<^bsub>x\<^esub> s (X \<tau>)" in spec, simp add: assms)
    have d1: "\<forall>\<tau>\<in>{0..t}. ((\<lambda>c. e (put\<^bsub>x\<^esub> s c)) \<circ> X 
      has_vector_derivative (\<D>\<^bsub>x\<^esub>\<langle>F\<rangle> e) (put\<^bsub>x\<^esub> s (X \<tau>))) (at \<tau> within {0..t})"
      using a3 apply(clarsimp simp: has_vderiv_on_def)
      apply (rule has_vector_derivative_expr_sol[OF assms(1,2), unfolded lframe_fun_def])
      apply (simp add: has_vector_derivative_def lframe_subst_alt)
      by (rule has_derivative_subset[of _ _ _ "Collect ((\<le>) 0)"], auto)
    hence d2: "\<forall>\<tau>\<in>{0..t}. ((\<lambda>c. e (put\<^bsub>x\<^esub> s c)) \<circ> X 
      has_vector_derivative 0) (at \<tau> within {0..t})"
      using a4 g 
      by (simp add: lframe_fun_alt lframe_frechetD_def)
    have c: "continuous_on {0..t} ((\<lambda>c. e (put\<^bsub>x\<^esub> s c)) \<circ> X)"
      using continuous_on_vector_derivative d2 by fastforce
    have d3: "\<And>\<tau>. 0 < \<tau> \<Longrightarrow> \<tau> < t \<Longrightarrow> (D ((\<lambda>c. e (put\<^bsub>x\<^esub> s c)) \<circ> X) \<mapsto> (\<lambda>x. 0) (at \<tau>))"
      by (metis atLeastAtMost_iff at_within_Icc_at d2 frechet_derivative_at 
          has_derivative_const has_vector_derivative_const 
          has_vector_derivative_def less_eq_real_def)
    have "\<parallel>((\<lambda>c. e (put\<^bsub>x\<^esub> s c)) \<circ> X) t - ((\<lambda>c. e (put\<^bsub>x\<^esub> s c)) \<circ> X) 0\<parallel> \<le> \<parallel>0\<parallel>"
      using mvt_general[OF t c d3] by auto
    hence "((\<lambda>c. e (put\<^bsub>x\<^esub> s c)) \<circ> X) t - ((\<lambda>c. e (put\<^bsub>x\<^esub> s c)) \<circ> X) 0 = 0" by simp
    thus "(\<lambda>c. e (put\<^bsub>x\<^esub> s c)) (X t) = 0"
      by (simp add: a6 a5 assms(1))
  qed
qed

lemma ldiff_inv_simple:
  fixes e :: "'s::real_normed_vector \<Rightarrow> real"
  assumes "differentiable\<^sub>e e" "`G \<longrightarrow> \<D>\<^bsub>\<one>\<^sub>L\<^esub>\<langle>F\<rangle> e = 0`"
  shows "diff_inv ({t. t \<ge> 0})\<^sub>e UNIV (G)\<^sub>e (\<lambda> _. F) 0 (e = 0)\<^sub>e "
  apply (simp add: diff_inv_on_id_lens[THEN sym])
  apply (rule ldiff_inv_on_eq)
  by (simp_all add: assms)

lemma ldiff_inv_on_le_less:
  fixes e :: "'s \<Rightarrow> real" and x :: "'c::real_normed_vector \<Longrightarrow> 's"
  assumes "vwb_lens x" "differentiable\<^sub>e e on x" "`G \<longrightarrow> \<D>\<^bsub>x\<^esub>\<langle>F\<rangle> e \<ge> 0`"
  shows ldiff_inv_on_leq: "diff_inv_on x (\<lambda> _. F) (G)\<^sub>e ({t. t \<ge> 0})\<^sub>e UNIV 0 (e \<ge> 0)\<^sub>e"
    and ldiff_inv_on_less: "diff_inv_on x (\<lambda> _. F) (G)\<^sub>e ({t. t \<ge> 0})\<^sub>e UNIV 0 (e > 0)\<^sub>e"
  using assms apply(simp_all add: diff_inv_on_eq ivp_sols_def tsubst2vecf_eq)
proof(auto simp: lens_defs expr_defs)
  fix t :: real and X :: "real \<Rightarrow> 'c" and s :: "'s"
  assume a1:"\<forall>s. (\<lambda>c. e (put\<^bsub>x\<^esub> s c)) differentiable at (get\<^bsub>x\<^esub> s)" and a2: "0 \<le> t" 
    and a3: "(X has_vderiv_on (\<lambda>t. get\<^bsub>x\<^esub> (F (put\<^bsub>x\<^esub> s (X t))))) (Collect ((\<le>) 0))" 
    "\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> G (put\<^bsub>x\<^esub> s (X \<tau>))" and a5: "X 0 = get\<^bsub>x\<^esub> s"
    and a4: "\<forall>s. G s \<longrightarrow> 0 \<le> \<partial> (\<lambda>c. e (put\<^bsub>x\<^esub> s c)) (at (get\<^bsub>x\<^esub> s)) (get\<^bsub>x\<^esub> (F s))"
  have g: "\<forall>t\<in>{0..t}. G (put\<^bsub>x\<^esub> s (X t))"
    by (simp add: a3(2))
  hence d0: "\<forall>t\<in>{0..t}. 0 \<le> \<partial> (\<lambda>c. e (put\<^bsub>x\<^esub> s c)) (at (X t)) (get\<^bsub>x\<^esub> (F (put\<^bsub>x\<^esub> s (X t))))"
    using a4 by (auto simp: assms(1))
  from a1 have dE: "\<forall>\<tau>\<in>{0..t}. ((\<lambda>c. e (put\<^bsub>x\<^esub> s c)) 
    has_derivative \<partial> (\<lambda>c. e (put\<^bsub>x\<^esub> s c)) (at (X \<tau>))) (at (X \<tau>))"
    by (clarsimp simp add: frechet_derivative_works)
      (drule_tac x="put\<^bsub>x\<^esub> s (X \<tau>)" in spec, simp add: assms)
  have d1: "\<forall>\<tau>\<in>{0..t}. ((\<lambda>c. e (put\<^bsub>x\<^esub> s c)) \<circ> X 
    has_vector_derivative (\<D>\<^bsub>x\<^esub>\<langle>F\<rangle> e) (put\<^bsub>x\<^esub> s (X \<tau>))) (at \<tau> within {0..t})"
    using a3 apply(clarsimp simp: has_vderiv_on_def)
    apply (rule has_vector_derivative_expr_sol[OF assms(1,2), unfolded lframe_fun_def])
    apply (simp add: has_vector_derivative_def lframe_subst_alt)
    by (rule has_derivative_subset[of _ _ _ "Collect ((\<le>) 0)"], auto)
  hence "\<forall>\<tau>\<in>{0..t}. ((\<lambda>c. e (put\<^bsub>x\<^esub> s c)) \<circ> X 
    has_derivative (\<lambda>r. r *\<^sub>R (\<D>\<^bsub>x\<^esub>\<langle>F\<rangle> e) (put\<^bsub>x\<^esub> s (X \<tau>)))) (at \<tau> within {0..t})"
    unfolding has_vector_derivative_def by simp
  hence "\<exists>r\<in>{0..t}. ((\<lambda>c. e (put\<^bsub>x\<^esub> s c)) \<circ> X) t - ((\<lambda>c. e (put\<^bsub>x\<^esub> s c)) \<circ> X) 0 
     = (t - 0) *\<^sub>R (\<D>\<^bsub>x\<^esub>\<langle>F\<rangle> e) (put\<^bsub>x\<^esub> s (X r))"
    using mvt_very_simple[OF a2, 
        of "(\<lambda>c. e (put\<^bsub>x\<^esub> s c)) \<circ> X" "\<lambda>\<tau> t. t *\<^sub>R (\<D>\<^bsub>x\<^esub>\<langle>F\<rangle> e) (put\<^bsub>x\<^esub> s (X \<tau>))"]
    using atLeastAtMost_iff by blast
  then obtain \<tau> where final: "0 \<le> \<tau>" "\<tau> \<le> t" 
    "0 \<le> \<partial> (\<lambda>c. e (put\<^bsub>x\<^esub> s c)) (at (X \<tau>)) (get\<^bsub>x\<^esub> (F (put\<^bsub>x\<^esub> s (X \<tau>))))"
    "e (put\<^bsub>x\<^esub> s (X t)) - e (put\<^bsub>x\<^esub> s (X 0)) = t * (\<D>\<^bsub>x\<^esub>\<langle>F\<rangle> e) (put\<^bsub>x\<^esub> s (X \<tau>))"
    using lframe_frechetD_def d0 by auto
  thus "0 \<le> e s \<Longrightarrow> 0 \<le> e (put\<^bsub>x\<^esub> s (X t))"
    using assms(1) a5 
    by (clarsimp simp: lframe_frechetD_def lframe_fun_alt)
      (smt split_mult_pos_le)
  show "0 < e s \<Longrightarrow> 0 < e (put\<^bsub>x\<^esub> s (X t))"
    using final assms(1) a5 
    by (clarsimp simp: lframe_frechetD_def lframe_fun_alt)
      (smt split_mult_pos_le)
qed

lemma ldiff_inv_on_eq_rule:
  fixes e :: "'s \<Rightarrow> 'a::real_inner" and x :: "'c::real_normed_vector \<Longrightarrow> 's"
  assumes "vwb_lens x" "differentiable\<^sub>e e on x" "differentiable\<^sub>e f on x"
  shows lderiv_eq: "`G \<longrightarrow> \<D>\<^bsub>x\<^esub>\<langle>F\<rangle> e = \<D>\<^bsub>x\<^esub>\<langle>F\<rangle> f` 
  \<Longrightarrow> diff_inv_on x (\<lambda> _. F) (G)\<^sub>e (Collect ((\<le>) 0))\<^sub>e UNIV 0 (e = f)\<^sub>e " (is "_ \<Longrightarrow> ?thesis1")
proof -
  have "`G \<longrightarrow> \<D>\<^bsub>x\<^esub>\<langle>F\<rangle> e = \<D>\<^bsub>x\<^esub>\<langle>F\<rangle> f` \<Longrightarrow> diff_inv_on x (\<lambda> _. F) (G)\<^sub>e ({t. t \<ge> 0})\<^sub>e UNIV 0 (e - f = 0)\<^sub>e"
    by (rule ldiff_inv_on_eq, simp_all add: framed_derivs ldifferentiable assms)
  moreover have "(e - f = 0)\<^sub>e = (e = f)\<^sub>e"
    by (simp add: expr_defs)
  ultimately show "`G \<longrightarrow> \<D>\<^bsub>x\<^esub>\<langle>F\<rangle> e = \<D>\<^bsub>x\<^esub>\<langle>F\<rangle> f` \<Longrightarrow> ?thesis1"
    by simp
qed

lemma ldiff_inv_on_le_rule:
  fixes e :: "'s \<Rightarrow> real" and x :: "'c::real_normed_vector \<Longrightarrow> 's"
  assumes "vwb_lens x" "differentiable\<^sub>e e on x" "differentiable\<^sub>e f on x"
  shows lderiv_le: "`B \<longrightarrow> \<D>\<^bsub>x\<^esub>\<langle>F\<rangle> f \<le> \<D>\<^bsub>x\<^esub>\<langle>F\<rangle> e` 
  \<Longrightarrow> diff_inv_on x (\<lambda> _. F) (B)\<^sub>e (Collect ((\<le>) 0))\<^sub>e UNIV 0 (e \<ge> f)\<^sub>e " (is "_ \<Longrightarrow> ?thesis2")
proof -
  have "`B \<longrightarrow> \<D>\<^bsub>x\<^esub>\<langle>F\<rangle> f \<le> \<D>\<^bsub>x\<^esub>\<langle>F\<rangle> e` \<Longrightarrow> diff_inv_on x (\<lambda> _. F) (B)\<^sub>e  ({t. t \<ge> 0})\<^sub>e UNIV 0 (e - f \<ge> 0)\<^sub>e"
    by (rule ldiff_inv_on_leq, simp_all add: framed_derivs ldifferentiable assms)
  moreover have "(e - f \<ge> 0)\<^sub>e = (e \<ge> f)\<^sub>e"
    by (simp add: expr_defs)
  ultimately show "`B \<longrightarrow> \<D>\<^bsub>x\<^esub>\<langle>F\<rangle> f \<le> \<D>\<^bsub>x\<^esub>\<langle>F\<rangle> e` \<Longrightarrow> ?thesis2"
    by simp
qed

lemma ldiff_inv_on_less_rule:
  fixes e :: "'s \<Rightarrow> real" and x :: "'c::real_normed_vector \<Longrightarrow> 's"
  assumes "vwb_lens x" "differentiable\<^sub>e e on x" "differentiable\<^sub>e f on x"
  shows lderiv_less: "`B \<longrightarrow> \<D>\<^bsub>x\<^esub>\<langle>F\<rangle> f \<le> \<D>\<^bsub>x\<^esub>\<langle>F\<rangle> e` 
  \<Longrightarrow> diff_inv_on x (\<lambda> _. F) (B)\<^sub>e (Collect ((\<le>) 0))\<^sub>e UNIV 0 (e > f)\<^sub>e " (is "_ \<Longrightarrow> ?thesis2")
proof -
  have "`B \<longrightarrow> \<D>\<^bsub>x\<^esub>\<langle>F\<rangle> f \<le> \<D>\<^bsub>x\<^esub>\<langle>F\<rangle> e` \<Longrightarrow> diff_inv_on x (\<lambda> _. F) (B)\<^sub>e ({t. t \<ge> 0})\<^sub>e UNIV 0 (e - f > 0)\<^sub>e "
    by (rule ldiff_inv_on_less, simp_all add: framed_derivs ldifferentiable assms)
  moreover have "(e - f \<ge> 0)\<^sub>e = (e \<ge> f)\<^sub>e"
    by (simp add: expr_defs)
  ultimately show "`B \<longrightarrow> \<D>\<^bsub>x\<^esub>\<langle>F\<rangle> f \<le> \<D>\<^bsub>x\<^esub>\<langle>F\<rangle> e` \<Longrightarrow> ?thesis2"
    by simp
qed

lemmas lderiv_rules = ldiff_inv_on_eq_rule ldiff_inv_on_le_rule ldiff_inv_on_less_rule


subsection \<open> Differentiating substitutions \<close>

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
  "vwb_lens x \<Longrightarrow> \<partial>\<^sub>s x [x \<leadsto> e] = [x \<leadsto>\<D>\<^bsub>x\<^esub>\<langle>[\<leadsto>]\<rangle> e]"
  by (simp add: frechet_derivative_subst_def expr_defs fun_eq_iff)

text \<open> A postcondition of a localised ODE is a postcondition of its unique localised solution. \<close>

definition local_lipschitz_on :: "('c::metric_space \<Longrightarrow> 's) \<Rightarrow> 'a::metric_space set 
  \<Rightarrow> 'c set \<Rightarrow> ('s \<Rightarrow> 's) \<Rightarrow> bool" 
  where "local_lipschitz_on A T S f = (\<forall> s. local_lipschitz T S (\<lambda>t c. get\<^bsub>A\<^esub> (f (put\<^bsub>A\<^esub> s c))))"

lemma c1_local_lipschitz_on:
  fixes a :: "('a::{heine_borel,banach,euclidean_space, times}) \<Longrightarrow> 's"
  assumes "vwb_lens a" "differentiable_subst a \<sigma> UNIV" 
    "\<forall>z s. continuous_on UNIV (\<lambda>(t::real,p:: 'a). \<partial> (\<lambda>c. get\<^bsub>a\<^esub> (\<sigma> (put\<^bsub>a\<^esub> s c))) (at p) z)"
  shows "local_lipschitz_on a (UNIV :: real set) UNIV \<sigma>"
proof (unfold local_lipschitz_on_def, clarify)
  fix s
  from assms(1,2)
  have 1:"\<forall>c'. D (\<lambda>c. get\<^bsub>a\<^esub> (\<sigma> (put\<^bsub>a\<^esub> s c))) \<mapsto> (\<partial> (\<lambda>c. get\<^bsub>a\<^esub> (\<sigma> (put\<^bsub>a\<^esub> s c))) (at c')) (at c')"
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

lemma c1_local_lipschitz_on':
  fixes a :: "('a::{heine_borel,banach,euclidean_space, times}) \<Longrightarrow> _"
  assumes "vwb_lens a" "differentiable_subst a \<sigma> UNIV" "continuous_subst_on a (\<partial>\<^sub>s a \<sigma>) UNIV UNIV"
    "\<exists> f. \<forall> x s. \<partial> (\<lambda>c. get\<^bsub>a\<^esub> (\<sigma> (put\<^bsub>a\<^esub> s c))) (at x) = f" 
  shows "local_lipschitz_on a (UNIV :: real set) UNIV \<sigma>"
proof (unfold local_lipschitz_on_def, clarify)
  fix s
  from assms 
  have 1:"\<forall>c'. D (\<lambda>c. get\<^bsub>a\<^esub> (\<sigma> (put\<^bsub>a\<^esub> s c))) \<mapsto> (\<partial> (\<lambda>c. get\<^bsub>a\<^esub> (\<sigma> (put\<^bsub>a\<^esub> s c))) (at c')) (at c')"
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

end