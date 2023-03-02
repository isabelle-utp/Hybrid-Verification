(*  Title: ODEs with lenses *)

section \<open> ODEs with lenses \<close>

text \<open> We use shallow expressions to rephrase the properties for hybrid systems in a 
cleaner presentation. \<close>

theory HS_Lens_ODEs
  imports 
    "HS_ODEs" 
    "Hybrid-Library.Cont_Lens"
    "Shallow-Expressions.Shallow_Expressions"
begin

text \<open> In this section we use type @{typ 's} for the state space, 
type @{typ 'c} for a sub-region of @{typ 's}, and types @{typ 't} and 
@{typ 'v} for generic representations of time and a value domain. With 
lenses @{term "x :: 'c \<Longrightarrow> 's"}, we lift entities from @{typ 'c} to 
@{typ 's} and frame others from @{typ 's} to @{typ 'c}. \<close>

no_notation id_lens ("1\<^sub>L")
notation id_lens ("\<one>\<^sub>L")

subsection \<open> Framing and lifting \<close>

definition lframe_fun :: "('c \<Longrightarrow> 's) \<Rightarrow> ('s \<Rightarrow> 'v) \<Rightarrow> 's \<Rightarrow> ('c \<Rightarrow> 'v)" (infixr "\<down>\<^sub>F\<index>" 100)
  where "(F\<down>\<^sub>F\<^bsub>x\<^esub> s) c = F (put\<^bsub>x\<^esub> s c)"

lemma lframe_fun_alt [expr_defs]: "(F\<down>\<^sub>F\<^bsub>x\<^esub> s) = (\<lambda>c. F (put\<^bsub>x\<^esub> s c))"
  by (auto simp: lframe_fun_def)

definition llift_fun :: "('c \<Longrightarrow> 's) \<Rightarrow> ('c \<Rightarrow> 'v) \<Rightarrow> ('s \<Rightarrow> 'v)" (infixr "\<up>\<^sub>F\<index>" 100)
  where [expr_defs]: "F\<up>\<^sub>F\<^bsub>x\<^esub> s \<equiv>  F (get\<^bsub>x\<^esub> s)"

definition lframe_set :: "('c \<Longrightarrow> 's) \<Rightarrow> 's set \<Rightarrow> 'c set" ("_\<down>\<^sub>S\<^sub>e\<^sub>t\<index>" [100] 100)
  where [expr_defs]: "X\<down>\<^sub>S\<^sub>e\<^sub>t\<^bsub>x\<^esub> = \<P> get\<^bsub>x\<^esub> X"

definition llift_set :: "('c \<Longrightarrow> 's) \<Rightarrow> 'c set \<Rightarrow> 's \<Rightarrow> 's set" (infixr "\<up>\<^sub>S\<^sub>e\<^sub>t\<index>" 100)
  where [expr_defs]: "X\<up>\<^sub>S\<^sub>e\<^sub>t\<^bsub>x\<^esub> s \<equiv> \<P> (\<lambda>c. put\<^bsub>x\<^esub> s c) X"

definition lframe_pred :: "('c \<Longrightarrow> 's) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> bool)" ("_\<down>\<^sub>P\<index>" [100] 1000)
  where [expr_defs]: "P\<down>\<^sub>P\<^bsub>x\<^esub> c \<longleftrightarrow> c \<in> {s. P s}\<down>\<^sub>S\<^sub>e\<^sub>t\<^bsub>x\<^esub>"

lemma lframe_pred_iff_pred_as_fun: 
  "vwb_lens x \<Longrightarrow> P\<down>\<^sub>P\<^bsub>x\<^esub> c \<longleftrightarrow> (\<exists>s. (P\<down>\<^sub>F\<^bsub>x\<^esub> s) c)"
  by (expr_auto add: image_iff)
    (metis vwb_lens_def wb_lens.get_put)

lemma lframe_set_Collect_llift_fun: 
  "vwb_lens x \<Longrightarrow> \<P> get\<^bsub>x\<^esub> UNIV = UNIV \<Longrightarrow> {s. P\<up>\<^sub>F\<^bsub>x\<^esub> s}\<down>\<^sub>S\<^sub>e\<^sub>t\<^bsub>x\<^esub> = {c. P c}"
  by expr_auto

lemma llift_set_Collect_lframe_pred: 
  "vwb_lens x \<Longrightarrow> {c. P\<down>\<^sub>P\<^bsub>x\<^esub> c}\<up>\<^sub>S\<^sub>e\<^sub>t\<^bsub>x\<^esub> s = {put\<^bsub>x\<^esub> s (get\<^bsub>x\<^esub> s') |s'. P s'}"
  by expr_auto

lemma Un_llift_set_lframe_pred_supset: 
  "vwb_lens x \<Longrightarrow> {s. P s} \<subseteq> (\<Union>s. {c. P\<down>\<^sub>P\<^bsub>x\<^esub> c}\<up>\<^sub>S\<^sub>e\<^sub>t\<^bsub>x\<^esub> s)"
  by (auto simp: lframe_pred_def llift_set_def image_iff lframe_set_def)
    (metis vwb_lens.put_eq)

text \<open> Localise a substitution using a lens. Useful for localising both ODEs and flows. \<close>

definition lframe_subst :: "('c \<Longrightarrow> 's) \<Rightarrow> ('s \<Rightarrow> 's) \<Rightarrow> 's \<Rightarrow> ('c \<Rightarrow> 'c)" (infixr "\<down>\<^sub>S\<^sub>u\<^sub>b\<^sub>s\<^sub>t\<index>" 100)
  where "(\<sigma>\<down>\<^sub>S\<^sub>u\<^sub>b\<^sub>s\<^sub>t\<^bsub>x\<^esub> s) c \<equiv> get\<^bsub>x\<^esub> ((\<sigma> \<down>\<^sub>F\<^bsub>x\<^esub> s) c)"

lemma lframe_subst_alt [expr_defs]: 
  "(\<down>\<^sub>S\<^sub>u\<^sub>b\<^sub>s\<^sub>t\<^bsub>x\<^esub>) \<sigma> \<equiv> (\<lambda>s c. get\<^bsub>x\<^esub> (\<sigma> (put\<^bsub>x\<^esub> s c)))"
  unfolding lframe_subst_def
  by expr_simp

abbreviation tsubst2vecf :: "('c::real_normed_vector \<Longrightarrow> 's) 
  \<Rightarrow> (real \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> 's \<Rightarrow> real \<Rightarrow> 'c \<Rightarrow> 'c" (infixr "\<down>\<^sub>V\<^sub>e\<^sub>c\<index>" 100)
  where "(F\<down>\<^sub>V\<^sub>e\<^sub>c\<^bsub>x\<^esub> s) t c \<equiv> (F t \<down>\<^sub>S\<^sub>u\<^sub>b\<^sub>s\<^sub>t\<^bsub>x\<^esub> s) c"

lemma tsubst2vecf_eq: "F\<down>\<^sub>V\<^sub>e\<^sub>c\<^bsub>x\<^esub> s = (\<lambda> t c. get\<^bsub>x\<^esub> (F t (put\<^bsub>x\<^esub> s c)))"
  by (auto simp: lframe_subst_def fun_eq_iff lframe_fun_def)


subsection \<open> Framed orbitals  \<close>

text \<open> A version of orbital localised by a lens \<close>

definition g_orbital_on :: "('c::real_normed_vector \<Longrightarrow> 's) 
  \<Rightarrow> (real \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> real set) \<Rightarrow> 'c set \<Rightarrow> real \<Rightarrow> 's \<Rightarrow> 's set"
  where "g_orbital_on x F G U S t\<^sub>0 s 
    = (g_orbital (F\<down>\<^sub>V\<^sub>e\<^sub>c\<^bsub>x\<^esub> s) (G\<down>\<^sub>F\<^bsub>x\<^esub> s) U S t\<^sub>0 (get\<^bsub>x\<^esub> s))\<up>\<^sub>S\<^sub>e\<^sub>t\<^bsub>x\<^esub> s"

lemma g_orbital_on_eq: "g_orbital_on x f G U S t\<^sub>0 s 
  = {put\<^bsub>x\<^esub> s (X t) |t X. t \<in> U (get\<^bsub>x\<^esub> s) 
    \<and> \<P> (\<lambda>t. put\<^bsub>x\<^esub> s (X t)) (down (U (get\<^bsub>x\<^esub> s)) t) \<subseteq> {s. G s} 
    \<and> X \<in> Sols U S (f\<down>\<^sub>V\<^sub>e\<^sub>c\<^bsub>x\<^esub> s) t\<^sub>0 (get\<^bsub>x\<^esub> s)}"
  unfolding g_orbital_on_def g_orbital_eq image_le_pred 
  by (auto simp: image_def tsubst2vecf_eq llift_set_def lframe_fun_def)

lemma g_orbital_on_id_lens: "g_orbital_on \<one>\<^sub>L = g_orbital"
  by (simp add: g_orbital_on_eq tsubst2vecf_eq g_orbital_eq fun_eq_iff lens_defs)

lemma g_orbital_onI:
  assumes "X \<in> Sols U S (\<lambda>t c. get\<^bsub>x\<^esub> (f t (put\<^bsub>x\<^esub> s c))) t\<^sub>0 (get\<^bsub>x\<^esub> s)"
    and "t \<in> U (get\<^bsub>x\<^esub> s)" and "(\<P> (\<lambda>\<tau>. put\<^bsub>x\<^esub> s (X \<tau>)) (down (U (get\<^bsub>x\<^esub> s)) t) \<subseteq> Collect G)"
  shows "put\<^bsub>x\<^esub> s (X t) \<in> g_orbital_on x f G U S t\<^sub>0 s"
  using assms unfolding g_orbital_on_eq tsubst2vecf_eq by auto


subsection \<open> Framed differential invariants \<close>

definition diff_inv_on :: "('c:: real_normed_vector \<Longrightarrow> 'a) \<Rightarrow> (real \<Rightarrow> 'a \<Rightarrow> 'a) 
  \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> real set) \<Rightarrow> 'c set \<Rightarrow> real \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" 
  where "diff_inv_on x f G U S t\<^sub>0 I \<equiv> (\<Union> \<circ> (\<P> (g_orbital_on x f G U S t\<^sub>0))) {s. I s} \<subseteq> {s. I s}"

lemma diff_inv_on_eq: "diff_inv_on x f G U S t\<^sub>0 I = 
  (\<forall>s. I s \<longrightarrow> (\<forall>X\<in>Sols U S (f\<down>\<^sub>V\<^sub>e\<^sub>c\<^bsub>x\<^esub> s) t\<^sub>0 (get\<^bsub>x\<^esub> s). 
    (\<forall>t\<in>U (get\<^bsub>x\<^esub> s).(\<forall>\<tau>\<in>(down (U (get\<^bsub>x\<^esub> s)) t). G (put\<^bsub>x\<^esub> s (X \<tau>))) \<longrightarrow> I (put\<^bsub>x\<^esub> s (X t)))))"
  unfolding diff_inv_on_def g_orbital_on_eq image_le_pred 
  by (auto simp: image_def tsubst2vecf_eq)

lemma diff_inv_on_id_lens: "diff_inv_on \<one>\<^sub>L f G U S t\<^sub>0 I = diff_inv U S G f t\<^sub>0 I"
  by (simp add: diff_inv_on_def diff_inv_def g_orbital_on_id_lens)

lemma diff_inv_on_iff:
  assumes"vwb_lens x"
  shows "diff_inv_on x f G U S t\<^sub>0 I \<longleftrightarrow> 
  (\<forall>s. diff_inv U S (\<lambda>c. G (put\<^bsub>x\<^esub> s c)) (f\<down>\<^sub>V\<^sub>e\<^sub>c\<^bsub>x\<^esub> s) t\<^sub>0 (\<lambda>c. I (put\<^bsub>x\<^esub> s c)))"
proof(intro iffI, goal_cases "(\<Rightarrow>)" "(\<Leftarrow>)")
  case ("(\<Rightarrow>)")
  then show ?case 
    using assms
    by (auto simp: diff_inv_on_eq diff_inv_eq tsubst2vecf_eq)
next
  case "(\<Leftarrow>)"
  thus ?case
    apply(clarsimp simp: diff_inv_on_eq diff_inv_eq)
    apply (erule_tac x=s in allE, erule_tac x="get\<^bsub>x\<^esub> s" in allE)
    using assms by auto
qed


subsection \<open> framed differentiation \<close>

lemma has_derivative_discr_expr:
  "\<lbrakk>vwb_lens x; $x \<sharp> (expr)\<^sub>e\<rbrakk> \<Longrightarrow> ((\<lambda>c. expr (put\<^bsub>x\<^esub> s c)) has_derivative (\<lambda>c. 0)) (at (get\<^bsub>x\<^esub> s) within S)"
  by expr_auto

definition ldifferentiable_expr :: "('c::real_normed_vector \<Longrightarrow> 's) \<Rightarrow> 'c set
  \<Rightarrow> ('s \<Rightarrow> 'v::real_normed_vector) \<Rightarrow> bool"
  where [expr_defs]: "ldifferentiable_expr x S expr 
  \<longleftrightarrow> (\<forall>s. (\<lambda>c. expr (put\<^bsub>x\<^esub> s c)) differentiable (at (get\<^bsub>x\<^esub> s) within S))"

syntax 
  "_differentiable_expr_on" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("differentiable\<index> _ on _" [0,100] 100)
  "_differentiable_expr" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("differentiable\<index> _ " [100] 100)

translations 
  "differentiable\<^bsub>x\<^esub> expr on S" == "CONST ldifferentiable_expr x S (expr)\<^sub>e"
  "differentiable\<^bsub>x\<^esub> expr" == "CONST ldifferentiable_expr x (CONST UNIV) (expr)\<^sub>e"

named_theorems ldifferentiable

lemma differentiable_number [ldifferentiable]:
  "differentiable\<^bsub>x\<^esub> 0 on S" 
  "differentiable\<^bsub>x\<^esub> 1 on S" 
  "differentiable\<^bsub>x\<^esub> (numeral \<guillemotleft>n\<guillemotright>) on S"
  by (simp_all add: expr_defs)

lemma differentiable_const [ldifferentiable]:
  "differentiable\<^bsub>x\<^esub> \<guillemotleft>k\<guillemotright> on S"
  by (simp_all add: expr_defs)

lemma differentiable_discr_expr [ldifferentiable]:
  "\<lbrakk> vwb_lens x; $x \<sharp> (expr)\<^sub>e \<rbrakk> \<Longrightarrow> differentiable\<^bsub>x\<^esub> expr on S"
  using differentiable_def has_derivative_discr_expr
  by (fastforce simp add: ldifferentiable_expr_def)

lemma differentiable_plus [ldifferentiable]:
  assumes "differentiable\<^bsub>x\<^esub> expr1 on S" "differentiable\<^bsub>x\<^esub> expr2 on S"
  shows "differentiable\<^bsub>x\<^esub> (expr1 + expr2) on S"
  using assms by (simp add: expr_defs)

lemma differentiable_minus [ldifferentiable]:
  assumes "differentiable\<^bsub>x\<^esub> expr1 on S" "differentiable\<^bsub>x\<^esub> expr2 on S"
  shows "differentiable\<^bsub>x\<^esub> (expr1 - expr2) on S"
  using assms by (simp add: expr_defs)

lemma differentiable_times [ldifferentiable]:
  fixes expr1 expr2 :: "'s \<Rightarrow> 'v::real_normed_field"
  assumes "differentiable\<^bsub>x\<^esub> expr1 on S" "differentiable\<^bsub>x\<^esub> expr2 on S"
  shows "differentiable\<^bsub>x\<^esub> (expr1 * expr2) on S"
  using assms by (simp add: expr_defs)

lemma differentiable_inverse [ldifferentiable]:
  fixes expr :: "'s \<Rightarrow> 'v::real_normed_field"
  assumes "`expr \<noteq> 0`" "differentiable\<^bsub>x\<^esub> expr on S"
  shows "differentiable\<^bsub>x\<^esub> (inverse expr) on S"
  using assms by (auto simp add: expr_defs)

lemma differentiable_divide [ldifferentiable]:
  fixes expr1 expr2 :: "'s \<Rightarrow> 'v::real_normed_field"
  assumes "`expr2 \<noteq> 0`" "differentiable\<^bsub>x\<^esub> expr1 on S" "differentiable\<^bsub>x\<^esub> expr2 on S"
  shows "differentiable\<^bsub>x\<^esub> (expr1 / expr2) on S"
  using assms by (auto simp add: expr_defs)

lemma differentiable_inner [ldifferentiable]:
  assumes "differentiable\<^bsub>x\<^esub> expr1 on S" "differentiable\<^bsub>x\<^esub> expr2 on S"
  shows "differentiable\<^bsub>x\<^esub> (expr1 \<bullet> expr2) on S"
  using assms by (simp add: expr_defs)

lemma differentiable_scaleR [ldifferentiable]:
  assumes "differentiable\<^bsub>x\<^esub> r on S" "differentiable\<^bsub>x\<^esub> expr on S"
  shows "differentiable\<^bsub>x\<^esub> (r *\<^sub>R expr) on S"
  using assms by (simp add: expr_defs)

lemma differentiable_power [ldifferentiable]:
  fixes expr :: "'s \<Rightarrow> 'v::real_normed_field"
  assumes "differentiable\<^bsub>x\<^esub> expr on S"
  shows "differentiable\<^bsub>x\<^esub> (expr^\<guillemotleft>n\<guillemotright>) on S"
  using assms by (simp add: expr_defs)

lemma sublens_obs_create: "\<lbrakk> mwb_lens X; Y \<subseteq>\<^sub>L X \<rbrakk> \<Longrightarrow> get\<^bsub>Y\<^esub> (put\<^bsub>X\<^esub> v s) = get\<^bsub>Y\<^esub> (create\<^bsub>X\<^esub> s)"
  by (simp add: lens_create_def sublens_obs_get)

lemma differentiable_cvar [ldifferentiable]:
  assumes "vwb_lens X" "x \<subseteq>\<^sub>L X" "bounded_linear (get\<^bsub>x /\<^sub>L X\<^esub>)"
  shows "differentiable\<^bsub>X\<^esub> $x on S"
  using assms apply (clarsimp simp add: expr_defs lens_quotient_def sublens_obs_create)
  using bounded_linear_imp_differentiable by blast

lemma differentiable_dvar [ldifferentiable]:
  assumes "x \<bowtie> y"
  shows "differentiable\<^bsub>y\<^esub> $x on S"
  using assms by (auto simp add: expr_defs)

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

expr_ctr lframe_frechetD

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

lemma lframeD_discr_expr [framed_derivs]:
  "\<lbrakk> vwb_lens x; $x \<sharp> (expr)\<^sub>e \<rbrakk> \<Longrightarrow> \<D>\<^bsub>x\<^esub>\<langle>\<sigma>\<rangle> expr = (0)\<^sub>e"
  by expr_simp

lemma lframeD_plus [framed_derivs]:
  "\<lbrakk>differentiable\<^bsub>x\<^esub> expr1 ; differentiable\<^bsub>x\<^esub> expr2\<rbrakk> 
  \<Longrightarrow> \<D>\<^bsub>x\<^esub>\<langle>\<sigma>\<rangle> (expr1 + expr2) = (\<D>\<^bsub>x\<^esub>\<langle>\<sigma>\<rangle> expr1 + \<D>\<^bsub>x\<^esub>\<langle>\<sigma>\<rangle> expr2)\<^sub>e"
  by (simp add: expr_defs fun_eq_iff frechet_derivative_plus)

lemma lframeD_minus [framed_derivs]:
  "\<lbrakk>differentiable\<^bsub>x\<^esub> expr1 ; differentiable\<^bsub>x\<^esub> expr2 \<rbrakk> 
  \<Longrightarrow> \<D>\<^bsub>x\<^esub>\<langle>\<sigma>\<rangle> (expr1 - expr2) = (\<D>\<^bsub>x\<^esub>\<langle>\<sigma>\<rangle> expr1 - \<D>\<^bsub>x\<^esub>\<langle>\<sigma>\<rangle> expr2)\<^sub>e"
  by (simp add: expr_defs fun_eq_iff frechet_derivative_minus)

lemma lframeD_times [framed_derivs]:
  fixes expr1 expr2 :: "'s \<Rightarrow> 'v::real_normed_field"
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


subsection \<open> framed differential invariants \<close>

thm lframe_subst_def[unfolded lframe_fun_alt] tsubst2vecf_eq lframe_fun_alt

lemma has_vector_derivative_expr:
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

lemma lie_diff_inv_on_eq:
  fixes e :: "'s \<Rightarrow> _::real_inner" and a :: "'c::real_normed_vector \<Longrightarrow> 's"
  assumes "vwb_lens a" "differentiable\<^sub>e e on a" "`B \<longrightarrow> \<L>\<^bsub>F\<^esub> e on a = 0`"
  shows "diff_inv_on a (\<lambda> _. F) (B)\<^sub>e ({t. t \<ge> 0})\<^sub>e UNIV 0 (e = 0)\<^sub>e"
  using assms apply(simp_all add: diff_inv_on_eq ivp_sols_def tsubst2vecf_eq)
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
  shows lie_diff_inv_on_leq: "diff_inv_on a (\<lambda> _. F) (B)\<^sub>e ({t. t \<ge> 0})\<^sub>e UNIV 0 (e \<ge> 0)\<^sub>e"
    and lie_diff_inv_on_less: "diff_inv_on a (\<lambda> _. F) (B)\<^sub>e ({t. t \<ge> 0})\<^sub>e UNIV 0 (e > 0)\<^sub>e"
  using assms apply(simp_all add: diff_inv_on_eq ivp_sols_def tsubst2vecf_eq)
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
  shows lie_deriv_eq: "`B \<longrightarrow> \<L>\<^bsub>F\<^esub> e on a = \<L>\<^bsub>F\<^esub> f on a` 
  \<Longrightarrow> diff_inv_on a (\<lambda> _. F) (B)\<^sub>e ({t. t \<ge> 0})\<^sub>e UNIV 0 (e = f)\<^sub>e " (is "_ \<Longrightarrow> ?thesis1")
proof -
  have "`B \<longrightarrow> \<L>\<^bsub>F\<^esub> e on a = \<L>\<^bsub>F\<^esub> f on a` \<Longrightarrow> diff_inv_on a (\<lambda> _. F) (B)\<^sub>e ({t. t \<ge> 0})\<^sub>e UNIV 0 (e - f = 0)\<^sub>e"
    by (rule lie_diff_inv_on_eq, simp_all add: lie_deriv closure assms)
  moreover have "(e - f = 0)\<^sub>e = (e = f)\<^sub>e"
    by (simp add: expr_defs)
  ultimately show "`B \<longrightarrow> \<L>\<^bsub>F\<^esub> e on a = \<L>\<^bsub>F\<^esub> f on a` \<Longrightarrow> ?thesis1"
    by simp
qed

lemma lie_deriv_le_rule:
  fixes e :: "'s \<Rightarrow> real" and a :: "'c::real_normed_vector \<Longrightarrow> 's"
  assumes "vwb_lens a" "differentiable\<^sub>e e on a" "differentiable\<^sub>e f on a"
  shows lie_deriv_le: "`B \<longrightarrow> \<L>\<^bsub>F\<^esub> f on a \<le> \<L>\<^bsub>F\<^esub> e on a` 
  \<Longrightarrow> diff_inv_on a (\<lambda> _. F) (B)\<^sub>e ({t. t \<ge> 0})\<^sub>e UNIV 0 (e \<ge> f)\<^sub>e " (is "_ \<Longrightarrow> ?thesis2")
proof -
  have "`B \<longrightarrow> \<L>\<^bsub>F\<^esub> f on a \<le> \<L>\<^bsub>F\<^esub> e on a` \<Longrightarrow> diff_inv_on a (\<lambda> _. F) (B)\<^sub>e  ({t. t \<ge> 0})\<^sub>e UNIV 0 (e - f \<ge> 0)\<^sub>e"
    by (rule lie_diff_inv_on_leq, simp_all add: lie_deriv closure assms)
  moreover have "(e - f \<ge> 0)\<^sub>e = (e \<ge> f)\<^sub>e"
    by (simp add: expr_defs)
  ultimately show "`B \<longrightarrow> \<L>\<^bsub>F\<^esub> f on a \<le> \<L>\<^bsub>F\<^esub> e on a` \<Longrightarrow> ?thesis2"
    by simp
qed

lemma lie_deriv_less_rule:
  fixes e :: "'s \<Rightarrow> real" and a :: "'c::real_normed_vector \<Longrightarrow> 's"
  assumes "vwb_lens a" "differentiable\<^sub>e e on a" "differentiable\<^sub>e f on a"
  shows lie_deriv_less: "`B \<longrightarrow> \<L>\<^bsub>F\<^esub> f on a \<le> \<L>\<^bsub>F\<^esub> e on a` \<Longrightarrow> diff_inv_on a (\<lambda> _. F) (B)\<^sub>e ({t. t \<ge> 0})\<^sub>e UNIV 0 (e > f)\<^sub>e " (is "_ \<Longrightarrow> ?thesis2")
proof -
  have "`B \<longrightarrow> \<L>\<^bsub>F\<^esub> f on a \<le> \<L>\<^bsub>F\<^esub> e on a` \<Longrightarrow> diff_inv_on a (\<lambda> _. F) (B)\<^sub>e ({t. t \<ge> 0})\<^sub>e UNIV 0 (e - f > 0)\<^sub>e "
    by (rule lie_diff_inv_on_less, simp_all add: lie_deriv closure assms)
  moreover have "(e - f \<ge> 0)\<^sub>e = (e \<ge> f)\<^sub>e"
    by (simp add: expr_defs)
  ultimately show "`B \<longrightarrow> \<L>\<^bsub>F\<^esub> f on a \<le> \<L>\<^bsub>F\<^esub> e on a` \<Longrightarrow> ?thesis2"
    by simp
qed

named_theorems diff_inv_on_intros "intro rules for certifying (localised) differential invariants"

lemma diff_inv_on_eq0I:
  fixes \<mu> :: "_ \<Rightarrow> 'c::real_inner"
  assumes "vwb_lens a"
    and Uhyp: "\<And>s. s \<in> S \<Longrightarrow> is_interval (U s)"
    and dX: "\<And>X t s. (D X = (\<lambda>\<tau>. (f\<down>\<^sub>V\<^sub>e\<^sub>c\<^bsub>a\<^esub> s) \<tau> (X \<tau>)) on U (X t\<^sub>0)) \<Longrightarrow>
  \<forall>\<tau>\<in>(down (U (X t\<^sub>0)) t). G (put\<^bsub>a\<^esub> s (X \<tau>)) \<Longrightarrow> (D (\<lambda>\<tau>. \<mu> (put\<^bsub>a\<^esub> s (X \<tau>))) = (\<lambda>t. 0) on U (X t\<^sub>0))"
  shows "diff_inv_on a f G U S t\<^sub>0  (\<mu> = 0)\<^sub>e"
  unfolding diff_inv_on_iff[OF assms(1)]
  apply (clarsimp, subst diff_inv_eq0I[OF Uhyp]; simp?)
  using dX by force

lemma diff_inv_on_eqI [diff_inv_on_intros]:
  fixes \<mu> \<nu> :: "_ \<Rightarrow> 'c::real_inner"
  assumes "vwb_lens a" (* do we need derivative rules for loc_subst then? *)
    and Uhyp: "\<And>s. s \<in> S \<Longrightarrow> is_interval (U s)"
    and dX: "\<And>X t s. (D X = (\<lambda>\<tau>. (f\<down>\<^sub>V\<^sub>e\<^sub>c\<^bsub>a\<^esub> s) \<tau> (X \<tau>)) on U (X t\<^sub>0)) \<Longrightarrow>
  \<forall>\<tau>\<in>(down (U (X t\<^sub>0)) t). G (put\<^bsub>a\<^esub> s (X \<tau>)) \<Longrightarrow> (D (\<lambda>\<tau>. \<mu> (put\<^bsub>a\<^esub> s (X \<tau>))-\<nu>(put\<^bsub>a\<^esub> s (X \<tau>))) = (\<lambda>t. 0) on U (X t\<^sub>0))"
  shows "diff_inv_on a f G U S t\<^sub>0 (\<mu> = \<nu>)\<^sub>e"
  using assms diff_inv_on_eq0I[OF assms(1,2), where \<mu>="\<lambda>s. \<mu> s - \<nu> s"]
  by auto

lemma diff_inv_on_leqI [diff_inv_on_intros]:
  fixes \<mu> ::"_ \<Rightarrow> real"
  assumes "vwb_lens a"
    and Uhyp: "\<And>s. s \<in> S \<Longrightarrow> is_interval (U s)"
    and Gg: "\<And>X t s. (D X = (\<lambda>\<tau>. (f\<down>\<^sub>V\<^sub>e\<^sub>c\<^bsub>a\<^esub> s) \<tau> (X \<tau>)) on U (X t\<^sub>0)) 
      \<Longrightarrow> (\<forall>\<tau>\<in>U(X t\<^sub>0). \<tau> > t\<^sub>0 \<longrightarrow> G (put\<^bsub>a\<^esub> s (X \<tau>)) \<longrightarrow> \<nu>' (put\<^bsub>a\<^esub> s (X \<tau>)) \<le> \<mu>' (put\<^bsub>a\<^esub> s (X \<tau>)))"
    and Gl: "\<And>X s. (D X = (\<lambda>\<tau>. (f\<down>\<^sub>V\<^sub>e\<^sub>c\<^bsub>a\<^esub> s) \<tau> (X \<tau>)) on U(X t\<^sub>0)) 
      \<Longrightarrow> (\<forall>\<tau>\<in>U(X t\<^sub>0). \<tau> < t\<^sub>0 \<longrightarrow> \<mu>' (put\<^bsub>a\<^esub> s (X \<tau>)) \<le> \<nu>' (put\<^bsub>a\<^esub> s (X \<tau>)))"
    and dX: "\<And>X t s. (D X = (\<lambda>\<tau>. (f\<down>\<^sub>V\<^sub>e\<^sub>c\<^bsub>a\<^esub> s) \<tau> (X \<tau>)) on U (X t\<^sub>0)) 
      \<Longrightarrow> (D (\<lambda>\<tau>. \<mu> (put\<^bsub>a\<^esub> s (X \<tau>)) - \<nu> (put\<^bsub>a\<^esub> s (X \<tau>))) = (\<lambda>\<tau>. \<mu>' (put\<^bsub>a\<^esub> s (X \<tau>)) - \<nu>' (put\<^bsub>a\<^esub> s (X \<tau>))) on U (X t\<^sub>0))"
  shows "diff_inv_on a f G U S t\<^sub>0 (\<nu> \<le> \<mu>)\<^sub>e"
  apply (clarsimp simp: diff_inv_on_iff[OF assms(1)])
  apply (rule diff_inv_leq_alt[OF Uhyp, where \<mu>'="\<lambda>c. \<mu>' (put\<^bsub>a\<^esub> _ c)" and \<nu>'="\<lambda>c. \<nu>' (put\<^bsub>a\<^esub> _ c)"])
  using assms by auto

lemma diff_inv_on_lessI [diff_inv_on_intros]:
  fixes \<mu> ::"_ \<Rightarrow> real"
  assumes "vwb_lens a"
    and Uhyp: "\<And>s. s \<in> S \<Longrightarrow> is_interval (U s)"
    and Gg: "\<And>X t s. (D X = (\<lambda>\<tau>. (f\<down>\<^sub>V\<^sub>e\<^sub>c\<^bsub>a\<^esub> s) \<tau> (X \<tau>)) on U (X t\<^sub>0)) 
      \<Longrightarrow> (\<forall>\<tau>\<in>U(X t\<^sub>0). \<tau> > t\<^sub>0 \<longrightarrow> G (put\<^bsub>a\<^esub> s (X \<tau>)) \<longrightarrow> \<nu>' (put\<^bsub>a\<^esub> s (X \<tau>)) \<le> \<mu>' (put\<^bsub>a\<^esub> s (X \<tau>)))"
    and Gl: "\<And>X s. (D X = (\<lambda>\<tau>. (f\<down>\<^sub>V\<^sub>e\<^sub>c\<^bsub>a\<^esub> s) \<tau> (X \<tau>)) on U(X t\<^sub>0)) 
      \<Longrightarrow> (\<forall>\<tau>\<in>U(X t\<^sub>0). \<tau> < t\<^sub>0 \<longrightarrow> \<mu>' (put\<^bsub>a\<^esub> s (X \<tau>)) \<le> \<nu>' (put\<^bsub>a\<^esub> s (X \<tau>)))"
    and dX: "\<And>X t s. (D X = (\<lambda>\<tau>. (f\<down>\<^sub>V\<^sub>e\<^sub>c\<^bsub>a\<^esub> s) \<tau> (X \<tau>)) on U (X t\<^sub>0)) 
      \<Longrightarrow> (D (\<lambda>\<tau>. \<mu> (put\<^bsub>a\<^esub> s (X \<tau>)) - \<nu> (put\<^bsub>a\<^esub> s (X \<tau>))) = (\<lambda>\<tau>. \<mu>' (put\<^bsub>a\<^esub> s (X \<tau>)) - \<nu>' (put\<^bsub>a\<^esub> s (X \<tau>))) on U (X t\<^sub>0))"
  shows "diff_inv_on a f G U S t\<^sub>0 (\<nu> < \<mu>)\<^sub>e "
  apply (clarsimp simp: diff_inv_on_iff[OF assms(1)])
  apply (rule diff_inv_less_alt[OF Uhyp, where \<mu>'="\<lambda>c. \<mu>' (put\<^bsub>a\<^esub> _ c)" and \<nu>'="\<lambda>c. \<nu>' (put\<^bsub>a\<^esub> _ c)"])
  using assms by auto

lemma diff_inv_on_nleq_iff:
  fixes \<mu>::"_ \<Rightarrow> real"
  shows "diff_inv_on a f G U S t\<^sub>0 (\<not> \<nu> \<le> \<mu>)\<^sub>e \<longleftrightarrow> diff_inv_on a f G U S t\<^sub>0 (\<nu> > \<mu>)\<^sub>e"
  unfolding approximation_preproc_push_neg(2) by presburger

lemma diff_inv_on_neqI [diff_inv_on_intros]:
  fixes \<mu>::"_ \<Rightarrow> real"
  assumes "vwb_lens a"
    and "diff_inv_on a f G U S t\<^sub>0 (\<nu> < \<mu>)\<^sub>e"
    and "diff_inv_on a f G U S t\<^sub>0 (\<nu> > \<mu>)\<^sub>e"
  shows "diff_inv_on a f G U S t\<^sub>0 (\<nu> \<noteq> \<mu>)\<^sub>e"
  using assms unfolding diff_inv_on_iff[OF assms(1)]
  using diff_inv_neqI by force

lemma 
  assumes "diff_inv_on a f G U S t\<^sub>0 (I\<^sub>1)\<^sub>e"
    and "diff_inv_on a f G U S t\<^sub>0 (I\<^sub>2)\<^sub>e"
  shows diff_inv_on_conjI [diff_inv_on_intros]: "diff_inv_on a f G U S t\<^sub>0 (I\<^sub>1 \<and> I\<^sub>2)\<^sub>e"
    and diff_inv_on_disjI [diff_inv_on_intros]: "diff_inv_on a f G U S t\<^sub>0 (I\<^sub>1 \<or> I\<^sub>2)\<^sub>e"
  using assms unfolding diff_inv_on_eq by auto

lemmas diff_inv_on_raw_eqI = diff_inv_on_eqI[unfolded expr_defs]
lemmas diff_inv_on_raw_leqI = diff_inv_on_leqI[unfolded expr_defs]
lemmas diff_inv_on_raw_lessI = diff_inv_on_lessI[unfolded expr_defs]
lemmas diff_inv_on_raw_conjI = diff_inv_on_conjI[unfolded expr_defs]
lemmas diff_inv_on_raw_disjjI = diff_inv_on_disjI[unfolded expr_defs]


subsubsection \<open> Non-framed-but-lensified differential invariant rules \<close>

named_theorems diff_inv_laws "encapsulating rules for (non-localised) differential invariants"

lemma diff_inv_eq_law [diff_inv_laws]:
  fixes \<mu>::"_ \<Rightarrow> real"
  assumes Uhyp: "\<And>s. s \<in> S \<Longrightarrow> is_interval (U s)"
    and dX: "\<And>X t. (D X = (\<lambda>\<tau>. f \<tau> (X \<tau>)) on U(X t\<^sub>0)) \<Longrightarrow> 
  \<forall>\<tau>\<in>(down (U(X t\<^sub>0)) t). G (X \<tau>) \<Longrightarrow> D (\<lambda>\<tau>. \<mu> (X \<tau>) - \<nu> (X \<tau>)) = (\<lambda>\<tau>. \<tau> *\<^sub>R 0) on U(X t\<^sub>0)"
  shows "diff_inv U S G f t\<^sub>0 (\<mu> = \<nu>)\<^sub>e"
  using assms by (simp add: SEXP_def, rule diff_inv_eqI, simp_all)

thm diff_inv_eq_law diff_inv_eqI[unfolded ] diff_inv_eq_law[unfolded expr_defs]
thm diff_inv_eqI[THEN ssubst[OF SEXP_def[of "\<lambda>s. \<mu> s = \<nu> s"], where P="\<lambda>q. diff_inv U S G f t\<^sub>0 q"]]

lemma diff_inv_leq_law [diff_inv_laws]:
  fixes \<mu>::"'a::banach \<Rightarrow> real"
  assumes Uhyp: "\<And>s. s \<in> S \<Longrightarrow> is_interval (U s)"
    and Gg: "\<And>X. (D X = (\<lambda>\<tau>. f \<tau> (X \<tau>)) on U (X t\<^sub>0)) \<Longrightarrow> (\<forall>\<tau>\<in>U (X t\<^sub>0). \<tau> > t\<^sub>0 \<longrightarrow> G (X \<tau>) \<longrightarrow> \<mu>' (X \<tau>) \<ge> \<nu>' (X \<tau>))"
    and Gl: "\<And>X. (D X = (\<lambda>\<tau>. f \<tau> (X \<tau>)) on U (X t\<^sub>0)) \<Longrightarrow> (\<forall>\<tau>\<in>U (X t\<^sub>0). \<tau> < t\<^sub>0 \<longrightarrow> \<mu>' (X \<tau>) \<le> \<nu>' (X \<tau>))"
    and dX: "\<And>X. (D X = (\<lambda>\<tau>. f \<tau> (X \<tau>)) on U (X t\<^sub>0)) \<Longrightarrow> D (\<lambda>\<tau>. \<mu>(X \<tau>)-\<nu>(X \<tau>)) = (\<lambda>\<tau>. \<mu>'(X \<tau>)-\<nu>'(X \<tau>)) on U (X t\<^sub>0)"
  shows "diff_inv U S G f t\<^sub>0 (\<nu> \<le> \<mu>)\<^sub>e"
  using assms
  by (simp add: SEXP_def, rule diff_inv_leq_alt, simp_all)

lemma diff_inv_less_law [diff_inv_laws]:
  fixes \<mu>::"'a::banach \<Rightarrow> real"
  assumes Uhyp: "\<And>s. s \<in> S \<Longrightarrow> is_interval (U s)"
    and Gg: "\<And>X. (D X = (\<lambda>\<tau>. f \<tau> (X \<tau>)) on U (X t\<^sub>0)) \<Longrightarrow> (\<forall>\<tau>\<in>U (X t\<^sub>0). \<tau> > t\<^sub>0 \<longrightarrow> G (X \<tau>) \<longrightarrow> \<mu>' (X \<tau>) \<ge> \<nu>' (X \<tau>))"
    and Gl: "\<And>X. (D X = (\<lambda>\<tau>. f \<tau> (X \<tau>)) on U (X t\<^sub>0)) \<Longrightarrow> (\<forall>\<tau>\<in>U (X t\<^sub>0). \<tau> < t\<^sub>0 \<longrightarrow> \<mu>' (X \<tau>) \<le> \<nu>' (X \<tau>))"
    and dX: "\<And>X. (D X = (\<lambda>\<tau>. f \<tau> (X \<tau>)) on U (X t\<^sub>0)) \<Longrightarrow> D (\<lambda>\<tau>. \<mu>(X \<tau>)-\<nu>(X \<tau>)) = (\<lambda>\<tau>. \<mu>'(X \<tau>)-\<nu>'(X \<tau>)) on U (X t\<^sub>0)"
  shows "diff_inv U S G f t\<^sub>0 (\<nu> < \<mu>)\<^sub>e"
  using assms
  by (simp add: SEXP_def, rule diff_inv_less_alt, simp_all)

lemma diff_inv_nleq_law:
  fixes \<mu>::"'a::banach \<Rightarrow> real"
  shows "diff_inv U S G f t\<^sub>0 (\<not> \<nu> \<le> \<mu>)\<^sub>e \<longleftrightarrow> diff_inv U S G f t\<^sub>0 (\<nu> > \<mu>)\<^sub>e"
  by (simp add: SEXP_def, subst diff_inv_nleq_iff, simp_all)

lemma diff_inv_neq_law [diff_inv_laws]:
  fixes \<mu>::"'a::banach \<Rightarrow> real"
  assumes "diff_inv U S G f t\<^sub>0 (\<nu> < \<mu>)\<^sub>e"
    and "diff_inv U S G f t\<^sub>0 (\<nu> > \<mu>)\<^sub>e"
  shows "diff_inv U S G f t\<^sub>0 (\<nu> \<noteq> \<mu>)\<^sub>e"
  using assms apply(simp add: SEXP_def)
  by (rule diff_inv_neqI, simp_all)

lemma diff_inv_neq_law_converse:
  fixes \<mu>::"'a::banach \<Rightarrow> real"
  assumes Uhyp: "\<And>s. s \<in> S \<Longrightarrow> is_interval (U s)" "\<And>s t. s \<in> S \<Longrightarrow> t \<in> U s \<Longrightarrow> t\<^sub>0 \<le> t"
    and conts: "\<And>X. (D X = (\<lambda>\<tau>. f \<tau> (X \<tau>)) on U (X t\<^sub>0)) \<Longrightarrow> continuous_on (\<P> X (U (X t\<^sub>0))) \<nu>"
      "\<And>X. (D X = (\<lambda>\<tau>. f \<tau> (X \<tau>)) on U (X t\<^sub>0)) \<Longrightarrow> continuous_on (\<P> X (U (X t\<^sub>0))) \<mu>"
    and dI:"diff_inv U S G f t\<^sub>0 (\<nu> \<noteq> \<mu>)\<^sub>e"
  shows "diff_inv U S G f t\<^sub>0 (\<nu> < \<mu>)\<^sub>e"
  using assms apply(simp add: SEXP_def)
  by (rule diff_inv_neqE, simp_all)

lemma
  assumes "diff_inv U S G f t\<^sub>0 (I\<^sub>1)\<^sub>e"
    and "diff_inv U S G f t\<^sub>0 (I\<^sub>2)\<^sub>e"
  shows diff_inv_conj_law [diff_inv_laws]: "diff_inv U S G f t\<^sub>0 (I\<^sub>1 \<and> I\<^sub>2)\<^sub>e"
    and diff_inv_disj_law [diff_inv_laws]: "diff_inv U S G f t\<^sub>0 (I\<^sub>1 \<or> I\<^sub>2)\<^sub>e"
  using assms unfolding diff_inv_eq by auto

end