(*  Title: ODEs with lenses *)

section \<open> ODEs with lenses \<close>

text \<open> We use shallow expressions to rephrase the properties for hybrid systems in a 
cleaner presentation. \<close>

theory Framed_Dyn_Sys
  imports 
    Dynamical_Systems 
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

definition diff_inv_on :: "('c:: real_normed_vector \<Longrightarrow> 's) \<Rightarrow> (real \<Rightarrow> 's \<Rightarrow> 's) 
  \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> real set) \<Rightarrow> 'c set \<Rightarrow> real \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> bool" 
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

named_theorems diff_inv_on_intros "intro rules for certifying (localised) differential invariants"

lemma diff_inv_on_eq0I:
  fixes \<mu> :: "_ \<Rightarrow> 'c::real_inner"
  assumes "vwb_lens x"
    and Uhyp: "\<And>s. s \<in> S \<Longrightarrow> is_interval (U s)"
    and dX: "\<And>X t s. (D X = (\<lambda>\<tau>. (f\<down>\<^sub>V\<^sub>e\<^sub>c\<^bsub>x\<^esub> s) \<tau> (X \<tau>)) on U (X t\<^sub>0)) \<Longrightarrow>
  \<forall>\<tau>\<in>(down (U (X t\<^sub>0)) t). G (put\<^bsub>x\<^esub> s (X \<tau>)) \<Longrightarrow> (D (\<lambda>\<tau>. \<mu> (put\<^bsub>x\<^esub> s (X \<tau>))) = (\<lambda>t. 0) on U (X t\<^sub>0))"
  shows "diff_inv_on x f G U S t\<^sub>0 (\<mu> = 0)\<^sub>e"
  unfolding diff_inv_on_iff[OF assms(1)]
  apply (clarsimp, subst diff_inv_eq0I[OF Uhyp]; simp?)
  using dX by force

lemma diff_inv_on_eqI [diff_inv_on_intros]:
  fixes \<mu> \<nu> :: "_ \<Rightarrow> 'c::real_inner"
  assumes "vwb_lens x" (* do we need derivative rules for loc_subst then? *)
    and Uhyp: "\<And>s. s \<in> S \<Longrightarrow> is_interval (U s)"
    and dX: "\<And>X t s. (D X = (\<lambda>\<tau>. (f\<down>\<^sub>V\<^sub>e\<^sub>c\<^bsub>x\<^esub> s) \<tau> (X \<tau>)) on U (X t\<^sub>0)) \<Longrightarrow>
  \<forall>\<tau>\<in>(down (U (X t\<^sub>0)) t). G (put\<^bsub>x\<^esub> s (X \<tau>)) \<Longrightarrow> (D (\<lambda>\<tau>. \<mu> (put\<^bsub>x\<^esub> s (X \<tau>))-\<nu>(put\<^bsub>x\<^esub> s (X \<tau>))) = (\<lambda>t. 0) on U (X t\<^sub>0))"
  shows "diff_inv_on x f G U S t\<^sub>0 (\<mu> = \<nu>)\<^sub>e"
  using assms diff_inv_on_eq0I[OF assms(1,2), where \<mu>="\<lambda>s. \<mu> s - \<nu> s"]
  by auto

lemma diff_inv_on_leqI [diff_inv_on_intros]:
  fixes \<mu> ::"_ \<Rightarrow> real"
  assumes "vwb_lens x"
    and Uhyp: "\<And>s. s \<in> S \<Longrightarrow> is_interval (U s)"
    and Gg: "\<And>X t s. (D X = (\<lambda>\<tau>. (f\<down>\<^sub>V\<^sub>e\<^sub>c\<^bsub>x\<^esub> s) \<tau> (X \<tau>)) on U (X t\<^sub>0)) 
      \<Longrightarrow> (\<forall>\<tau>\<in>U(X t\<^sub>0). \<tau> > t\<^sub>0 \<longrightarrow> G (put\<^bsub>x\<^esub> s (X \<tau>)) \<longrightarrow> \<nu>' (put\<^bsub>x\<^esub> s (X \<tau>)) \<le> \<mu>' (put\<^bsub>x\<^esub> s (X \<tau>)))"
    and Gl: "\<And>X s. (D X = (\<lambda>\<tau>. (f\<down>\<^sub>V\<^sub>e\<^sub>c\<^bsub>x\<^esub> s) \<tau> (X \<tau>)) on U(X t\<^sub>0)) 
      \<Longrightarrow> (\<forall>\<tau>\<in>U(X t\<^sub>0). \<tau> < t\<^sub>0 \<longrightarrow> \<mu>' (put\<^bsub>x\<^esub> s (X \<tau>)) \<le> \<nu>' (put\<^bsub>x\<^esub> s (X \<tau>)))"
    and dX: "\<And>X t s. (D X = (\<lambda>\<tau>. (f\<down>\<^sub>V\<^sub>e\<^sub>c\<^bsub>x\<^esub> s) \<tau> (X \<tau>)) on U (X t\<^sub>0)) 
      \<Longrightarrow> (D (\<lambda>\<tau>. \<mu> (put\<^bsub>x\<^esub> s (X \<tau>)) - \<nu> (put\<^bsub>x\<^esub> s (X \<tau>))) = (\<lambda>\<tau>. \<mu>' (put\<^bsub>x\<^esub> s (X \<tau>)) - \<nu>' (put\<^bsub>x\<^esub> s (X \<tau>))) on U (X t\<^sub>0))"
  shows "diff_inv_on x f G U S t\<^sub>0 (\<nu> \<le> \<mu>)\<^sub>e"
  apply (clarsimp simp: diff_inv_on_iff[OF assms(1)])
  apply (rule diff_inv_leq_alt[OF Uhyp, where \<mu>'="\<lambda>c. \<mu>' (put\<^bsub>x\<^esub> _ c)" and \<nu>'="\<lambda>c. \<nu>' (put\<^bsub>x\<^esub> _ c)"])
  using assms by auto

lemma diff_inv_on_lessI [diff_inv_on_intros]:
  fixes \<mu> ::"_ \<Rightarrow> real"
  assumes "vwb_lens x"
    and Uhyp: "\<And>s. s \<in> S \<Longrightarrow> is_interval (U s)"
    and Gg: "\<And>X t s. (D X = (\<lambda>\<tau>. (f\<down>\<^sub>V\<^sub>e\<^sub>c\<^bsub>x\<^esub> s) \<tau> (X \<tau>)) on U (X t\<^sub>0)) 
      \<Longrightarrow> (\<forall>\<tau>\<in>U(X t\<^sub>0). \<tau> > t\<^sub>0 \<longrightarrow> G (put\<^bsub>x\<^esub> s (X \<tau>)) \<longrightarrow> \<nu>' (put\<^bsub>x\<^esub> s (X \<tau>)) \<le> \<mu>' (put\<^bsub>x\<^esub> s (X \<tau>)))"
    and Gl: "\<And>X s. (D X = (\<lambda>\<tau>. (f\<down>\<^sub>V\<^sub>e\<^sub>c\<^bsub>x\<^esub> s) \<tau> (X \<tau>)) on U(X t\<^sub>0)) 
      \<Longrightarrow> (\<forall>\<tau>\<in>U(X t\<^sub>0). \<tau> < t\<^sub>0 \<longrightarrow> \<mu>' (put\<^bsub>x\<^esub> s (X \<tau>)) \<le> \<nu>' (put\<^bsub>x\<^esub> s (X \<tau>)))"
    and dX: "\<And>X t s. (D X = (\<lambda>\<tau>. (f\<down>\<^sub>V\<^sub>e\<^sub>c\<^bsub>x\<^esub> s) \<tau> (X \<tau>)) on U (X t\<^sub>0)) 
      \<Longrightarrow> (D (\<lambda>\<tau>. \<mu> (put\<^bsub>x\<^esub> s (X \<tau>)) - \<nu> (put\<^bsub>x\<^esub> s (X \<tau>))) = (\<lambda>\<tau>. \<mu>' (put\<^bsub>x\<^esub> s (X \<tau>)) - \<nu>' (put\<^bsub>x\<^esub> s (X \<tau>))) on U (X t\<^sub>0))"
  shows "diff_inv_on x f G U S t\<^sub>0 (\<nu> < \<mu>)\<^sub>e "
  apply (clarsimp simp: diff_inv_on_iff[OF assms(1)])
  apply (rule diff_inv_less_alt[OF Uhyp, where \<mu>'="\<lambda>c. \<mu>' (put\<^bsub>x\<^esub> _ c)" and \<nu>'="\<lambda>c. \<nu>' (put\<^bsub>x\<^esub> _ c)"])
  using assms by auto

lemma diff_inv_on_nleq_iff:
  fixes \<mu>::"_ \<Rightarrow> real"
  shows "diff_inv_on x f G U S t\<^sub>0 (\<not> \<nu> \<le> \<mu>)\<^sub>e \<longleftrightarrow> diff_inv_on x f G U S t\<^sub>0 (\<nu> > \<mu>)\<^sub>e"
  unfolding approximation_preproc_push_neg(2) by presburger

lemma diff_inv_on_neqI [diff_inv_on_intros]:
  fixes \<mu>::"_ \<Rightarrow> real"
  assumes "vwb_lens x"
    and "diff_inv_on x f G U S t\<^sub>0 (\<nu> < \<mu>)\<^sub>e"
    and "diff_inv_on x f G U S t\<^sub>0 (\<nu> > \<mu>)\<^sub>e"
  shows "diff_inv_on x f G U S t\<^sub>0 (\<nu> \<noteq> \<mu>)\<^sub>e"
  using assms unfolding diff_inv_on_iff[OF assms(1)]
  using diff_inv_neqI by force

lemma 
  assumes "diff_inv_on x f G U S t\<^sub>0 (I\<^sub>1)\<^sub>e"
    and "diff_inv_on x f G U S t\<^sub>0 (I\<^sub>2)\<^sub>e"
  shows diff_inv_on_conjI [diff_inv_on_intros]: "diff_inv_on x f G U S t\<^sub>0 (I\<^sub>1 \<and> I\<^sub>2)\<^sub>e"
    and diff_inv_on_disjI [diff_inv_on_intros]: "diff_inv_on x f G U S t\<^sub>0 (I\<^sub>1 \<or> I\<^sub>2)\<^sub>e"
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