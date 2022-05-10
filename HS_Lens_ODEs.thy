(*  Title: ODEs with lenses *)

section \<open> ODEs with lenses \<close>

text \<open> We use shallow expressions to rephrase the properties for hybrid systems in a 
cleaner presentation. \<close>

theory HS_Lens_ODEs
  imports "HS_ODEs" "Hybrid-Library.Cont_Lens" "Shallow-Expressions.Shallow_Expressions"
begin

no_notation id_lens ("1\<^sub>L")
notation id_lens ("\<one>\<^sub>L")

subsection \<open> ODEs and Orbits  \<close>

text \<open> Localise a substitution using a lens. Useful for localising both ODEs and flows. \<close>

abbreviation loc_subst :: 
  "('c \<Longrightarrow> 's)              \<comment> \<open> lens selecting @{typ 'c}, a local region \<close> 
   \<Rightarrow> (real \<Rightarrow> 's \<Rightarrow> 's)     \<comment> \<open> substitution on the global state space @{typ 's}\<close>
   \<Rightarrow> 's                    \<comment> \<open> initial global state \<close>
   \<Rightarrow> (real \<Rightarrow> 'c \<Rightarrow> 'c)"    \<comment> \<open> substitution on the local state space @{typ 'c} \<close>
   where "loc_subst a f s \<equiv> (\<lambda> t c. get\<^bsub>a\<^esub> (f t (put\<^bsub>a\<^esub> s c)))"

text \<open> A version of guarded orbits localised by a lens \<close>

text \<open> A version of orbital localised by a lens \<close>

definition g_orbital_on :: "('c::real_normed_vector \<Longrightarrow> 'a) \<Rightarrow> (real \<Rightarrow> 'a \<Rightarrow> 'a) 
  \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> real set) \<Rightarrow> 'c set \<Rightarrow> real => 'a \<Rightarrow> 'a set"
  where "g_orbital_on a f G U S t\<^sub>0 s
    = \<P> (put\<^bsub>a\<^esub> s) (g_orbital (loc_subst a f s) (\<lambda>c. G (put\<^bsub>a\<^esub> s c)) U S t\<^sub>0 (get\<^bsub>a\<^esub> s))"

lemma g_orbital_on_id_lens: "g_orbital_on \<one>\<^sub>L = g_orbital"
  by (simp add: g_orbital_on_def fun_eq_iff lens_defs)

lemma g_orbital_on_eq: "g_orbital_on a f G U S t\<^sub>0 s = {put\<^bsub>a\<^esub> s (X t) |t X. 
  t \<in> U (get\<^bsub>a\<^esub> s) 
  \<and> \<P> (\<lambda>x. put\<^bsub>a\<^esub> s (X x)) (down (U (get\<^bsub>a\<^esub> s)) t) \<subseteq> {s. G s} 
  \<and> X \<in> Sols U S (loc_subst a f s) t\<^sub>0 (get\<^bsub>a\<^esub> s)}"
  unfolding g_orbital_on_def g_orbital_eq image_le_pred 
  by (auto simp: image_def)

lemma g_orbital_onI:
  assumes "X \<in> Sols U S (\<lambda>t c. get\<^bsub>a\<^esub> (f t (put\<^bsub>a\<^esub> s c))) t\<^sub>0 (get\<^bsub>a\<^esub> s)"
    and "t \<in> U (get\<^bsub>a\<^esub> s)" and "(\<P> (\<lambda>x. put\<^bsub>a\<^esub> s (X x)) (down (U (get\<^bsub>a\<^esub> s)) t) \<subseteq> Collect G)"
  shows "put\<^bsub>a\<^esub> s (X t) \<in> g_orbital_on a f G U S t\<^sub>0 s"
  using assms unfolding g_orbital_on_eq by auto

subsection \<open> Differential Invariants \<close>

definition diff_inv_on :: "('a \<Rightarrow> bool) \<Rightarrow> ('c:: real_normed_vector \<Longrightarrow> 'a) \<Rightarrow> (real \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 
  ('c \<Rightarrow> real set) \<Rightarrow> 'c set \<Rightarrow> real \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" 
  where "diff_inv_on I a f U S t\<^sub>0 G \<equiv> (\<Union> \<circ> (\<P> (g_orbital_on a f G U S t\<^sub>0))) {s. I s} \<subseteq> {s. I s}"

lemma diff_inv_on_eq: "diff_inv_on I a f U S t\<^sub>0 G = 
  (\<forall>s. I s \<longrightarrow> (\<forall>X\<in>Sols U S (loc_subst a f s) t\<^sub>0 (get\<^bsub>a\<^esub> s). 
    (\<forall>t\<in>U (get\<^bsub>a\<^esub> s).(\<forall>\<tau>\<in>(down (U (get\<^bsub>a\<^esub> s)) t). G (put\<^bsub>a\<^esub> s (X \<tau>))) \<longrightarrow> I (put\<^bsub>a\<^esub> s (X t)))))"
  unfolding diff_inv_on_def g_orbital_on_eq image_le_pred by (auto simp: image_def)

lemma diff_inv_on_id_lens: "diff_inv_on I \<one>\<^sub>L f U S t\<^sub>0 G = diff_inv U S G f t\<^sub>0 I"
  by (simp add: diff_inv_on_def diff_inv_def g_orbital_on_id_lens)

lemma diff_inv_on_iff:
  assumes"vwb_lens a"
  shows "diff_inv_on I a f U S t\<^sub>0 G \<longleftrightarrow> 
  (\<forall>s. diff_inv U S (\<lambda>c. G (put\<^bsub>a\<^esub> s c)) (loc_subst a f s) t\<^sub>0 (\<lambda>c. I (put\<^bsub>a\<^esub> s c)))"
proof(intro iffI, goal_cases "(\<Rightarrow>)" "(\<Leftarrow>)")
  case ("(\<Rightarrow>)")
  then show ?case 
    using assms
    by (auto simp: diff_inv_on_eq diff_inv_eq)
next
  case "(\<Leftarrow>)"
  thus ?case
    apply(clarsimp simp: diff_inv_on_eq diff_inv_eq)
    apply (erule_tac x=s in allE, erule_tac x="get\<^bsub>a\<^esub> s" in allE)
    using assms by auto
qed


subsubsection \<open> framed differential invariant rules \<close>

named_theorems diff_inv_on_intros "intro rules for certifying (localised) differential invariants"

lemma diff_inv_on_eq0I:
  fixes \<mu> :: "_ \<Rightarrow> 'c::real_inner"
  assumes "vwb_lens a"
    and Uhyp: "\<And>s. s \<in> S \<Longrightarrow> is_interval (U s)"
    and dX: "\<And>X t s. (D X = (\<lambda>\<tau>. (loc_subst a f s) \<tau> (X \<tau>)) on U (X t\<^sub>0)) \<Longrightarrow>
  \<forall>\<tau>\<in>(down (U (X t\<^sub>0)) t). G (put\<^bsub>a\<^esub> s (X \<tau>)) \<Longrightarrow> (D (\<lambda>\<tau>. \<mu> (put\<^bsub>a\<^esub> s (X \<tau>))) = (\<lambda>t. 0) on U (X t\<^sub>0))"
  shows "diff_inv_on (\<mu> = 0)\<^sub>e a f U S t\<^sub>0 G"
  unfolding diff_inv_on_iff[OF assms(1)]
  apply (clarsimp, subst diff_inv_eq0I[OF Uhyp]; simp?)
  using dX by force

lemma diff_inv_on_eqI [diff_inv_on_intros]:
  fixes \<mu> \<nu> :: "_ \<Rightarrow> 'c::real_inner"
  assumes "vwb_lens a" (* do we need derivative rules for loc_subst then? *)
    and Uhyp: "\<And>s. s \<in> S \<Longrightarrow> is_interval (U s)"
    and dX: "\<And>X t s. (D X = (\<lambda>\<tau>. (loc_subst a f s) \<tau> (X \<tau>)) on U (X t\<^sub>0)) \<Longrightarrow>
  \<forall>\<tau>\<in>(down (U (X t\<^sub>0)) t). G (put\<^bsub>a\<^esub> s (X \<tau>)) \<Longrightarrow> (D (\<lambda>\<tau>. \<mu> (put\<^bsub>a\<^esub> s (X \<tau>))-\<nu>(put\<^bsub>a\<^esub> s (X \<tau>))) = (\<lambda>t. 0) on U (X t\<^sub>0))"
  shows "diff_inv_on (\<mu> = \<nu>)\<^sub>e a f U S t\<^sub>0 G"
  using assms diff_inv_on_eq0I[OF assms(1,2), where \<mu>="\<lambda>s. \<mu> s - \<nu> s"]
  by auto

lemma diff_inv_on_leqI [diff_inv_on_intros]:
  fixes \<mu> ::"'a::real_normed_vector \<Rightarrow> real"
  assumes "vwb_lens a"
    and Uhyp: "\<And>s. s \<in> S \<Longrightarrow> is_interval (U s)"
    and Gg: "\<And>X t s. (D X = (\<lambda>\<tau>. (loc_subst a f s) \<tau> (X \<tau>)) on U (X t\<^sub>0)) 
      \<Longrightarrow> (\<forall>\<tau>\<in>U(X t\<^sub>0). \<tau> > t\<^sub>0 \<longrightarrow> G (put\<^bsub>a\<^esub> s (X \<tau>)) \<longrightarrow> \<nu>' (put\<^bsub>a\<^esub> s (X \<tau>)) \<le> \<mu>' (put\<^bsub>a\<^esub> s (X \<tau>)))"
    and Gl: "\<And>X s. (D X = (\<lambda>\<tau>. (loc_subst a f s) \<tau> (X \<tau>)) on U(X t\<^sub>0)) 
      \<Longrightarrow> (\<forall>\<tau>\<in>U(X t\<^sub>0). \<tau> < t\<^sub>0 \<longrightarrow> \<mu>' (put\<^bsub>a\<^esub> s (X \<tau>)) \<le> \<nu>' (put\<^bsub>a\<^esub> s (X \<tau>)))"
    and dX: "\<And>X t s. (D X = (\<lambda>\<tau>. (loc_subst a f s) \<tau> (X \<tau>)) on U (X t\<^sub>0)) 
      \<Longrightarrow> (D (\<lambda>\<tau>. \<mu> (put\<^bsub>a\<^esub> s (X \<tau>)) - \<nu> (put\<^bsub>a\<^esub> s (X \<tau>))) = (\<lambda>\<tau>. \<mu>' (put\<^bsub>a\<^esub> s (X \<tau>)) - \<nu>' (put\<^bsub>a\<^esub> s (X \<tau>))) on U (X t\<^sub>0))"
  shows "diff_inv_on (\<nu> \<le> \<mu>)\<^sub>e a f U S t\<^sub>0 G"
  apply (clarsimp simp: diff_inv_on_iff[OF assms(1)])
  apply (rule diff_inv_leq_alt[OF Uhyp, where \<mu>'="\<lambda>c. \<mu>' (put\<^bsub>a\<^esub> _ c)" and \<nu>'="\<lambda>c. \<nu>' (put\<^bsub>a\<^esub> _ c)"])
  using assms by auto

lemma diff_inv_on_lessI [diff_inv_on_intros]:
  fixes \<mu> ::"'a::real_normed_vector \<Rightarrow> real"
  assumes "vwb_lens a"
    and Uhyp: "\<And>s. s \<in> S \<Longrightarrow> is_interval (U s)"
    and Gg: "\<And>X t s. (D X = (\<lambda>\<tau>. (loc_subst a f s) \<tau> (X \<tau>)) on U (X t\<^sub>0)) 
      \<Longrightarrow> (\<forall>\<tau>\<in>U(X t\<^sub>0). \<tau> > t\<^sub>0 \<longrightarrow> G (put\<^bsub>a\<^esub> s (X \<tau>)) \<longrightarrow> \<nu>' (put\<^bsub>a\<^esub> s (X \<tau>)) \<le> \<mu>' (put\<^bsub>a\<^esub> s (X \<tau>)))"
    and Gl: "\<And>X s. (D X = (\<lambda>\<tau>. (loc_subst a f s) \<tau> (X \<tau>)) on U(X t\<^sub>0)) 
      \<Longrightarrow> (\<forall>\<tau>\<in>U(X t\<^sub>0). \<tau> < t\<^sub>0 \<longrightarrow> \<mu>' (put\<^bsub>a\<^esub> s (X \<tau>)) \<le> \<nu>' (put\<^bsub>a\<^esub> s (X \<tau>)))"
    and dX: "\<And>X t s. (D X = (\<lambda>\<tau>. (loc_subst a f s) \<tau> (X \<tau>)) on U (X t\<^sub>0)) 
      \<Longrightarrow> (D (\<lambda>\<tau>. \<mu> (put\<^bsub>a\<^esub> s (X \<tau>)) - \<nu> (put\<^bsub>a\<^esub> s (X \<tau>))) = (\<lambda>\<tau>. \<mu>' (put\<^bsub>a\<^esub> s (X \<tau>)) - \<nu>' (put\<^bsub>a\<^esub> s (X \<tau>))) on U (X t\<^sub>0))"
  shows "diff_inv_on (\<nu> < \<mu>)\<^sub>e a f U S t\<^sub>0 G"
  apply (clarsimp simp: diff_inv_on_iff[OF assms(1)])
  apply (rule diff_inv_less_alt[OF Uhyp, where \<mu>'="\<lambda>c. \<mu>' (put\<^bsub>a\<^esub> _ c)" and \<nu>'="\<lambda>c. \<nu>' (put\<^bsub>a\<^esub> _ c)"])
  using assms by auto

lemma diff_inv_on_nleq_iff:
  fixes \<mu>::"'a::real_normed_vector \<Rightarrow> real"
  shows "diff_inv_on (\<not> \<nu> \<le> \<mu>)\<^sub>e a f U S t\<^sub>0 G \<longleftrightarrow> diff_inv_on (\<nu> > \<mu>)\<^sub>e a f U S t\<^sub>0 G"
  unfolding approximation_preproc_push_neg(2) by presburger

lemma diff_inv_on_neqI [diff_inv_on_intros]:
  fixes \<mu>::"'a::real_normed_vector \<Rightarrow> real"
  assumes "vwb_lens a"
    and "diff_inv_on (\<nu> < \<mu>)\<^sub>e a f U S t\<^sub>0 G"
    and "diff_inv_on (\<nu> > \<mu>)\<^sub>e a f U S t\<^sub>0 G"
  shows "diff_inv_on (\<nu> \<noteq> \<mu>)\<^sub>e a f U S t\<^sub>0 G"
  using assms unfolding diff_inv_on_iff[OF assms(1)]
  using diff_inv_neqI by force

lemma 
  assumes "diff_inv_on (I\<^sub>1)\<^sub>e a f U S t\<^sub>0 G"
    and "diff_inv_on (I\<^sub>2)\<^sub>e a f U S t\<^sub>0 G"
  shows diff_inv_on_conjI [diff_inv_on_intros]: "diff_inv_on (I\<^sub>1 \<and> I\<^sub>2)\<^sub>e a f U S t\<^sub>0 G"
    and diff_inv_on_disjI [diff_inv_on_intros]: "diff_inv_on (I\<^sub>1 \<or> I\<^sub>2)\<^sub>e a f U S t\<^sub>0 G"
  using assms unfolding diff_inv_on_eq by auto


subsubsection \<open> Non-framed-but-lensified differential invariant rules \<close>

named_theorems diff_inv_laws "encapsulating rules for (non-localised) differential invariants"

lemma diff_inv_eq_law [diff_inv_laws]:
  fixes \<mu>::"'a::banach \<Rightarrow> real"
  assumes Uhyp: "\<And>s. s \<in> S \<Longrightarrow> is_interval (U s)"
    and dX: "\<And>X t. (D X = (\<lambda>\<tau>. f \<tau> (X \<tau>)) on U(X t\<^sub>0)) \<Longrightarrow> 
  \<forall>\<tau>\<in>(down (U(X t\<^sub>0)) t). G (X \<tau>) \<Longrightarrow> D (\<lambda>\<tau>. \<mu> (X \<tau>) - \<nu> (X \<tau>)) = (\<lambda>\<tau>. \<tau> *\<^sub>R 0) on U(X t\<^sub>0)"
  shows "diff_inv U S G f t\<^sub>0 (\<mu> = \<nu>)\<^sub>e"
  using assms by (simp add: SEXP_def, rule diff_inv_eqI, simp_all)

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

subsection \<open> Differential ghosts \<close>

lemma diff_ghost_very_simple:
  assumes 
    "vwb_lens y" "y \<bowtie> a" "y \<sharp>\<^sub>s \<sigma>" "$y \<sharp> B"
    "diff_inv_on (G)\<^sub>e (a +\<^sub>L y) (\<lambda>t. \<sigma>(y \<leadsto> \<guillemotleft>k\<guillemotright> *\<^sub>R $y)) (Collect ((\<le>) 0))\<^sub>e UNIV 0 B"
  shows "diff_inv_on (G \\ $y)\<^sub>e a (\<lambda>t. \<sigma>) (Collect ((\<le>) 0))\<^sub>e UNIV 0 B"
  using assms(5)
  apply (simp add: expr_defs diff_inv_on_eq)
  apply (auto)
  apply (rename_tac s X s' t)
  apply (drule_tac x="s \<triangleleft>\<^bsub>y\<^esub> s'" in spec)
  apply (auto)
  using assms(1) apply auto[1]
  apply (drule_tac x="\<lambda> t. (X t, exp (k * t) *\<^sub>R get\<^bsub>y\<^esub> s')" in bspec)
   apply (simp add: ivp_sols_def)
   apply (auto simp add: lens_defs has_vderiv_on_def)[1]
     apply (rule derivative_intros)
  using assms(1-4) apply (simp add: expr_defs)
      apply (metis lens_indep.lens_put_irr2 lens_indep_comm)
     apply (rule has_vector_derivative_eq_rhs)
      apply (force intro: derivative_intros)
     apply (simp)
  using assms(1-4)
     apply (simp_all add: lens_defs expr_defs lens_indep.lens_put_irr2)
  apply (metis assms(1) assms(2) lens_indep_def mwb_lens.axioms(1) vwb_lens_mwb weak_lens.put_get)
  done

end