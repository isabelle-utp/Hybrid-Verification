(*  Title:       ODEs and Dynamical Systems for HS verification
    Author:      Jonathan Julián Huerta y Munive, 2021
    Maintainer:  Jonathan Julián Huerta y Munive <jonjulian23@gmail.com>
*)

section \<open> Ordinary Differential Equations \<close>

text \<open>Vector fields @{text "f::real \<Rightarrow> 'a \<Rightarrow> ('a::real_normed_vector)"} represent systems 
of ordinary differential equations (ODEs). Picard-Lindeloef's theorem guarantees existence 
and uniqueness of local solutions to initial value problems involving Lipschitz continuous 
vector fields. A (local) flow @{text "\<phi>::real \<Rightarrow> 'a \<Rightarrow> ('a::real_normed_vector)"} for such 
a system is the function that maps initial conditions to their unique solutions. In dynamical 
systems, the set of all points @{text "\<phi> t s::'a"} for a fixed @{text "s::'a"} is the flow's 
orbit. If the orbit of each @{text "s \<in> I"} is conatined in @{text I}, then @{text I} is an 
invariant set of this system. This section formalises these concepts with a focus on hybrid 
systems (HS) verification.\<close>

theory Dynamical_Systems
  imports "HS_Preliminaries"
begin

subsection \<open> Initial value problems and orbits \<close>

notation image ("\<P>")

lemma image_le_pred[simp]: "(\<P> f A \<subseteq> {s. G s}) = (\<forall>x\<in>A. G (f x))"
  unfolding image_def by force

definition ivp_sols :: "(real \<Rightarrow> 'a \<Rightarrow> ('a::real_normed_vector)) \<Rightarrow> real set \<Rightarrow> real \<Rightarrow> 
  'a \<Rightarrow> (real \<Rightarrow> 'a) set" ("Sols")
  where "Sols f T t\<^sub>0 s = {X. (D X = (\<lambda>t. f t (X t)) on T) \<and> X t\<^sub>0 = s \<and> t\<^sub>0 \<in> T}"

lemma ivp_solsI: 
  assumes "D X = (\<lambda>t. f t (X t)) on T" 
      and "X t\<^sub>0 = s" and "t\<^sub>0 \<in> T"
    shows "X \<in> Sols f T t\<^sub>0 s"
  using assms unfolding ivp_sols_def by blast

lemma ivp_solsD:
  assumes "X \<in> Sols f T t\<^sub>0 s"
  shows "D X = (\<lambda>t. f t (X t)) on T" 
    and "X t\<^sub>0 = s" and "t\<^sub>0 \<in> T"
  using assms unfolding ivp_sols_def by auto

lemma in_ivp_sols_subset:
  "t\<^sub>0 \<in> T \<Longrightarrow> T \<subseteq> U \<Longrightarrow> X \<in> Sols f U t\<^sub>0 s \<Longrightarrow> X \<in> Sols f T t\<^sub>0 s "
  apply(rule ivp_solsI)
  using ivp_solsD(1,2) has_vderiv_on_subset by blast+

(*definition g_orbit :: "('a \<Rightarrow> bool) \<Rightarrow> ('b::real_vector) set \<Rightarrow> 'b \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'a set" ("\<gamma>")
  where "\<gamma> G T t\<^sub>0 X = \<Union> {\<P> X T  |t. \<P> X {t\<^sub>0--t} \<subseteq> {s. G s}}" 

lemma g_orbit_eq: "\<gamma> G T t\<^sub>0 X = {X t |t. t \<in> T \<and> (\<forall>\<tau>\<in>{t\<^sub>0--t}. G (X \<tau>))}"
  apply(rule set_eqI2; clarsimp simp: g_orbit_def)
  apply(rename_tac \<tau> t)
  apply(rule_tac x=\<tau> in exI, simp)*)

definition g_orbit :: "('a \<Rightarrow> bool) \<Rightarrow> ('b::real_vector) set \<Rightarrow> 'b \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'a set" ("\<gamma>")
  where "\<gamma> G T t\<^sub>0 X = {X t |t. t \<in> T \<and> (\<forall>\<tau>\<in>{t\<^sub>0--t}. G (X \<tau>))}"

definition g_orbital :: "(real \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> real set) \<Rightarrow> real \<Rightarrow> 
  ('a::real_normed_vector) \<Rightarrow> 'a set" 
  where "g_orbital f G U t\<^sub>0 s = \<Union>{\<gamma> G {t\<^sub>0--t} t\<^sub>0 X |X t. {t\<^sub>0--t} \<subseteq> U s \<and> X \<in> Sols f {t\<^sub>0--t} t\<^sub>0 s}"

lemma g_orbital_eq: "g_orbital f G U t\<^sub>0 s = 
  {X t |t X. {t\<^sub>0--t} \<subseteq> U s \<and> \<P> X ({t\<^sub>0--t}) \<subseteq> {s. G s} \<and> X \<in> Sols f {t\<^sub>0--t} t\<^sub>0 s }"
proof(rule set_eqI2; clarsimp simp: g_orbital_def g_orbit_def)
  fix X t \<tau>
  assume xivp: "X \<in> Sols f {t\<^sub>0--t} t\<^sub>0 s" 
    and ivl: "\<tau> \<in> {t\<^sub>0--t}" "{t\<^sub>0--t} \<subseteq> U s"
    and guard: "\<forall>r\<in>{t\<^sub>0--\<tau>}. G (X r)"
  hence "X \<in> Sols f {t\<^sub>0--\<tau>} t\<^sub>0 s"
    by (auto simp: closed_segment_eq_real_ivl 
        intro!: in_ivp_sols_subset[OF _ _ xivp])
  moreover have "{t\<^sub>0--\<tau>} \<subseteq> U s"
    using ivl by (auto simp: closed_segment_eq_real_ivl split: if_splits)
  ultimately show "\<exists>r Y. X \<tau> = Y r \<and> {t\<^sub>0--r} \<subseteq> U s \<and> 
  (\<forall>r\<in>{t\<^sub>0--r}. G (Y r)) \<and> Y \<in> Sols f {t\<^sub>0--r} t\<^sub>0 s"
    using guard by auto
next
  fix t X
  assume xivp: "X \<in> Sols f {t\<^sub>0--t} t\<^sub>0 s" 
    and ivl: "{t\<^sub>0--t} \<subseteq> U s"
    and guard: "\<forall>\<tau>\<in>{t\<^sub>0--t}. G (X \<tau>)"
  hence "X t \<in> \<gamma> G {t\<^sub>0--t} t\<^sub>0 X"
    unfolding g_orbit_def by auto
  thus "\<exists>\<rho>. (\<exists>X t. \<rho> = {X \<tau> |\<tau>. \<tau> \<in> {t\<^sub>0--t} \<and> (\<forall>r\<in>{t\<^sub>0--\<tau>}. G (X r))} \<and>
  {t\<^sub>0--t} \<subseteq> U s \<and> X \<in> Sols f {t\<^sub>0--t} t\<^sub>0 s) \<and> X t \<in> \<rho>"
    using xivp ivl guard by auto
qed

lemma g_orbitalI:
  assumes "X \<in> Sols f {t\<^sub>0--t} t\<^sub>0 s"
    and "{t\<^sub>0--t} \<subseteq> U s" and "\<P> X ({t\<^sub>0--t}) \<subseteq> {s. G s}"
  shows "X t \<in> g_orbital f G U t\<^sub>0 s"
  using assms unfolding g_orbital_eq by auto

lemma g_orbitalD:
  assumes "s' \<in> g_orbital f G U t\<^sub>0 s"
  obtains X and t where "X \<in> Sols f {t\<^sub>0--t} t\<^sub>0 s"
  and "X t = s'" and "{t\<^sub>0--t} \<subseteq> U s" and "\<P> X ({t\<^sub>0--t}) \<subseteq> {s. G s}"
  using assms unfolding g_orbital_eq by auto

lemma g_orbital_eq_dL_semantics: "g_orbital f G (\<lambda>s. {t. t \<ge> 0}) 0 s =
  {X t |t X. t \<ge> 0 \<and> (\<forall>\<tau>\<in>{0..t}. G (X \<tau>)) \<and> 
  (\<forall>\<tau>\<in>{0..t}. (X has_vector_derivative (f \<tau> (X \<tau>))) (at \<tau> within {0..t})) \<and> X 0 = s}"
  unfolding g_orbital_eq g_orbit_def ivp_sols_def has_vderiv_on_def 
  apply (rule set_eqI2; clarsimp simp: closed_segment_eq_real_ivl split: if_splits)
  subgoal for s' t
    apply safe
   apply(rule_tac x=t in exI, rule_tac x=X in exI, clarsimp )
     apply (force simp: atLeastAtMost_def)
   apply(rule_tac x=t in exI, rule_tac x=X in exI)
     apply (force simp: atLeastAtMost_def)
    done
  by (rule_tac x=t in exI, clarsimp, rule_tac x=X in exI, clarsimp)


lemma "X \<in> Sols f {t\<^sub>0--t} t\<^sub>0 s \<Longrightarrow> {t\<^sub>0--t} \<subseteq> U s \<Longrightarrow> \<gamma> G {t\<^sub>0--t} t\<^sub>0 X \<subseteq> g_orbital f G U t\<^sub>0 s"
  unfolding g_orbital_def by auto

lemma "g_orbital f G U t\<^sub>0 s \<subseteq> g_orbital f (\<lambda>s. True) U t\<^sub>0 s"
  unfolding g_orbital_eq by auto

lemma "\<nu> \<in> g_orbital f G (\<lambda>s. {t. t \<ge> 0}) 0 \<omega> \<longleftrightarrow> 
  (\<exists>t\<ge>0. \<exists>X\<in>Sols f {0..t} 0 \<omega>. X t = \<nu> \<and> (\<forall>\<tau>\<in>{0..t}. G (X \<tau>)))"
  by (simp add: g_orbital_eq_dL_semantics ivp_sols_def has_vderiv_on_def, rule iffI) force+

no_notation g_orbit ("\<gamma>")


subsection \<open> Differential Invariants \<close>

definition diff_inv :: "('a \<Rightarrow> bool) \<Rightarrow> (real \<Rightarrow> ('a::real_normed_vector) \<Rightarrow> 'a) \<Rightarrow> 
  ('a \<Rightarrow> real set) \<Rightarrow> real \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" 
  where "diff_inv I f U t\<^sub>0 G \<equiv> (\<Union> \<circ> (\<P> (g_orbital f G U t\<^sub>0))) {s. I s} \<subseteq> {s. I s}"

lemma diff_inv_eq: "diff_inv I f U t\<^sub>0 G = 
  (\<forall>s. I s \<longrightarrow> (\<forall>t. \<forall>X\<in>Sols f {t\<^sub>0--t} t\<^sub>0 s. {t\<^sub>0--t} \<subseteq> U s \<longrightarrow> (\<forall>\<tau>\<in>{t\<^sub>0--t}. G (X \<tau>)) \<longrightarrow> I (X t)))"
  unfolding diff_inv_def g_orbital_eq image_le_pred by auto

lemma diff_inv_eq_inv_set:
  "diff_inv I f U t\<^sub>0 G = (\<forall>s. I s \<longrightarrow> (g_orbital f G U t\<^sub>0 s) \<subseteq> {s. I s})"
  unfolding diff_inv_eq g_orbital_eq image_le_pred by auto

lemma "diff_inv I f U t\<^sub>0 (\<lambda>s. True) \<Longrightarrow> diff_inv I f U t\<^sub>0 G"
  unfolding diff_inv_eq by auto

thm filter_eq_iff eventually_at eventually_at_topological \<comment> \<open> filters \<close>
thm at_within_open at_within_open_subset at_within_Icc_at \<comment> \<open> at within \<close>
thm has_derivative_at_within Lim_ident_at \<comment> \<open> derivative at within \<close>
thm has_field_derivative_iff_has_vector_derivative \<comment> \<open> real vs vector derivative \<close>
thm Rolle_deriv mvt mvt_simple mvt_very_simple mvt_general \<comment> \<open> mean value theorem \<close>
thm has_derivative_componentwise_within tendsto_componentwise_iff bounded_linear_compose
thm c1_implies_local_lipschitz

lemma open_real_segment: "open {a<--<b}" for a::real
  unfolding open_segment_eq_real_ivl by auto

lemma has_derivative_at_within_iff: "(D f \<mapsto> f' (at x within S)) \<longleftrightarrow> bounded_linear f' \<and> 
  (\<forall>X. open X \<longrightarrow> 0 \<in> X \<longrightarrow> (\<exists>d>0. \<forall>s\<in>S. s \<noteq> x \<and> \<parallel>s - x\<parallel> < d \<longrightarrow> (f s - f x - f' (s - x)) /\<^sub>R \<parallel>s - x\<parallel> \<in> X))"
  unfolding has_derivative_at_within tendsto_def eventually_at dist_norm by simp

lemma has_vderiv_on_iff: "(D f = f' on T) \<longleftrightarrow> (\<forall>x\<in>T. D f \<mapsto> (\<lambda>h. h *\<^sub>R f' x) (at x within T))"
  unfolding has_vderiv_on_def has_vector_derivative_def by simp

lemma mvt_ivl_general:
  fixes f :: "real \<Rightarrow> 'a::real_inner"
  assumes "a \<noteq> b" and "continuous_on {a--b} f"
    and "\<forall>x\<in>{a<--<b}. D f \<mapsto> (f' x) (at x)"
  shows "\<exists>x\<in>{a<--<b}. \<parallel>f b - f a\<parallel> \<le> \<parallel>f' x \<bar>b - a\<bar>\<parallel>"
proof(cases "a < b")
  case True
  thus ?thesis 
    using closed_segment_eq_real_ivl open_segment_eq_real_ivl
      assms mvt_general[of a b f] by force
next
  case False
  hence "b < a" "{a--b} = {b..a}" "{a<--<b} = {b<..<a}"
    using assms closed_segment_eq_real_ivl open_segment_eq_real_ivl by auto
  hence cont: "continuous_on {b..a} f" and "\<forall>x\<in>{b<..<a}. D f \<mapsto> (f' x) (at x)"
    using assms by auto
  hence "\<exists>x\<in>{b<..<a}. \<parallel>f b - f a\<parallel> \<le> \<parallel>f' x \<bar>a - b\<bar>\<parallel>"
    using mvt_general[OF \<open>b < a\<close> cont, of f'] 
    by (auto simp: Real_Vector_Spaces.real_normed_vector_class.norm_minus_commute)
  thus ?thesis 
    by (subst \<open>{a<--<b} = {b<..<a}\<close>) auto
qed

named_theorems diff_inv_rules "rules for certifying differential invariants"

lemma diff_inv_eq0I:
  fixes \<mu>::"'a::real_normed_vector \<Rightarrow> 'b::real_inner"
  assumes "\<And>X t. {t\<^sub>0--t} \<subseteq> U (X t\<^sub>0) \<Longrightarrow> (D X = (\<lambda>\<tau>. f \<tau> (X \<tau>)) on {t\<^sub>0--t}) \<Longrightarrow> \<forall>\<tau>\<in>{t\<^sub>0--t}. G (X \<tau>) \<Longrightarrow> 
    D (\<lambda>\<tau>. \<mu> (X \<tau>)) = (\<lambda>\<tau>. \<tau> *\<^sub>R 0) on {t\<^sub>0--t}"
  shows "diff_inv (\<lambda>s. \<mu> s = 0) f U t\<^sub>0 G"
proof(clarsimp simp: diff_inv_eq ivp_sols_def)
  fix X t
  assume xivp: "D X = (\<lambda>\<tau>. f \<tau> (X \<tau>)) on {t\<^sub>0--t}" "\<mu> (X t\<^sub>0) = 0"
    and "\<forall>\<tau>\<in>{t\<^sub>0--t}. G (X \<tau>)" and "{t\<^sub>0--t} \<subseteq> U (X t\<^sub>0)"
  hence key: "D (\<lambda>\<tau>. \<mu> (X \<tau>)) = (\<lambda>\<tau>. \<tau> *\<^sub>R 0) on {t\<^sub>0--t}"
    using assms by blast
  hence "\<forall>\<tau>\<in>{t\<^sub>0<--<t}. D (\<lambda>\<tau>. \<mu> (X \<tau>)) \<mapsto> (\<lambda>t. 0) (at \<tau>)"
    using has_vderiv_on_subset[OF key segment_open_subset_closed, unfolded has_vderiv_on_iff]
      at_within_open[OF _ open_real_segment, of _ t\<^sub>0 t] by auto
  moreover note mvt_ivl_general[OF _ vderiv_on_continuous_on[OF key], of "\<lambda>\<tau> t. 0"]
  ultimately have "t\<^sub>0 \<noteq> t \<Longrightarrow> \<parallel>\<mu> (X t)\<parallel> = 0"
    using xivp by auto
  thus "\<mu> (X t) = 0"
    using xivp by auto
qed

lemma diff_inv_eqI [diff_inv_rules]:
  fixes \<mu>::"'a::real_normed_vector \<Rightarrow> 'b::real_inner"
  assumes "\<And>X t. {t\<^sub>0--t} \<subseteq> U (X t\<^sub>0) \<Longrightarrow> (D X = (\<lambda>\<tau>. f \<tau> (X \<tau>)) on {t\<^sub>0--t}) \<Longrightarrow> \<forall>\<tau>\<in>{t\<^sub>0--t}. G (X \<tau>) \<Longrightarrow> 
    D (\<lambda>\<tau>. \<mu> (X \<tau>) - \<nu> (X \<tau>)) = (\<lambda>\<tau>. \<tau> *\<^sub>R 0) on {t\<^sub>0--t}"
  shows "diff_inv (\<lambda>s. \<mu> s = \<nu> s) f U t\<^sub>0 G"
  using diff_inv_eq0I[where \<mu>="\<lambda>s. \<mu> s - \<nu> s"] assms by auto

text \<open> can this be generalised to @{term "\<mu>::'a::real_normed_vector \<Rightarrow> 'b::real_inner"}? \<close>
lemma 
  fixes \<mu>::"'a::real_normed_vector \<Rightarrow> real"
  assumes "\<And>X t. {t\<^sub>0--t} \<subseteq> U (X t\<^sub>0) \<Longrightarrow> (D X = (\<lambda>\<tau>. f \<tau> (X \<tau>)) on {t\<^sub>0--t}) \<Longrightarrow> \<forall>\<tau>\<in>{t\<^sub>0--t}. G (X \<tau>) \<Longrightarrow> 
    (D (\<lambda>\<tau>. \<mu> (X \<tau>)) = (\<lambda>\<tau>. \<mu>' (X \<tau>)) on {t\<^sub>0--t}) \<and> (\<forall>\<tau>\<in>{t\<^sub>0<--<t}. (\<tau> > t\<^sub>0 \<longrightarrow> \<mu>' (X \<tau>) \<ge> 0) \<and> (\<tau> < t\<^sub>0 \<longrightarrow> \<mu>' (X \<tau>) \<le> 0))"
  shows diff_inv_leq0I: "diff_inv (\<lambda>s. 0 \<le> \<mu> s) f U t\<^sub>0 G"
    and diff_inv_less0I: "diff_inv (\<lambda>s. 0 < \<mu> s) f U t\<^sub>0 G"
proof(auto simp: diff_inv_eq ivp_sols_def)
  fix X t
  assume xivp: "D X = (\<lambda>\<tau>. f \<tau> (X \<tau>)) on {t\<^sub>0--t}"
    and ghyp: "\<forall>\<tau>\<in>{t\<^sub>0--t}. G (X \<tau>)" and ivl: "{t\<^sub>0--t} \<subseteq> U (X t\<^sub>0)"
  hence key: "D (\<lambda>\<tau>. \<mu> (X \<tau>)) = (\<lambda>\<tau>. \<mu>' (X \<tau>)) on {t\<^sub>0--t}"
    using assms by auto
  {assume "t\<^sub>0 \<noteq> t"
    then obtain \<tau> where mvt: "\<mu> (X t) = (t - t\<^sub>0) * \<mu>' (X \<tau>) + \<mu> (X t\<^sub>0)" and "\<tau> \<in> {t\<^sub>0<--<t}"
      using mvt_simple_closed_segmentE[OF key] by (metis diff_add_cancel)
    hence "t\<^sub>0 < t \<Longrightarrow> t\<^sub>0 < \<tau>" and "t\<^sub>0 > t \<Longrightarrow> t\<^sub>0 > \<tau>"
      unfolding open_segment_eq_real_ivl by auto
    hence "t\<^sub>0 < t \<Longrightarrow> 0 \<le> \<mu>' (X \<tau>)" and "t < t\<^sub>0 \<Longrightarrow> \<mu>' (X \<tau>) \<le> 0"
      using assms[OF ivl xivp(1) ghyp] \<open>\<tau> \<in> {t\<^sub>0<--<t}\<close> by auto
    hence "(0 < \<mu> (X t\<^sub>0) \<longrightarrow> \<mu> (X t) > 0) \<and> (0 \<le> \<mu> (X t\<^sub>0) \<longrightarrow> 0 \<le> \<mu> (X t))"
      using mvt \<open>t\<^sub>0 \<noteq> t\<close> mult_nonneg_nonneg mult_neg_neg
      by (metis add_nonneg_nonneg diff_gt_0_iff_gt le_add_same_cancel2 
          less_eq_real_def linorder_not_le mult_eq_0_iff)}
  thus "0 < \<mu> (X t\<^sub>0) \<Longrightarrow> 0 < \<mu> (X t)" 
    and "0 \<le> \<mu> (X t\<^sub>0) \<Longrightarrow> 0 \<le> \<mu> (X t)"
    by blast+
qed

lemma 
  fixes \<mu>::"'a::real_normed_vector \<Rightarrow> real"
  assumes "\<And>X t. {t\<^sub>0--t} \<subseteq> U (X t\<^sub>0) \<Longrightarrow> (D X = (\<lambda>\<tau>. f \<tau> (X \<tau>)) on {t\<^sub>0--t}) \<Longrightarrow> \<forall>\<tau>\<in>{t\<^sub>0--t}. G (X \<tau>) \<Longrightarrow> 
    (D (\<lambda>\<tau>. \<mu>(X \<tau>)-\<nu>(X \<tau>)) = (\<lambda>\<tau>. \<mu>'(X \<tau>)-\<nu>'(X \<tau>)) on {t\<^sub>0--t}) \<and> 
    (\<forall>\<tau>\<in>{t\<^sub>0<--<t}. (\<tau> > t\<^sub>0 \<longrightarrow> \<mu>' (X \<tau>) \<ge> \<nu>' (X \<tau>)) \<and> (\<tau> < t\<^sub>0 \<longrightarrow> \<mu>' (X \<tau>) \<le> \<nu>' (X \<tau>)))"
  shows diff_inv_leqI [diff_inv_rules]: "diff_inv (\<lambda>s. \<nu> s \<le> \<mu> s) f U t\<^sub>0 G"
    and diff_inv_lessI [diff_inv_rules]: "diff_inv (\<lambda>s. \<nu> s < \<mu> s) f U t\<^sub>0 G"
  using diff_inv_less0I[where \<mu>="\<lambda>s. \<mu> s - \<nu> s" and \<mu>'="\<lambda>s. \<mu>' s - \<nu>' s"] assms 
  diff_inv_leq0I[where \<mu>="\<lambda>s. \<mu> s - \<nu> s" and \<mu>'="\<lambda>s. \<mu>' s - \<nu>' s"] by auto

lemma diff_inv_nleq_iff:
  fixes \<mu>::"'a::banach \<Rightarrow> real"
  shows "diff_inv (\<lambda>s. \<not> \<nu> s \<le> \<mu> s) f U t\<^sub>0 G \<longleftrightarrow> diff_inv (\<lambda>s. \<nu> s > \<mu> s) f U t\<^sub>0 G"
  unfolding diff_inv_eq approximation_preproc_push_neg(2) by presburger

lemma diff_inv_neqI [diff_inv_rules]:
  fixes \<mu>::"'a::banach \<Rightarrow> real"
  assumes "diff_inv (\<lambda>s. \<nu> s < \<mu> s) f U t\<^sub>0 G"
    and "diff_inv (\<lambda>s. \<nu> s > \<mu> s) f U t\<^sub>0 G"
  shows "diff_inv (\<lambda>s. \<nu> s \<noteq> \<mu> s) f U t\<^sub>0 G"
proof(unfold diff_inv_eq, clarsimp)
  fix s::'a and X::"real \<Rightarrow> 'a" and t::real
  assume "\<nu> s \<noteq> \<mu> s" and Xhyp: "X \<in> Sols f {t\<^sub>0--t} t\<^sub>0 s" 
     and thyp: "{t\<^sub>0--t} \<subseteq> U s" and Ghyp: "\<forall>\<tau>\<in>{t\<^sub>0--t}. G (X \<tau>)"
  hence "\<nu> s < \<mu> s \<or> \<nu> s > \<mu> s"
    by linarith
  moreover have "\<nu> s < \<mu> s \<Longrightarrow> \<nu> (X t) < \<mu> (X t)"
    using assms(1) Xhyp thyp Ghyp 
    unfolding diff_inv_eq by auto
  moreover have "\<nu> s > \<mu> s \<Longrightarrow> \<nu> (X t) > \<mu> (X t)"
    using assms(2) Xhyp thyp Ghyp 
    unfolding diff_inv_eq by auto
  ultimately show "\<nu> (X t) = \<mu> (X t) \<Longrightarrow> False"
    by auto
qed

lemma diff_inv_neqE:
  fixes \<mu>::"'a::banach \<Rightarrow> real"
  assumes Uhyp: "\<And>s. s \<in> S \<Longrightarrow> is_interval (U s)" "\<And>s t. s \<in> S \<Longrightarrow> t \<in> U s \<Longrightarrow> t\<^sub>0 \<le> t"
    and conts: "\<And>X t. (D X = (\<lambda>\<tau>. f \<tau> (X \<tau>)) on {t\<^sub>0--t}) \<Longrightarrow> continuous_on (\<P> X {t\<^sub>0--t}) \<nu>"
      "\<And>X t. (D X = (\<lambda>\<tau>. f \<tau> (X \<tau>)) on {t\<^sub>0--t}) \<Longrightarrow> continuous_on (\<P> X {t\<^sub>0--t}) \<mu>"
    and dI:"diff_inv (\<lambda>s. \<nu> s \<noteq> \<mu> s) f U t\<^sub>0 G"
  shows "diff_inv (\<lambda>s. \<nu> s < \<mu> s) f U t\<^sub>0 G"
proof(unfold diff_inv_eq ivp_sols_def, clarsimp)
  fix X t
  assume xivp: "D X = (\<lambda>\<tau>. f \<tau> (X \<tau>)) on {t\<^sub>0--t}" "\<nu> (X t\<^sub>0) < \<mu> (X t\<^sub>0)"
  assume ivl: "{t\<^sub>0--t} \<subseteq> U (X t\<^sub>0)" and Ghyp: "\<forall>\<tau>\<in>{t\<^sub>0--t}. G (X \<tau>)"
  hence "\<mu> (X t) \<noteq> \<nu> (X t)"
    using dI xivp ivp_solsI[of X f, OF _ _ ends_in_segment(1)[of t\<^sub>0 t]]
    unfolding diff_inv_eq by (metis order_less_irrefl)
  moreover
  {assume ineq2:"\<nu> (X t) > \<mu> (X t)"
    note continuous_on_compose[OF vderiv_on_continuous_on[OF xivp(1)]]
    hence "continuous_on {t\<^sub>0--t} (\<lambda>\<tau>. \<nu> (X \<tau>))" 
      and "continuous_on {t\<^sub>0--t} (\<lambda>\<tau>. \<mu> (X \<tau>))"
      using xivp(1) conts by force+
    then obtain \<tau> where "\<tau> \<in> {t\<^sub>0--t}" "\<mu> (X \<tau>) = \<nu> (X \<tau>)"
      using IVT_two_functions_real_ivl[OF _ _ xivp(2) ineq2] by force
    hence "\<forall>r\<in>{t\<^sub>0--\<tau>}. G (X r)" and "{t\<^sub>0--\<tau>} \<subseteq> U (X t\<^sub>0)"
      using Ghyp ivl closed_segment_closed_segment_subset ivl by blast+ 
    hence "\<mu> (X \<tau>) \<noteq> \<nu> (X \<tau>)"
      using dI xivp ivp_solsI[of X f, OF _ _ ends_in_segment(1)[of t\<^sub>0 \<tau>]] 
      unfolding diff_inv_eq
      by (metis (full_types) closed_segment_commute ends_in_segment(2) \<open>\<tau> \<in> {t\<^sub>0--t}\<close> 
          has_vderiv_on_subset order_less_irrefl subset_closed_segment)
    hence "False"
      using \<open>\<mu> (X \<tau>) = \<nu> (X \<tau>)\<close> by blast}
  ultimately show "\<nu> (X t) < \<mu> (X t)"
    by fastforce
qed

lemma diff_inv_conjI [diff_inv_rules]:
  assumes "diff_inv I\<^sub>1 f U t\<^sub>0 G"
    and "diff_inv I\<^sub>2 f U t\<^sub>0 G"
  shows "diff_inv (\<lambda>s. I\<^sub>1 s \<and> I\<^sub>2 s) f U t\<^sub>0 G"
  using assms unfolding diff_inv_def by auto

lemma diff_inv_disjI [diff_inv_rules]:
  assumes "diff_inv I\<^sub>1 f U t\<^sub>0 G"
    and "diff_inv I\<^sub>2 f U t\<^sub>0 G"
  shows "diff_inv (\<lambda>s. I\<^sub>1 s \<or> I\<^sub>2 s) f U t\<^sub>0 G"
  using assms unfolding diff_inv_def by auto


subsection \<open> Picard-Lindeloef \<close>

text\<open> A locale with the assumptions of Picard-Lindeloef's theorem. It extends 
@{term "ll_on_open_it"} by providing an initial time @{term "t\<^sub>0 \<in> T"}.\<close>

locale picard_lindeloef =
  fixes f::"real \<Rightarrow> ('a::{heine_borel,banach}) \<Rightarrow> 'a" and T::"real set" and S::"'a set" and t\<^sub>0::real
  assumes open_domain: "open T" "open S"
    and interval_time: "is_interval T"
    and init_time: "t\<^sub>0 \<in> T"
    and cont_vec_field: "\<forall>s \<in> S. continuous_on T (\<lambda>t. f t s)"
    and lipschitz_vec_field: "local_lipschitz T S f"
begin

sublocale ll_on_open_it T f S t\<^sub>0
  by (unfold_locales) (auto simp: cont_vec_field lipschitz_vec_field interval_time open_domain) 

lemma ll_on_open: "ll_on_open T f S"
  using local.general.ll_on_open_axioms .

lemmas subintervalI = closed_segment_subset_domain
   and init_time_ex_ivl = existence_ivl_initial_time[OF init_time]
   and flow_at_init[simp] = general.flow_initial_time[OF init_time]
                               
abbreviation "ex_ivl s \<equiv> existence_ivl t\<^sub>0 s"

lemma flow_has_vderiv_on_ex_ivl:
  assumes "s \<in> S"
  shows "D flow t\<^sub>0 s = (\<lambda>t. f t (flow t\<^sub>0 s t)) on ex_ivl s"
  using flow_usolves_ode[OF init_time \<open>s \<in> S\<close>] 
  unfolding usolves_ode_from_def solves_ode_def by blast

lemma flow_funcset_ex_ivl:
  assumes "s \<in> S"
  shows "flow t\<^sub>0 s \<in> ex_ivl s \<rightarrow> S"
  using flow_usolves_ode[OF init_time \<open>s \<in> S\<close>] 
  unfolding usolves_ode_from_def solves_ode_def by blast

lemma flow_in_ivp_sols_ex_ivl:
  assumes "s \<in> S"
  shows "flow t\<^sub>0 s \<in> Sols f (ex_ivl s) t\<^sub>0 s"
  using flow_has_vderiv_on_ex_ivl[OF assms] 
  by (auto intro: ivp_solsI simp: init_time assms)

lemma csols_eq: "csols t\<^sub>0 s = {(X, t). t \<in> T \<and>  X \<in> Sols f {t\<^sub>0--t} t\<^sub>0 s \<and> X \<in> {t\<^sub>0--t} \<rightarrow> S}"
  unfolding ivp_sols_def csols_def solves_ode_def 
  using closed_segment_subset_domain init_time by auto

lemma subset_ex_ivlI:
  "Y\<^sub>1 \<in> {t\<^sub>0--t} \<rightarrow> S \<Longrightarrow> Y\<^sub>1 \<in> Sols f T t\<^sub>0 s \<Longrightarrow> {t\<^sub>0--t} \<subseteq> T \<Longrightarrow> A \<subseteq> {t\<^sub>0--t} \<Longrightarrow> A \<subseteq> ex_ivl s"
  apply(clarsimp simp: existence_ivl_def)
  apply(subgoal_tac "t\<^sub>0 \<in> T", clarsimp simp: csols_eq)
   apply(rule_tac x=Y\<^sub>1 in exI, rule_tac x=t in exI, safe, force)
  by (rule in_ivp_sols_subset[OF ends_in_segment(1)], auto)

lemma unique_solution: \<comment> \<open> proved for a subset of T for general applications \<close>
  assumes "s \<in> S" and "t\<^sub>0 \<in> U" and "t \<in> U" 
    and "is_interval U" and "U \<subseteq> ex_ivl s" 
    and xivp: "D Y\<^sub>1 = (\<lambda>t. f t (Y\<^sub>1 t)) on U" "Y\<^sub>1 t\<^sub>0 = s" "Y\<^sub>1 \<in> U \<rightarrow> S"
    and yivp: "D Y\<^sub>2 = (\<lambda>t. f t (Y\<^sub>2 t)) on U" "Y\<^sub>2 t\<^sub>0 = s" "Y\<^sub>2 \<in> U \<rightarrow> S"
  shows "Y\<^sub>1 t = Y\<^sub>2 t"
proof-
  have "t\<^sub>0 \<in> T"
    using assms existence_ivl_subset by auto
  have key: "(flow t\<^sub>0 s usolves_ode f from t\<^sub>0) (ex_ivl s) S"
    using flow_usolves_ode[OF \<open>t\<^sub>0 \<in> T\<close> \<open>s \<in> S\<close>] .
  hence "\<forall>t\<in>U. Y\<^sub>1 t = flow t\<^sub>0 s t"
    unfolding usolves_ode_from_def solves_ode_def apply safe
    by (erule_tac x=Y\<^sub>1 in allE, erule_tac x=U in allE, auto simp: assms)
  also have "\<forall>t\<in>U. Y\<^sub>2 t = flow t\<^sub>0 s t"
    using key unfolding usolves_ode_from_def solves_ode_def apply safe
    by (erule_tac x=Y\<^sub>2 in allE, erule_tac x=U in allE, auto simp: assms)
  ultimately show "Y\<^sub>1 t = Y\<^sub>2 t"
    using assms by auto
qed

text \<open>Applications of lemma @{text "unique_solution"}: \<close>

lemma unique_solution_closed_ivl:
  assumes xivp: "D X = (\<lambda>t. f t (X t)) on {t\<^sub>0--t}" "X t\<^sub>0 = s" "X \<in> {t\<^sub>0--t} \<rightarrow> S" and "t \<in> T"
    and yivp: "D Y = (\<lambda>t. f t (Y t)) on {t\<^sub>0--t}" "Y t\<^sub>0 = s" "Y \<in> {t\<^sub>0--t} \<rightarrow> S" and "s \<in> S" 
  shows "X t = Y t"
  apply(rule unique_solution[OF \<open>s \<in> S\<close>, of "{t\<^sub>0--t}"], simp_all add: assms)
  apply(unfold existence_ivl_def csols_eq ivp_sols_def, clarsimp)
  using xivp \<open>t \<in> T\<close> by blast

lemma solution_eq_flow:
  assumes xivp: "D X = (\<lambda>t. f t (X t)) on ex_ivl s" "X t\<^sub>0 = s" "X \<in> ex_ivl s \<rightarrow> S" 
    and "t \<in> ex_ivl s" and "s \<in> S" 
  shows "X t = flow t\<^sub>0 s t"
  apply(rule unique_solution[OF \<open>s \<in> S\<close> init_time_ex_ivl \<open>t \<in> ex_ivl s\<close>])
  using flow_has_vderiv_on_ex_ivl flow_funcset_ex_ivl \<open>s \<in> S\<close> by (auto simp: assms)

(*
lemma ivp_unique_solution:
  assumes "s \<in> S" and ivl: "is_interval (U s)" and "U s \<subseteq> T" and "t \<in> U s" 
    and ivp1: "Y\<^sub>1 \<in> Sols f U S t\<^sub>0 s" and ivp2: "Y\<^sub>2 \<in> Sols f U S t\<^sub>0 s"
  shows "Y\<^sub>1 t = Y\<^sub>2 t"
proof(rule unique_solution[OF \<open>s \<in> S\<close>, of "{t\<^sub>0--t}"], simp_all)
  have "t\<^sub>0 \<in> U s"
    using ivp_solsD[OF ivp1] by auto
  hence obs0: "{t\<^sub>0--t} \<subseteq> U s"
    using closed_segment_subset_interval[OF ivl] \<open>t \<in> U s\<close> by blast
  moreover have obs1: "Y\<^sub>1 \<in> Sols f (\<lambda>s. {t\<^sub>0--t}) S t\<^sub>0 s"
    by (rule in_ivp_sols_subset[OF _ calculation(1) ivp1], simp)
  moreover have obs2: "Y\<^sub>2 \<in> Sols f (\<lambda>s. {t\<^sub>0--t}) S t\<^sub>0 s"
    by (rule in_ivp_sols_subset[OF _ calculation(1) ivp2], simp)
  ultimately show "{t\<^sub>0--t} \<subseteq> ex_ivl s"
    apply(unfold existence_ivl_def csols_eq, clarsimp)
    apply(rule_tac x=Y\<^sub>1 in exI, rule_tac x=t in exI)
    using \<open>t \<in> U s\<close> and \<open>U s \<subseteq> T\<close> by force
  show "D Y\<^sub>1 = (\<lambda>t. f t (Y\<^sub>1 t)) on {t\<^sub>0--t}"
    by (rule ivp_solsD[OF in_ivp_sols_subset[OF _ _ ivp1]], simp_all add: obs0)
  show "D Y\<^sub>2 = (\<lambda>t. f t (Y\<^sub>2 t)) on {t\<^sub>0--t}"
    by (rule ivp_solsD[OF in_ivp_sols_subset[OF _ _ ivp2]], simp_all add: obs0)
  show "Y\<^sub>1 t\<^sub>0 = s" and "Y\<^sub>2 t\<^sub>0 = s"
    using ivp_solsD[OF ivp1] ivp_solsD[OF ivp2] by auto
  show "Y\<^sub>1 \<in> {t\<^sub>0--t} \<rightarrow> S" and "Y\<^sub>2 \<in> {t\<^sub>0--t} \<rightarrow> S"
    using ivp_solsD[OF obs1] ivp_solsD[OF obs2] by auto
qed*)

lemma g_orbital_orbit:
  assumes "s \<in> S" and ivl: "is_interval (U s)" and "U s \<subseteq> T"
    and ivp: "Y \<in> Sols f (U s) t\<^sub>0 s"
  shows "g_orbital f G U t\<^sub>0 s = g_orbit G (U s) t\<^sub>0 Y"
proof(rule set_eqI2)
  have eq1: "\<forall>Z \<in> Sols f (U s) t\<^sub>0 s. \<forall>t\<in>U s. Z t = Y t"
    by (clarsimp, rule ivp_unique_solution[OF assms(1,2,3) _ _ ivp], auto)
  have "g_orbital f G U t\<^sub>0 s \<subseteq> g_orbit G (U s) t\<^sub>0 Y"
  proof
    fix x assume "x \<in> g_orbital f G U t\<^sub>0 s"
    then obtain Z and t where z_def: "x = Z t \<and> {t\<^sub>0--t} \<subseteq> U s \<and> (\<forall>\<tau>\<in>{t\<^sub>0--t}. G (Z \<tau>))" 
      and ivp: "Z \<in> Sols f {t\<^sub>0--t} t\<^sub>0 s"
      unfolding g_orbital_eq by auto
    hence "t\<^sub>0 \<in> U s"
      by auto
    hence "\<forall>\<tau>\<in>{t\<^sub>0--t}. Z \<tau> = Y \<tau>"
      using z_def apply clarsimp
      thm ivp[unfolded ivp_sols_def, simplified] unique_solution[OF assms(1)]
      by (rule ivp_unique_solution[OF assms(1,2,3) _ _ ivp], auto)
    thus "x \<in> g_orbit Y G (U s)"
      using z_def eq1 unfolding g_orbit_eq by simp metis
  qed
  moreover have "g_orbit G (U s) t\<^sub>0 Y \<subseteq> g_orbital f G U t\<^sub>0 s"
    apply(unfold g_orbital_eq g_orbit_def ivp_sols_def, clarsimp)
    apply(rule_tac x=t in exI, rule_tac x=Y in exI)
    using ivp_solsD[OF ivp] ivl \<open>t\<^sub>0 \<in> U s\<close> apply auto
  ultimately show ?thesis
    by blast
qed

end

lemma local_lipschitz_add: 
  fixes f1 f2 :: "real \<Rightarrow> 'a::banach \<Rightarrow> 'a"
  assumes "local_lipschitz T S f1"
      and "local_lipschitz T S f2" 
    shows "local_lipschitz T S (\<lambda>t s. f1 t s + f2 t s)"
proof(unfold local_lipschitz_def, clarsimp)
  fix s and t assume "s \<in> S" and "t \<in> T"
  obtain \<epsilon>\<^sub>1 L1 where "\<epsilon>\<^sub>1 > 0" and L1: "\<And>\<tau>. \<tau>\<in>cball t \<epsilon>\<^sub>1 \<inter> T \<Longrightarrow> L1-lipschitz_on (cball s \<epsilon>\<^sub>1 \<inter> S) (f1 \<tau>)"
    using local_lipschitzE[OF assms(1) \<open>t \<in> T\<close> \<open>s \<in> S\<close>] by blast
  obtain \<epsilon>\<^sub>2 L2 where "\<epsilon>\<^sub>2 > 0" and L2: "\<And>\<tau>. \<tau>\<in>cball t \<epsilon>\<^sub>2 \<inter> T \<Longrightarrow> L2-lipschitz_on (cball s \<epsilon>\<^sub>2 \<inter> S) (f2 \<tau>)"
    using local_lipschitzE[OF assms(2) \<open>t \<in> T\<close> \<open>s \<in> S\<close>] by blast
  have ballH: "cball s (min \<epsilon>\<^sub>1 \<epsilon>\<^sub>2) \<inter> S \<subseteq> cball s \<epsilon>\<^sub>1 \<inter> S" "cball s (min \<epsilon>\<^sub>1 \<epsilon>\<^sub>2) \<inter> S \<subseteq> cball s \<epsilon>\<^sub>2 \<inter> S"
    by auto
  have obs1: "\<forall>\<tau>\<in>cball t \<epsilon>\<^sub>1 \<inter> T. L1-lipschitz_on (cball s (min \<epsilon>\<^sub>1 \<epsilon>\<^sub>2) \<inter> S) (f1 \<tau>)"
    using lipschitz_on_subset[OF L1 ballH(1)] by blast
  also have obs2: "\<forall>\<tau>\<in>cball t \<epsilon>\<^sub>2 \<inter> T. L2-lipschitz_on (cball s (min \<epsilon>\<^sub>1 \<epsilon>\<^sub>2) \<inter> S) (f2 \<tau>)"
    using lipschitz_on_subset[OF L2 ballH(2)] by blast
  ultimately have "\<forall>\<tau>\<in>cball t (min \<epsilon>\<^sub>1 \<epsilon>\<^sub>2) \<inter> T. 
    (L1 + L2)-lipschitz_on (cball s (min \<epsilon>\<^sub>1 \<epsilon>\<^sub>2) \<inter> S) (\<lambda>s. f1 \<tau> s + f2 \<tau> s)"
    using lipschitz_on_add by fastforce
  thus "\<exists>u>0. \<exists>L. \<forall>t\<in>cball t u \<inter> T. L-lipschitz_on (cball s u \<inter> S) (\<lambda>s. f1 t s + f2 t s)"
    apply(rule_tac x="min \<epsilon>\<^sub>1 \<epsilon>\<^sub>2" in exI)
    using \<open>\<epsilon>\<^sub>1 > 0\<close> \<open>\<epsilon>\<^sub>2 > 0\<close> by force
qed

lemma picard_lindeloef_add: "picard_lindeloef f1 T S t\<^sub>0 \<Longrightarrow> picard_lindeloef f2 T S t\<^sub>0 \<Longrightarrow> 
  picard_lindeloef (\<lambda>t s. f1 t s + f2 t s) T S t\<^sub>0"
  unfolding picard_lindeloef_def apply(clarsimp, rule conjI)
  using continuous_on_add apply fastforce
  using local_lipschitz_add by blast

lemma picard_lindeloef_constant: "picard_lindeloef (\<lambda>t s. c) UNIV UNIV t\<^sub>0"
  apply(unfold_locales, simp_all add: local_lipschitz_def lipschitz_on_def, clarsimp)
  by (rule_tac x=1 in exI, clarsimp, rule_tac x="1/2" in exI, simp)


subsection \<open> Flows for ODEs \<close>

text\<open> A locale designed for verification of hybrid systems. The user can select the interval 
of existence and the defining flow equation via the variables @{term "T"} and @{term "\<phi>"}.\<close>

locale local_flow = picard_lindeloef "(\<lambda> t. f)" T S 0 
  for f::"'a::{heine_borel,banach} \<Rightarrow> 'a" and T S L +
  fixes \<phi> :: "real \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes ivp:
    "\<And> t s. t \<in> T \<Longrightarrow> s \<in> S \<Longrightarrow> D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on {0--t}"
    "\<And> s. s \<in> S \<Longrightarrow> \<phi> 0 s = s"
    "\<And> t s. t \<in> T \<Longrightarrow> s \<in> S \<Longrightarrow> (\<lambda>t. \<phi> t s) \<in> {0--t} \<rightarrow> S"
begin

lemma in_ivp_sols_ivl: 
  assumes "t \<in> T" "s \<in> S"
  shows "(\<lambda>t. \<phi> t s) \<in> Sols (\<lambda>t. f) {0--t} 0 s"
  apply(rule ivp_solsI)
  using ivp assms by auto

lemma eq_solution_ivl:
  assumes xivp: "D X = (\<lambda>t. f (X t)) on {0--t}" "X 0 = s" "X \<in> {0--t} \<rightarrow> S" 
    and indom: "t \<in> T" "s \<in> S"
  shows "X t = \<phi> t s"
  apply(rule unique_solution_closed_ivl[OF xivp \<open>t \<in> T\<close>])
  using \<open>s \<in> S\<close> ivp indom by auto

lemma ex_ivl_eq:
  assumes "s \<in> S"
  shows "ex_ivl s = T"
  using existence_ivl_subset[of s] apply safe
  unfolding existence_ivl_def csols_eq
  using in_ivp_sols_ivl[OF _ assms] ivp(3) apply auto
  sorry

lemma has_derivative_on_open1: 
  assumes  "t > 0" "t \<in> T" "s \<in> S"
  obtains B where "t \<in> B" and "open B" and "B \<subseteq> T"
    and "D (\<lambda>\<tau>. \<phi> \<tau> s) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R f (\<phi> t s)) at t within B" 
proof-
  obtain r::real where rHyp: "r > 0" "ball t r \<subseteq> T"
    using open_contains_ball_eq open_domain(1) \<open>t \<in> T\<close> by blast
  moreover have "t + r/2 > 0"
    using \<open>r > 0\<close> \<open>t > 0\<close> by auto
  moreover have "{0--t} \<subseteq> T" 
    using subintervalI[OF init_time \<open>t \<in> T\<close>] .
  ultimately have subs: "{0<--<t + r/2} \<subseteq> T"
    unfolding abs_le_eq abs_le_eq real_ivl_eqs[OF \<open>t > 0\<close>] real_ivl_eqs[OF \<open>t + r/2 > 0\<close>] 
    by clarify (case_tac "t < x", simp_all add: cball_def ball_def dist_norm subset_eq field_simps)
  have "t + r/2 \<in> T"
    using rHyp unfolding real_ivl_eqs[OF rHyp(1)] by (simp add: subset_eq)
  hence "{0--t + r/2} \<subseteq> T"
    using subintervalI[OF init_time] by blast
  hence "(D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on {0--(t + r/2)})"
    using ivp(1)[OF _ \<open>s \<in> S\<close>] by auto
  hence vderiv: "(D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on {0<--<t + r/2})"
    apply(rule has_vderiv_on_subset)
    unfolding real_ivl_eqs[OF \<open>t + r/2 > 0\<close>] by auto
  have "t \<in> {0<--<t + r/2}"
    unfolding real_ivl_eqs[OF \<open>t + r/2 > 0\<close>] using rHyp \<open>t > 0\<close> by simp
  moreover have "D (\<lambda>\<tau>. \<phi> \<tau> s) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R f (\<phi> t s)) (at t within {0<--<t + r/2})"
    using vderiv calculation unfolding has_vderiv_on_def has_vector_derivative_def by blast
  moreover have "open {0<--<t + r/2}"
    unfolding real_ivl_eqs[OF \<open>t + r/2 > 0\<close>] by simp
  ultimately show ?thesis
    using subs that by blast
qed

lemma has_derivative_on_open2: 
  assumes "t < 0" "t \<in> T" "s \<in> S"
  obtains B where "t \<in> B" and "open B" and "B \<subseteq> T"
    and "D (\<lambda>\<tau>. \<phi> \<tau> s) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R f (\<phi> t s)) at t within B" 
proof-
  obtain r::real where rHyp: "r > 0" "ball t r \<subseteq> T"
    using open_contains_ball_eq open_domain(1) \<open>t \<in> T\<close> by blast
  moreover have "t - r/2 < 0"
    using \<open>r > 0\<close> \<open>t < 0\<close> by auto
  moreover have "{0--t} \<subseteq> T" 
    using subintervalI[OF init_time \<open>t \<in> T\<close>] .
  ultimately have subs: "{0<--<t - r/2} \<subseteq> T"
    unfolding open_segment_eq_real_ivl closed_segment_eq_real_ivl
      real_ivl_eqs[OF rHyp(1)] by(auto simp: subset_eq)
  have "t - r/2 \<in> T"
    using rHyp unfolding real_ivl_eqs by (simp add: subset_eq)
  hence "{0--t - r/2} \<subseteq> T"
    using subintervalI[OF init_time] by blast
  hence "(D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on {0--(t - r/2)})"
    using ivp(1)[OF _ \<open>s \<in> S\<close>] by auto
  hence vderiv: "(D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on {0<--<t - r/2})"
    apply(rule has_vderiv_on_subset)
    unfolding open_segment_eq_real_ivl closed_segment_eq_real_ivl by auto
  have "t \<in> {0<--<t - r/2}"
    unfolding open_segment_eq_real_ivl using rHyp \<open>t < 0\<close> by simp
  moreover have "D (\<lambda>\<tau>. \<phi> \<tau> s) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R f (\<phi> t s)) (at t within {0<--<t - r/2})"
    using vderiv calculation unfolding has_vderiv_on_def has_vector_derivative_def by blast
  moreover have "open {0<--<t - r/2}"
    unfolding open_segment_eq_real_ivl by simp
  ultimately show ?thesis
    using subs that by blast
qed

lemma has_derivative_on_open3: 
  assumes "s \<in> S"
  obtains B where "0 \<in> B" and "open B" and "B \<subseteq> T"
    and "D (\<lambda>\<tau>. \<phi> \<tau> s) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R f (\<phi> 0 s)) at 0 within B" 
proof-
  obtain r::real where rHyp: "r > 0" "ball 0 r \<subseteq> T"
    using open_contains_ball_eq open_domain(1) init_time by blast
  hence "r/2 \<in> T" "-r/2 \<in> T" "r/2 > 0"
    unfolding real_ivl_eqs by auto
  hence subs: "{0--r/2} \<subseteq> T" "{0--(-r/2)} \<subseteq> T"
    using subintervalI[OF init_time] by auto
  hence "(D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on {0--r/2})"
    "(D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on {0--(-r/2)})"
    using ivp(1)[OF _ \<open>s \<in> S\<close>] by auto
  also have "{0--r/2} = {0--r/2} \<union> closure {0--r/2} \<inter> closure {0--(-r/2)}"
    "{0--(-r/2)} = {0--(-r/2)} \<union> closure {0--r/2} \<inter> closure {0--(-r/2)}"
    unfolding closed_segment_eq_real_ivl \<open>r/2 > 0\<close> by auto
  ultimately have vderivs:
    "(D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on {0--r/2} \<union> closure {0--r/2} \<inter> closure {0--(-r/2)})"
    "(D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on {0--(-r/2)} \<union> closure {0--r/2} \<inter> closure {0--(-r/2)})"
    unfolding closed_segment_eq_real_ivl \<open>r/2 > 0\<close> by auto
  have obs: "0 \<in> {-r/2<--<r/2}"
    unfolding open_segment_eq_real_ivl using \<open>r/2 > 0\<close> by auto
  have union: "{-r/2--r/2} = {0--r/2} \<union> {0--(-r/2)}"
    unfolding closed_segment_eq_real_ivl by auto
  hence "(D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on {-r/2--r/2})"
    using has_vderiv_on_union[OF vderivs] by simp
  hence "(D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on {-r/2<--<r/2})"
    using has_vderiv_on_subset[OF _ segment_open_subset_closed[of "-r/2" "r/2"]] by auto
  hence "D (\<lambda>\<tau>. \<phi> \<tau> s) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R f (\<phi> 0 s)) (at 0 within {-r/2<--<r/2})"
    unfolding has_vderiv_on_def has_vector_derivative_def using obs by blast
  moreover have "open {-r/2<--<r/2}"
    unfolding open_segment_eq_real_ivl by simp
  moreover have "{-r/2<--<r/2} \<subseteq> T"
    using subs union segment_open_subset_closed by blast 
  ultimately show ?thesis
    using obs that by blast
qed

lemma has_derivative_on_open: 
  assumes "t \<in> T" "s \<in> S"
  obtains B where "t \<in> B" and "open B" and "B \<subseteq> T"
    and "D (\<lambda>\<tau>. \<phi> \<tau> s) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R f (\<phi> t s)) at t within B" 
  apply(subgoal_tac "t < 0 \<or> t = 0 \<or> t > 0")
  using has_derivative_on_open1[OF _ assms] has_derivative_on_open2[OF _ assms]
    has_derivative_on_open3[OF \<open>s \<in> S\<close>] by blast force

lemma in_domain:
  assumes "s \<in> S"
  shows "(\<lambda>t. \<phi> t s) \<in> T \<rightarrow> S"
  using ivp(3)[OF _ assms] by blast

lemma has_vderiv_on_domain:
  assumes "s \<in> S"
  shows "D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on T"
proof(unfold has_vderiv_on_def has_vector_derivative_def, clarsimp)
  fix t assume "t \<in> T"
  then obtain B where "t \<in> B" and "open B" and "B \<subseteq> T" 
    and Dhyp: "D (\<lambda>t. \<phi> t s) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R f (\<phi> t s)) at t within B"
    using assms has_derivative_on_open[OF \<open>t \<in> T\<close>] by blast
  hence "t \<in> interior B"
    using interior_eq by auto
  thus "D (\<lambda>t. \<phi> t s) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R f (\<phi> t s)) at t within T"
    using has_derivative_at_within_mono[OF _ \<open>B \<subseteq> T\<close> Dhyp] by blast
qed

lemma in_ivp_sols: 
  assumes "s \<in> S" and "0 \<in> U s" and "U s \<subseteq> T"
  shows "(\<lambda>t. \<phi> t s) \<in> Sols (\<lambda>t. f) U S 0 s"
  apply(rule in_ivp_sols_subset[OF _ _ ivp_solsI, of _ _ _ "\<lambda>s. T"])
  using  ivp(2)[OF \<open>s \<in> S\<close>] has_vderiv_on_domain[OF \<open>s \<in> S\<close>] 
    in_domain[OF \<open>s \<in> S\<close>] assms by auto

lemma eq_solution:
  assumes "s \<in> S" and "is_interval (U s)" and "U s \<subseteq> T" and "t \<in> U s"
    and xivp: "X \<in> Sols (\<lambda>t. f) U S 0 s"
  shows "X t = \<phi> t s"
  apply(rule ivp_unique_solution[OF assms], rule in_ivp_sols)
  by (simp_all add: ivp_solsD(4)[OF xivp] assms)

lemma ivp_sols_collapse: 
  assumes "T = UNIV" and "s \<in> S"
  shows "Sols (\<lambda>t. f) (\<lambda>s. T) S 0 s = {(\<lambda>t. \<phi> t s)}"
  apply (safe, simp_all add: fun_eq_iff, clarsimp)
   apply(rule eq_solution[of _ "\<lambda>s. T"]; simp add: assms)
  by (rule in_ivp_sols; simp add: assms)

lemma additive_in_ivp_sols:
  assumes "s \<in> S" and "\<P> (\<lambda>\<tau>. \<tau> + t) T \<subseteq> T"
  shows "(\<lambda>\<tau>. \<phi> (\<tau> + t) s) \<in> Sols (\<lambda>t. f) (\<lambda>s. T) S 0 (\<phi> (0 + t) s)"
  apply(rule ivp_solsI[OF vderiv_on_composeI])
       apply(rule has_vderiv_on_subset[OF has_vderiv_on_domain])
  using in_domain assms init_time by (auto intro!: poly_derivatives)

lemma is_monoid_action:
  assumes "s \<in> S" and "T = UNIV"
  shows "\<phi> 0 s = s" and "\<phi> (t\<^sub>1 + t\<^sub>2) s = \<phi> t\<^sub>1 (\<phi> t\<^sub>2 s)"
proof-
  show "\<phi> 0 s = s"
    using ivp assms by simp
  have "\<phi> (0 + t\<^sub>2) s = \<phi> t\<^sub>2 s" 
    by simp
  also have "\<phi> (0 + t\<^sub>2) s \<in> S"
    using in_domain assms by auto
  ultimately show "\<phi> (t\<^sub>1 + t\<^sub>2) s = \<phi> t\<^sub>1 (\<phi> t\<^sub>2 s)"
    using eq_solution[OF _ _ _ _ additive_in_ivp_sols] assms by auto
qed

lemma g_orbital_collapses: 
  assumes "s \<in> S" and "is_interval (U s)" and "U s \<subseteq> T" and "0 \<in> U s"
  shows "g_orbital (\<lambda>t. f) G U S 0 s = {\<phi> t s| t. t \<in> U s \<and> (\<forall>\<tau>\<in>down (U s) t. G (\<phi> \<tau> s))}"
  apply (subst g_orbital_orbit[of _ _ "\<lambda>t. \<phi> t s"], simp_all add: assms g_orbit_eq)
  by (rule in_ivp_sols, simp_all add: assms)

definition orbit :: "'a \<Rightarrow> 'a set" ("\<gamma>\<^sup>\<phi>")
  where "\<gamma>\<^sup>\<phi> s = g_orbital (\<lambda>t. f) (\<lambda>s. True) (\<lambda>s. T) S 0 s"

lemma orbit_eq: 
  assumes "s \<in> S"
  shows "\<gamma>\<^sup>\<phi> s = {\<phi> t s| t. t \<in> T}"
  apply(unfold orbit_def, subst g_orbital_collapses)
  by (simp_all add: assms init_time interval_time)

lemma true_g_orbit_eq:
  assumes "s \<in> S"
  shows "g_orbit (\<lambda>t. \<phi> t s) (\<lambda>s. True) T = \<gamma>\<^sup>\<phi> s"
  unfolding g_orbit_eq orbit_eq[OF assms] by simp

end

lemma line_is_local_flow: 
  "0 \<in> T \<Longrightarrow> is_interval T \<Longrightarrow> open T \<Longrightarrow> local_flow (\<lambda> s. c) T UNIV (\<lambda> t s. s + t *\<^sub>R c)"
  apply(unfold_locales, simp_all add: local_lipschitz_def lipschitz_on_def, clarsimp)
   apply(rule_tac x=1 in exI, clarsimp, rule_tac x="1/2" in exI, simp)
  apply(rule_tac f'1="\<lambda> s. 0" and g'1="\<lambda> s. c" in has_vderiv_on_add[THEN has_vderiv_on_eq_rhs])
    apply(rule derivative_intros, simp)+
  by simp_all


subsection \<open> Verification components \<close>

type_synonym 'a pred = "'a \<Rightarrow> bool"
type_synonym 's prog = "'s \<Rightarrow> 's set"

definition fbox :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'b pred \<Rightarrow> 'a pred" ("|_] _" [61,81] 82)
  where "|F] P = (\<lambda>s. (\<forall>s'. s' \<in> F s \<longrightarrow> P s'))"

lemma fbox_iso: "P \<le> Q \<Longrightarrow> |F] P \<le> |F] Q"
  unfolding fbox_def by auto

lemma fbox_anti: "\<forall>s. F\<^sub>1 s \<subseteq> F\<^sub>2 s \<Longrightarrow> |F\<^sub>2] P \<le> |F\<^sub>1] P"
  unfolding fbox_def by auto

lemma fbox_invariants: 
  assumes "I \<le> |F] I" and "J \<le> |F] J"
  shows "(\<lambda>s. I s \<and> J s) \<le> |F] (\<lambda>s. I s \<and> J s)"
    and "(\<lambda>s. I s \<or> J s) \<le> |F] (\<lambda>s. I s \<or> J s)"
  using assms unfolding fbox_def by auto

subsection \<open> Verification of hybrid programs \<close>

text \<open> Verification by providing evolution \<close>

definition g_evol :: "(('a::real_vector) \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b pred \<Rightarrow> ('b \<Rightarrow> 'a set) \<Rightarrow> ('b \<Rightarrow> 'b set)" ("EVOL")
  where "EVOL \<phi> G U = (\<lambda>s. g_orbit G (U s) 0 (\<lambda>t. \<phi> t s))"

lemma fbox_g_evol[simp]: 
  fixes \<phi> :: "('a::real_vector) \<Rightarrow> 'b \<Rightarrow> 'b"
  shows "|EVOL \<phi> G U] Q = (\<lambda>s. (\<forall>t\<in>U s. (\<forall>\<tau>\<in>{0--t}. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s)))"
  unfolding g_evol_def g_orbit_def fbox_def by auto

text \<open> Verification by providing solutions \<close>

lemma fbox_g_orbital: "|g_orbital f G U t\<^sub>0] Q = 
  (\<lambda>s. \<forall>t. \<forall>X\<in>Sols f {t\<^sub>0--t} t\<^sub>0 s. {t\<^sub>0--t} \<subseteq> U s \<longrightarrow> (\<forall>\<tau>\<in>{t\<^sub>0--t}. G (X \<tau>)) \<longrightarrow> Q (X t))"
  unfolding fbox_def g_orbital_eq by (auto simp: fun_eq_iff)

lemma fbox_g_orbital_ivl: "\<forall>s. is_interval (U s) \<and> t\<^sub>0 \<in> U s \<Longrightarrow> |g_orbital f G U t\<^sub>0] Q = 
  (\<lambda>s. \<forall>t\<in>U s. \<forall>X\<in>Sols f {t\<^sub>0--t} t\<^sub>0 s. (\<forall>\<tau>\<in>{t\<^sub>0--t}. G (X \<tau>)) \<longrightarrow> Q (X t))"
  unfolding fbox_g_orbital apply(clarsimp simp: fun_eq_iff)
  using closed_segment_subset_interval
  by (smt (verit, best) ends_in_segment(2) ivp_solsD(2) subset_iff)

end