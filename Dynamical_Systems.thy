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


subsection \<open> Differential Invariants \<close>

definition diff_invariant :: "('a \<Rightarrow> bool) \<Rightarrow> (real \<Rightarrow> ('a::real_normed_vector) \<Rightarrow> 'a) \<Rightarrow> 
  ('a \<Rightarrow> real set) \<Rightarrow> real \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" 
  where "diff_invariant I f U t\<^sub>0 G \<equiv> (\<Union> \<circ> (\<P> (g_orbital f G U t\<^sub>0))) {s. I s} \<subseteq> {s. I s}"

lemma diff_invariant_eq: "diff_invariant I f U t\<^sub>0 G = 
  (\<forall>s. I s \<longrightarrow> (\<forall>t. \<forall>X\<in>Sols f {t\<^sub>0--t} t\<^sub>0 s. {t\<^sub>0--t} \<subseteq> U s \<longrightarrow> (\<forall>\<tau>\<in>{t\<^sub>0--t}. G (X \<tau>)) \<longrightarrow> I (X t)))"
  unfolding diff_invariant_def g_orbital_eq image_le_pred by auto

lemma diff_inv_eq_inv_set:
  "diff_invariant I f U t\<^sub>0 G = (\<forall>s. I s \<longrightarrow> (g_orbital f G U t\<^sub>0 s) \<subseteq> {s. I s})"
  unfolding diff_invariant_eq g_orbital_eq image_le_pred by auto

lemma "diff_invariant I f U t\<^sub>0 (\<lambda>s. True) \<Longrightarrow> diff_invariant I f U t\<^sub>0 G"
  unfolding diff_invariant_eq by auto

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

named_theorems diff_invariant_rules "rules for certifying differential invariants"

lemma diff_invariant_eq_zero:
  fixes \<mu>::"'a::real_normed_vector \<Rightarrow> 'b::real_inner"
  assumes "\<And>X t. {t\<^sub>0--t} \<subseteq> U (X t\<^sub>0) \<Longrightarrow> (D X = (\<lambda>\<tau>. f \<tau> (X \<tau>)) on {t\<^sub>0--t}) \<Longrightarrow> \<forall>\<tau>\<in>{t\<^sub>0--t}. G (X \<tau>) \<Longrightarrow> 
    D (\<lambda>\<tau>. \<mu> (X \<tau>)) = (\<lambda>\<tau>. \<tau> *\<^sub>R 0) on {t\<^sub>0--t}"
  shows "diff_invariant (\<lambda>s. \<mu> s = 0) f U t\<^sub>0 G"
proof(clarsimp simp: diff_invariant_eq ivp_sols_def)
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

lemma diff_invariant_eq_rule [diff_invariant_rules]:
  fixes \<mu>::"'a::real_normed_vector \<Rightarrow> 'b::real_inner"
  assumes "\<And>X t. {t\<^sub>0--t} \<subseteq> U (X t\<^sub>0) \<Longrightarrow> (D X = (\<lambda>\<tau>. f \<tau> (X \<tau>)) on {t\<^sub>0--t}) \<Longrightarrow> \<forall>\<tau>\<in>{t\<^sub>0--t}. G (X \<tau>) \<Longrightarrow> 
    D (\<lambda>\<tau>. \<mu> (X \<tau>) - \<nu> (X \<tau>)) = (\<lambda>\<tau>. \<tau> *\<^sub>R 0) on {t\<^sub>0--t}"
  shows "diff_invariant (\<lambda>s. \<mu> s = \<nu> s) f U t\<^sub>0 G"
  using diff_invariant_eq_zero[where \<mu>="\<lambda>s. \<mu> s - \<nu> s"] assms by auto

text \<open> can this be generalised to @{term "\<mu>::'a::real_normed_vector \<Rightarrow> 'b::real_inner"}? \<close>
lemma diff_invariant_leq_rule [diff_invariant_rules]:
  fixes \<mu>::"'a::real_normed_vector \<Rightarrow> real"
  assumes "\<And>X t. {t\<^sub>0--t} \<subseteq> U (X t\<^sub>0) \<Longrightarrow> (D X = (\<lambda>\<tau>. f \<tau> (X \<tau>)) on {t\<^sub>0--t}) \<Longrightarrow> \<forall>\<tau>\<in>{t\<^sub>0--t}. G (X \<tau>) \<Longrightarrow> 
    D (\<lambda>\<tau>. \<mu> (X \<tau>)) = (\<lambda>\<tau>. \<mu>' (X \<tau>)) on {t\<^sub>0--t}"
  shows "diff_invariant (\<lambda>s. 0 < \<mu> s) f U t\<^sub>0 G"
proof(clarsimp simp: diff_invariant_eq ivp_sols_def)
  fix X t
  assume xivp: "D X = (\<lambda>\<tau>. f \<tau> (X \<tau>)) on {t\<^sub>0--t}" "0 < \<mu> (X t\<^sub>0)"
    and "\<forall>\<tau>\<in>{t\<^sub>0--t}. G (X \<tau>)" and "{t\<^sub>0--t} \<subseteq> U (X t\<^sub>0)"
  hence key: "D (\<lambda>\<tau>. \<mu> (X \<tau>)) = (\<lambda>\<tau>. \<mu>' (X \<tau>)) on {t\<^sub>0--t}"
    using assms by auto
  hence d_open: "\<And>\<tau>. t\<^sub>0 \<le> \<tau> \<Longrightarrow> \<tau> \<le> t \<Longrightarrow> D (\<lambda>\<tau>. \<mu> (X \<tau>)) \<mapsto> (\<lambda>t. t *\<^sub>R (\<mu>' (X \<tau>))) (at \<tau> within {t\<^sub>0--t})"
    unfolding has_vderiv_on_iff by (auto simp: closed_segment_eq_real_ivl)
  {assume "t\<^sub>0 \<noteq> t"
    then obtain \<tau> where "\<parallel>\<mu> (X t) - \<mu> (X t\<^sub>0)\<parallel> \<le> \<parallel>\<bar>t - t\<^sub>0\<bar> *\<^sub>R \<mu>' (X \<tau>)\<parallel>" and "\<tau> \<in> {t\<^sub>0<--<t}"
      using mvt_ivl_general[OF _ vderiv_on_continuous_on[OF key] d_open] by auto
    note mvt_very_simple[of t\<^sub>0 t "\<lambda>t. \<mu> (X t)" "\<lambda>\<tau> t. t *\<^sub>R \<mu>' (X \<tau>)"]
  }
  show "0 < \<mu> (X t)"
    sorry
qed

lemma diff_invariant_leq_rule [diff_invariant_rules]:
  fixes \<mu>::"'a::banach \<Rightarrow> real"
  assumes Gg: "\<And>X t. (D X = (\<lambda>\<tau>. f \<tau> (X \<tau>)) on {t\<^sub>0--t}) \<Longrightarrow> (\<forall>\<tau>\<in>U(X t\<^sub>0). \<tau> > t\<^sub>0 \<longrightarrow> G (X \<tau>) \<longrightarrow> \<mu>' (X \<tau>) \<ge> \<nu>' (X \<tau>))"
    and Gl: "\<And>X. (D X = (\<lambda>\<tau>. f \<tau> (X \<tau>)) on U(X t\<^sub>0)) \<Longrightarrow> (\<forall>\<tau>\<in>U(X t\<^sub>0). \<tau> < t\<^sub>0 \<longrightarrow> \<mu>' (X \<tau>) \<le> \<nu>' (X \<tau>))"
    and dX: "\<And>X. (D X = (\<lambda>\<tau>. f \<tau> (X \<tau>)) on U(X t\<^sub>0)) \<Longrightarrow> D (\<lambda>\<tau>. \<mu>(X \<tau>)-\<nu>(X \<tau>)) = (\<lambda>\<tau>. \<mu>'(X \<tau>)-\<nu>'(X \<tau>)) on U(X t\<^sub>0)"
  shows "diff_invariant (\<lambda>s. \<nu> s \<le> \<mu> s) f U t\<^sub>0 G"
proof(simp_all add: diff_invariant_eq ivp_sols_def, safe)
  fix X t assume Ghyp: "\<forall>\<tau>. \<tau> \<in> U (X t\<^sub>0) \<and> \<tau> \<le> t \<longrightarrow> G (X \<tau>)"
  assume xivp: "D X = (\<lambda>x. f x (X x)) on U (X t\<^sub>0)" "\<nu> (X t\<^sub>0) \<le> \<mu> (X t\<^sub>0)" "X \<in> U (X t\<^sub>0) \<rightarrow> S"
  assume tHyp: "t \<in> U (X t\<^sub>0)" and t0Hyp: "t\<^sub>0 \<in> U (X t\<^sub>0)" 
  hence obs1: "{t\<^sub>0--t} \<subseteq> U (X t\<^sub>0)" "{t\<^sub>0<--<t} \<subseteq> U (X t\<^sub>0)"
    using closed_segment_subset_interval[OF Uhyp t0Hyp tHyp] xivp(3) segment_open_subset_closed
    by (force, metis PiE \<open>X t\<^sub>0 \<in> S \<Longrightarrow> {t\<^sub>0--t} \<subseteq> U (X t\<^sub>0)\<close> dual_order.trans)
  hence obs2: "D (\<lambda>\<tau>. \<mu> (X \<tau>) - \<nu> (X \<tau>)) = (\<lambda>\<tau>. \<mu>' (X \<tau>) - \<nu>' (X \<tau>)) on {t\<^sub>0--t}"
    using has_vderiv_on_subset[OF dX[OF xivp(1)]] by auto
  {assume "t \<noteq> t\<^sub>0"
    then obtain r where rHyp: "r \<in> {t\<^sub>0<--<t}" 
      and "(\<mu>(X t)-\<nu>(X t)) - (\<mu>(X t\<^sub>0)-\<nu>(X t\<^sub>0)) = (\<lambda>\<tau>. \<tau>*(\<mu>'(X r)-\<nu>'(X r))) (t - t\<^sub>0)"
      using mvt_simple_closed_segmentE obs2 by blast
    hence mvt: "\<mu>(X t)-\<nu>(X t) = (t - t\<^sub>0)*(\<mu>'(X r)-\<nu>'(X r)) + (\<mu>(X t\<^sub>0)-\<nu>(X t\<^sub>0))"
      by force
    have primed: "\<And>\<tau>. \<tau> \<in> U (X t\<^sub>0) \<Longrightarrow> \<tau> > t\<^sub>0 \<Longrightarrow> G (X \<tau>) \<Longrightarrow> \<mu>' (X \<tau>) \<ge> \<nu>' (X \<tau>)" 
      "\<And>\<tau>. \<tau> \<in> U (X t\<^sub>0) \<Longrightarrow> \<tau> < t\<^sub>0 \<Longrightarrow> \<mu>' (X \<tau>) \<le> \<nu>' (X \<tau>)"
      using Gg[OF xivp(1)] Gl[OF xivp(1)] by auto
    have "t > t\<^sub>0 \<Longrightarrow> r > t\<^sub>0 \<and> G (X r)" "\<not> t\<^sub>0 \<le> t \<Longrightarrow> r < t\<^sub>0" "r \<in> U (X t\<^sub>0)"
      using \<open>r \<in> {t\<^sub>0<--<t}\<close> obs1 Ghyp
      unfolding open_segment_eq_real_ivl closed_segment_eq_real_ivl by auto
    moreover have "r > t\<^sub>0 \<Longrightarrow> G (X r) \<Longrightarrow> (\<mu>'(X r)- \<nu>'(X r)) \<ge> 0" "r < t\<^sub>0 \<Longrightarrow> (\<mu>'(X r)-\<nu>'(X r)) \<le> 0"
      using primed(1,2)[OF \<open>r \<in> U (X t\<^sub>0)\<close>] by auto
    ultimately have "(t - t\<^sub>0) * (\<mu>'(X r)-\<nu>'(X r)) \<ge> 0"
      by (case_tac "t \<ge> t\<^sub>0", force, auto simp: split_mult_pos_le)
    hence "(t - t\<^sub>0) * (\<mu>'(X r)-\<nu>'(X r)) + (\<mu>(X t\<^sub>0)-\<nu>(X t\<^sub>0)) \<ge> 0"
      using xivp(2) by auto
    hence "\<nu> (X t) \<le> \<mu> (X t)"
      using mvt by simp}
  thus "\<nu> (X t) \<le> \<mu> (X t)"
    using xivp by blast
qed

lemma diff_invariant_less_rule [diff_invariant_rules]:
  fixes \<mu>::"'a::banach \<Rightarrow> real"
  assumes Uhyp: "\<And>s. s \<in> S \<Longrightarrow> is_interval (U s)"
    and Gg: "\<And>X. (D X = (\<lambda>\<tau>. f \<tau> (X \<tau>)) on U(X t\<^sub>0)) \<Longrightarrow> (\<forall>\<tau>\<in>U(X t\<^sub>0). \<tau> > t\<^sub>0 \<longrightarrow> G (X \<tau>) \<longrightarrow> \<mu>' (X \<tau>) \<ge> \<nu>' (X \<tau>))"
    and Gl: "\<And>X. (D X = (\<lambda>\<tau>. f \<tau> (X \<tau>)) on U(X t\<^sub>0)) \<Longrightarrow> (\<forall>\<tau>\<in>U(X t\<^sub>0). \<tau> < t\<^sub>0 \<longrightarrow> \<mu>' (X \<tau>) \<le> \<nu>' (X \<tau>))"
    and dX: "\<And>X. (D X = (\<lambda>\<tau>. f \<tau> (X \<tau>)) on U(X t\<^sub>0)) \<Longrightarrow> D (\<lambda>\<tau>. \<mu>(X \<tau>)-\<nu>(X \<tau>)) = (\<lambda>\<tau>. \<mu>'(X \<tau>)-\<nu>'(X \<tau>)) on U(X t\<^sub>0)"
  shows "diff_invariant (\<lambda>s. \<nu> s < \<mu> s) f U S t\<^sub>0 G"
proof(simp_all add: diff_invariant_eq ivp_sols_def, safe)
  fix X t assume Ghyp: "\<forall>\<tau>. \<tau> \<in> U (X t\<^sub>0) \<and> \<tau> \<le> t \<longrightarrow> G (X \<tau>)"
  assume xivp: "D X = (\<lambda>x. f x (X x)) on U (X t\<^sub>0)" "\<nu> (X t\<^sub>0) < \<mu> (X t\<^sub>0)" "X \<in> U (X t\<^sub>0) \<rightarrow> S"
  assume tHyp: "t \<in> U (X t\<^sub>0)" and t0Hyp: "t\<^sub>0 \<in> U (X t\<^sub>0)" 
  hence obs1: "{t\<^sub>0--t} \<subseteq> U (X t\<^sub>0)" "{t\<^sub>0<--<t} \<subseteq> U (X t\<^sub>0)"
    using closed_segment_subset_interval[OF Uhyp t0Hyp tHyp] xivp(3) segment_open_subset_closed
    by (force, metis PiE \<open>X t\<^sub>0 \<in> S \<Longrightarrow> {t\<^sub>0--t} \<subseteq> U (X t\<^sub>0)\<close> dual_order.trans)
  hence obs2: "D (\<lambda>\<tau>. \<mu> (X \<tau>) - \<nu> (X \<tau>)) = (\<lambda>\<tau>. \<mu>' (X \<tau>) - \<nu>' (X \<tau>)) on {t\<^sub>0--t}"
    using has_vderiv_on_subset[OF dX[OF xivp(1)]] by auto
  {assume "t \<noteq> t\<^sub>0"
    then obtain r where rHyp: "r \<in> {t\<^sub>0<--<t}" 
      and "(\<mu>(X t)-\<nu>(X t)) - (\<mu>(X t\<^sub>0)-\<nu>(X t\<^sub>0)) = (\<lambda>\<tau>. \<tau>*(\<mu>'(X r)-\<nu>'(X r))) (t - t\<^sub>0)"
      using mvt_simple_closed_segmentE obs2 by blast
    hence mvt: "\<mu>(X t)-\<nu>(X t) = (t - t\<^sub>0)*(\<mu>'(X r)-\<nu>'(X r)) + (\<mu>(X t\<^sub>0)-\<nu>(X t\<^sub>0))"
      by force
    have primed: "\<And>\<tau>. \<tau> \<in> U (X t\<^sub>0) \<Longrightarrow> \<tau> > t\<^sub>0 \<Longrightarrow> G (X \<tau>) \<Longrightarrow> \<mu>' (X \<tau>) \<ge> \<nu>' (X \<tau>)" 
      "\<And>\<tau>. \<tau> \<in> U (X t\<^sub>0) \<Longrightarrow> \<tau> < t\<^sub>0 \<Longrightarrow> \<mu>' (X \<tau>) \<le> \<nu>' (X \<tau>)"
      using Gg[OF xivp(1)] Gl[OF xivp(1)] by auto
    have "t > t\<^sub>0 \<Longrightarrow> r > t\<^sub>0 \<and> G (X r)" "\<not> t\<^sub>0 \<le> t \<Longrightarrow> r < t\<^sub>0" "r \<in> U (X t\<^sub>0)"
      using \<open>r \<in> {t\<^sub>0<--<t}\<close> obs1 Ghyp
      unfolding open_segment_eq_real_ivl closed_segment_eq_real_ivl by auto
    moreover have "r > t\<^sub>0 \<Longrightarrow> G (X r) \<Longrightarrow> (\<mu>'(X r)- \<nu>'(X r)) \<ge> 0" "r < t\<^sub>0 \<Longrightarrow> (\<mu>'(X r)-\<nu>'(X r)) \<le> 0"
      using primed(1,2)[OF \<open>r \<in> U (X t\<^sub>0)\<close>] by auto
    ultimately have "(t - t\<^sub>0) * (\<mu>'(X r)-\<nu>'(X r)) \<ge> 0"
      by (case_tac "t \<ge> t\<^sub>0", force, auto simp: split_mult_pos_le)
    hence "(t - t\<^sub>0) * (\<mu>'(X r)-\<nu>'(X r)) + (\<mu>(X t\<^sub>0)-\<nu>(X t\<^sub>0)) > 0"
      using xivp(2) by auto
    hence "\<nu> (X t) < \<mu> (X t)"
      using mvt by simp}
  thus "\<nu> (X t) < \<mu> (X t)"
    using xivp by blast
qed

lemma diff_invariant_nleq_rule:
  fixes \<mu>::"'a::banach \<Rightarrow> real"
  shows "diff_invariant (\<lambda>s. \<not> \<nu> s \<le> \<mu> s) f U S t\<^sub>0 G \<longleftrightarrow> diff_invariant (\<lambda>s. \<nu> s > \<mu> s) f U S t\<^sub>0 G"
  unfolding diff_invariant_eq apply safe
  by (clarsimp, erule_tac x=s in allE, simp, erule_tac x=X in ballE, force, force)+

lemma diff_invariant_neq_rule [diff_invariant_rules]:
  fixes \<mu>::"'a::banach \<Rightarrow> real"
  assumes "diff_invariant (\<lambda>s. \<nu> s < \<mu> s) f U S t\<^sub>0 G"
    and "diff_invariant (\<lambda>s. \<nu> s > \<mu> s) f U S t\<^sub>0 G"
  shows "diff_invariant (\<lambda>s. \<nu> s \<noteq> \<mu> s) f U S t\<^sub>0 G"
proof(unfold diff_invariant_eq, clarsimp)
  fix s::'a and X::"real \<Rightarrow> 'a" and t::real
  assume "\<nu> s \<noteq> \<mu> s" and Xhyp: "X \<in> Sols f U S t\<^sub>0 s" 
     and thyp: "t \<in> U s" and Ghyp: "\<forall>\<tau>. \<tau> \<in> U s \<and> \<tau> \<le> t \<longrightarrow> G (X \<tau>)"
  hence "\<nu> s < \<mu> s \<or> \<nu> s > \<mu> s"
    by linarith
  moreover have "\<nu> s < \<mu> s \<Longrightarrow> \<nu> (X t) < \<mu> (X t)"
    using assms(1) Xhyp thyp Ghyp unfolding diff_invariant_eq by auto
  moreover have "\<nu> s > \<mu> s \<Longrightarrow> \<nu> (X t) > \<mu> (X t)"
    using assms(2) Xhyp thyp Ghyp unfolding diff_invariant_eq by auto
  ultimately show "\<nu> (X t) = \<mu> (X t) \<Longrightarrow> False"
    by auto
qed

lemma diff_invariant_neq_rule_converse:
  fixes \<mu>::"'a::banach \<Rightarrow> real"
  assumes Uhyp: "\<And>s. s \<in> S \<Longrightarrow> is_interval (U s)" "\<And>s t. s \<in> S \<Longrightarrow> t \<in> U s \<Longrightarrow> t\<^sub>0 \<le> t"
    and conts: "\<And>X. (D X = (\<lambda>\<tau>. f \<tau> (X \<tau>)) on U(X t\<^sub>0)) \<Longrightarrow> continuous_on (\<P> X (U (X t\<^sub>0))) \<nu>"
      "\<And>X. (D X = (\<lambda>\<tau>. f \<tau> (X \<tau>)) on U(X t\<^sub>0)) \<Longrightarrow> continuous_on (\<P> X (U (X t\<^sub>0))) \<mu>"
    and dI:"diff_invariant (\<lambda>s. \<nu> s \<noteq> \<mu> s) f U S t\<^sub>0 G"
  shows "diff_invariant (\<lambda>s. \<nu> s < \<mu> s) f U S t\<^sub>0 G"
proof(unfold diff_invariant_eq ivp_sols_def, clarsimp)
  fix X t assume Ghyp: "\<forall>\<tau>. \<tau> \<in> U (X t\<^sub>0) \<and> \<tau> \<le> t \<longrightarrow> G (X \<tau>)"
  assume xivp: "D X = (\<lambda>x. f x (X x)) on U (X t\<^sub>0)" "\<nu> (X t\<^sub>0) < \<mu> (X t\<^sub>0)" "X \<in> U (X t\<^sub>0) \<rightarrow> S"
  assume tHyp: "t \<in> U (X t\<^sub>0)" and t0Hyp: "t\<^sub>0 \<in> U (X t\<^sub>0)"
  hence "t\<^sub>0 \<le> t" and "\<mu> (X t) \<noteq> \<nu> (X t)"
    using xivp(3) Uhyp(2) apply force
    using dI tHyp xivp(2) Ghyp ivp_solsI[of X f U "X t\<^sub>0", OF xivp(1) _ xivp(3) t0Hyp]
    unfolding diff_invariant_eq by force
  moreover
  {assume ineq2:"\<nu> (X t) > \<mu> (X t)"
    note continuous_on_compose[OF vderiv_on_continuous_on[OF xivp(1)]]
    hence "continuous_on (U (X t\<^sub>0)) (\<nu> \<circ> X)" and "continuous_on (U (X t\<^sub>0)) (\<mu> \<circ> X)"
      using xivp(1) conts by blast+
    also have "{t\<^sub>0--t} \<subseteq> U (X t\<^sub>0)"
      using closed_segment_subset_interval[OF Uhyp(1) t0Hyp tHyp] xivp(3) t0Hyp by auto
    ultimately have "continuous_on {t\<^sub>0--t} (\<lambda>\<tau>. \<nu> (X \<tau>))" 
      and "continuous_on {t\<^sub>0--t} (\<lambda>\<tau>. \<mu> (X \<tau>))"
      using continuous_on_subset by auto
    then obtain \<tau> where "\<tau> \<in> {t\<^sub>0--t}" "\<mu> (X \<tau>) = \<nu> (X \<tau>)"
      using IVT_two_functions_real_ivl[OF _ _ xivp(2) ineq2] by force
    hence "\<forall>r\<in>down (U (X t\<^sub>0)) \<tau>. G (X r)" and "\<tau> \<in> U (X t\<^sub>0)"
      using Ghyp \<open>\<tau> \<in> {t\<^sub>0--t}\<close> \<open>t\<^sub>0 \<le> t\<close> \<open>{t\<^sub>0--t} \<subseteq> U (X t\<^sub>0)\<close> 
      by (auto simp: closed_segment_eq_real_ivl)
    hence "\<mu> (X \<tau>) \<noteq> \<nu> (X \<tau>)"
      using dI tHyp xivp(2) ivp_solsI[of X f U "X t\<^sub>0", OF xivp(1) _ xivp(3) t0Hyp]
      unfolding diff_invariant_eq by force
    hence "False"
      using \<open>\<mu> (X \<tau>) = \<nu> (X \<tau>)\<close> by blast}
  ultimately show "\<nu> (X t) < \<mu> (X t)"
    by fastforce
qed

lemma diff_invariant_conj_rule [diff_invariant_rules]:
  assumes "diff_invariant I\<^sub>1 f U S t\<^sub>0 G"
    and "diff_invariant I\<^sub>2 f U S t\<^sub>0 G"
  shows "diff_invariant (\<lambda>s. I\<^sub>1 s \<and> I\<^sub>2 s) f U S t\<^sub>0 G"
  using assms unfolding diff_invariant_def by auto

lemma diff_invariant_disj_rule [diff_invariant_rules]:
  assumes "diff_invariant I\<^sub>1 f U S t\<^sub>0 G"
    and "diff_invariant I\<^sub>2 f U S t\<^sub>0 G"
  shows "diff_invariant (\<lambda>s. I\<^sub>1 s \<or> I\<^sub>2 s) f U S t\<^sub>0 G"
  using assms unfolding diff_invariant_def by auto



type_synonym 'a pred = "'a \<Rightarrow> bool"

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

lemma fbox_g_orbital: "|g_orbital f G U t\<^sub>0] Q = 
  (\<lambda>s. \<forall>t. \<forall>X\<in>Sols f {t\<^sub>0--t} t\<^sub>0 s. {t\<^sub>0--t} \<subseteq> U (X t\<^sub>0) \<longrightarrow> (\<forall>\<tau>\<in>{t\<^sub>0--t}. G (X \<tau>)) \<longrightarrow> Q (X t))"
  unfolding fbox_def g_orbital_eq apply(auto simp: fun_eq_iff)
   apply(erule_tac x="X t" in allE, clarsimp, erule_tac x=t in allE)
   apply(clarsimp simp: ivp_sols_def, erule_tac x=X in allE, force)
  by (erule_tac x=t in allE, erule_tac x=X in ballE; clarsimp simp: ivp_sols_def)

lemma fbox_g_orbital_ivl: "\<forall>s. is_interval (U s) \<and> t\<^sub>0 \<in> U s \<Longrightarrow> |g_orbital f G U t\<^sub>0] Q = 
  (\<lambda>s. \<forall>t\<in>U s. \<forall>X\<in>Sols f {t\<^sub>0--t} t\<^sub>0 s. (\<forall>\<tau>\<in>{t\<^sub>0--t}. G (X \<tau>)) \<longrightarrow> Q (X t))"
  unfolding fbox_g_orbital apply(clarsimp simp: fun_eq_iff)
  using closed_segment_subset_interval
  by (smt (verit, best) ends_in_segment(2) ivp_solsD(2) subset_iff)

end