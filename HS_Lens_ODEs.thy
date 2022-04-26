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
  "('c \<Longrightarrow> 's) \<comment> \<open> A lens selecting a local region \<close> 
   \<Rightarrow> (real \<Rightarrow> 's \<Rightarrow> 's) \<comment> \<open> Substitution on the global state space\<close>
   \<Rightarrow> 's \<comment> \<open> An initial global state \<close>
   \<Rightarrow> (real \<Rightarrow> 'c \<Rightarrow> 'c)" \<comment> \<open> Substitution on the local state space \<close>
   where "loc_subst a f s \<equiv> (\<lambda> t c. get\<^bsub>a\<^esub> (f t (put\<^bsub>a\<^esub> s c)))"

text \<open> A version of guarded orbits localised by a lens \<close>

text \<open> A version of orbital localised by a lens \<close>

definition
  g_orbital_on :: 
    "('c::real_normed_vector \<Longrightarrow> 'a) 
      \<Rightarrow> (real \<Rightarrow> 'a \<Rightarrow> 'a) 
      \<Rightarrow> ('a \<Rightarrow> bool) 
      \<Rightarrow> ('c \<Rightarrow> real set) \<Rightarrow> 'c set \<Rightarrow> real => 'a \<Rightarrow> 'a set"
    where "g_orbital_on a f G U S t\<^sub>0 
            = (\<lambda> s. put\<^bsub>a\<^esub> s 
              ` g_orbital 
                  (loc_subst a f s) 
                  (\<lambda> c. G (put\<^bsub>a\<^esub> s c))
                  U S
                  t\<^sub>0 (get\<^bsub>a\<^esub> s))"

lemma g_orbital_on_id_lens: "g_orbital_on \<one>\<^sub>L = g_orbital"
  by (simp add: g_orbital_on_def fun_eq_iff lens_defs)

lemma g_orbital_on_eq: "g_orbital_on a f G U S t\<^sub>0 s = 
  {put\<^bsub>a\<^esub> s (X t) |t X. t \<in> U (get\<^bsub>a\<^esub> s) \<and> \<P> (\<lambda>x. put\<^bsub>a\<^esub> s (X x)) (down (U (get\<^bsub>a\<^esub> s)) t) \<subseteq> {s. G s} \<and> X \<in> Sols U S (loc_subst a f s) t\<^sub>0 (get\<^bsub>a\<^esub> s)}"
  unfolding g_orbital_on_def g_orbital_eq image_le_pred 
  by (auto simp: image_def)

lemma g_orbital_onI:
  assumes "X \<in> Sols U S (\<lambda>t c. get\<^bsub>a\<^esub> (f t (put\<^bsub>a\<^esub> s c))) t\<^sub>0 (get\<^bsub>a\<^esub> s)"
    and "t \<in> U (get\<^bsub>a\<^esub> s)" and "(\<P> (\<lambda>x. put\<^bsub>a\<^esub> s (X x)) (down (U (get\<^bsub>a\<^esub> s)) t) \<subseteq> Collect G)"
  shows "put\<^bsub>a\<^esub> s (X t) \<in> g_orbital_on a f G U S t\<^sub>0 s"
  using assms unfolding g_orbital_on_eq by auto

subsection \<open> Differential Invariants \<close>

definition diff_invariant_on :: "('a \<Rightarrow> bool) \<Rightarrow> ('c:: real_normed_vector \<Longrightarrow> 'a) \<Rightarrow> (real \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 
  ('c \<Rightarrow> real set) \<Rightarrow> 'c set \<Rightarrow> real \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" 
  where "diff_invariant_on I a f U S t\<^sub>0 G \<equiv> (\<Union> \<circ> (\<P> (g_orbital_on a f G U S t\<^sub>0))) {s. I s} \<subseteq> {s. I s}"

lemma diff_invariant_on_eq: "diff_invariant_on I a f U S t\<^sub>0 G = 
  (\<forall>s. I s \<longrightarrow> (\<forall>X\<in>Sols U S (loc_subst a f s) t\<^sub>0 (get\<^bsub>a\<^esub> s). (\<forall>t\<in>U (get\<^bsub>a\<^esub> s).(\<forall>\<tau>\<in>(down (U (get\<^bsub>a\<^esub> s)) t). G (put\<^bsub>a\<^esub> s (X \<tau>))) \<longrightarrow> I (put\<^bsub>a\<^esub> s (X t)))))"
  unfolding diff_invariant_on_def g_orbital_on_eq image_le_pred by (auto simp: image_def)

lemma diff_invariant_on_id_lens: "diff_invariant_on I \<one>\<^sub>L f U S t\<^sub>0 G = diff_invariant I f U S t\<^sub>0 G"
  by (simp add: diff_invariant_on_def diff_invariant_def g_orbital_on_id_lens)

named_theorems diff_invariant_on_rules "rules for certifying (localised) differential invariants"

lemma diff_invariant_on_eq_rule_expr [diff_invariant_on_rules]:
  assumes "vwb_lens a"
    and Uhyp: "\<And>s. s \<in> S \<Longrightarrow> is_interval (U s)"
    and dX: "\<And>X t s. (D X = (\<lambda>\<tau>. get\<^bsub>a\<^esub> (f \<tau> (put\<^bsub>a\<^esub> s (X \<tau>)))) on U (get\<^bsub>a\<^esub> s)) \<Longrightarrow>
  \<forall>\<tau>\<in>(down (U(get\<^bsub>a\<^esub> s)) t). G (put\<^bsub>a\<^esub> s (X \<tau>)) \<Longrightarrow> (D (\<lambda>\<tau>. \<mu> (put\<^bsub>a\<^esub> s (X \<tau>))-\<nu>(put\<^bsub>a\<^esub> s (X \<tau>))) = ((*\<^sub>R) 0) on U (get\<^bsub>a\<^esub> s))"
  shows "diff_invariant_on (\<mu> = \<nu>)\<^sub>e a f U S t\<^sub>0 G"
proof(simp add: diff_invariant_on_eq ivp_sols_def, clarsimp simp: SEXP_def)
  fix X t s
  assume xivp: "D X = (\<lambda>\<tau>. loc_subst a f s \<tau> (X \<tau>)) on U (get\<^bsub>a\<^esub> s)" "\<mu> s = \<nu> s" "X \<in> U (get\<^bsub>a\<^esub> s) \<rightarrow> S"
    and tHyp: "t \<in> U (get\<^bsub>a\<^esub> s)" and t0Hyp: "t\<^sub>0 \<in> U (get\<^bsub>a\<^esub> s)" and init: "X t\<^sub>0 = get\<^bsub>a\<^esub> s"
    and GHyp: "\<forall>\<tau>. \<tau> \<in> U (get\<^bsub>a\<^esub> s) \<and> \<tau> \<le> t \<longrightarrow> G (put\<^bsub>a\<^esub> s (X \<tau>))"
  hence "(D (\<lambda>\<tau>. \<mu> (put\<^bsub>a\<^esub> s (X \<tau>))-\<nu>(put\<^bsub>a\<^esub> s (X \<tau>))) = ((*\<^sub>R) 0) on U (get\<^bsub>a\<^esub> s))"
    using dX by auto
  hence "D (\<lambda>\<tau>. \<mu> (put\<^bsub>a\<^esub> s (X \<tau>))-\<nu>(put\<^bsub>a\<^esub> s (X \<tau>))) = ((*\<^sub>R) 0) on {t\<^sub>0--t}"
    apply(rule has_vderiv_on_subset[OF _ closed_segment_subset_interval[OF Uhyp t0Hyp tHyp]])
    using xivp(3) t0Hyp init by force
  then obtain \<tau> where "\<mu> (put\<^bsub>a\<^esub> s (X t)) - \<nu> (put\<^bsub>a\<^esub> s (X t)) - (\<mu> (put\<^bsub>a\<^esub> s (X t\<^sub>0)) - \<nu> (put\<^bsub>a\<^esub> s (X t\<^sub>0))) = (t - t\<^sub>0) * \<tau> *\<^sub>R 0"
    using mvt_very_simple_closed_segmentE by fastforce
  thus "\<mu> (put\<^bsub>a\<^esub> s (X t)) = \<nu> (put\<^bsub>a\<^esub> s (X t))" 
    using xivp(2) assms(1) init by simp
qed

lemma diff_invariant_on_eq_rule_expr_inner [diff_invariant_on_rules]:
  fixes \<mu> \<nu> :: "_ \<Rightarrow> 'c::real_inner"
  assumes "vwb_lens a"
    and dX: "\<And>X t s. (D X = (\<lambda>\<tau>. get\<^bsub>a\<^esub> (f \<tau> (put\<^bsub>a\<^esub> s (X \<tau>)))) on {t\<^sub>0..}) \<Longrightarrow>
  \<forall>\<tau>\<in>(down {t\<^sub>0..} t). G (put\<^bsub>a\<^esub> s (X \<tau>)) \<Longrightarrow> (D (\<lambda>\<tau>. \<mu> (put\<^bsub>a\<^esub> s (X \<tau>))- \<nu> (put\<^bsub>a\<^esub> s (X \<tau>))) = (\<lambda> t. 0) on {t\<^sub>0..})"
  shows "diff_invariant_on (\<mu> = \<nu>)\<^sub>e a f (\<lambda> _. {t\<^sub>0..}) S t\<^sub>0 G"
proof(simp add: diff_invariant_on_eq ivp_sols_def, clarsimp simp: SEXP_def)
  fix X t s
  assume xivp: "D X = (\<lambda>\<tau>. loc_subst a f s \<tau> (X \<tau>)) on {t\<^sub>0..}" "\<mu> s = \<nu> s" "X \<in> {t\<^sub>0..} \<rightarrow> S"
    and t0Hyp: "t\<^sub>0 \<le> t" and init: "X t\<^sub>0 = get\<^bsub>a\<^esub> s"
    and GHyp: "\<forall>\<tau>. t\<^sub>0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> G (put\<^bsub>a\<^esub> s (X \<tau>))"
  show "\<mu> (put\<^bsub>a\<^esub> s (X t)) = \<nu> (put\<^bsub>a\<^esub> s (X t))"
  proof (cases "t\<^sub>0 = t")
    case True
    then show ?thesis
      using assms(1) init xivp(2) by auto 
  next
    case False
    hence t0: "t\<^sub>0 < t"
      using t0Hyp by linarith
    have "(D (\<lambda>\<tau>. \<mu> (put\<^bsub>a\<^esub> s (X \<tau>))-\<nu>(put\<^bsub>a\<^esub> s (X \<tau>))) = (\<lambda> t. 0) on {t\<^sub>0..})"
      using dX[OF xivp(1)] GHyp by blast
    hence D: "D (\<lambda>\<tau>. \<mu> (put\<^bsub>a\<^esub> s (X \<tau>))-\<nu>(put\<^bsub>a\<^esub> s (X \<tau>))) = (\<lambda> t. 0) on {t\<^sub>0--t}"
      by(rule has_vderiv_on_subset[OF _ closed_segment_subset_interval[OF _]], auto simp add: t0Hyp)
    hence cont: "continuous_on {t\<^sub>0..t} (\<lambda>\<tau>. \<mu> (put\<^bsub>a\<^esub> s (X \<tau>)) - \<nu> (put\<^bsub>a\<^esub> s (X \<tau>)))"
      by (simp add: ODE_Auxiliarities.closed_segment_eq_real_ivl t0Hyp vderiv_on_continuous_on)
    have DR: "(\<And>x. t\<^sub>0 < x \<Longrightarrow> x < t \<Longrightarrow> D (\<lambda>\<tau>. \<mu> (put\<^bsub>a\<^esub> s (X \<tau>)) - \<nu> (put\<^bsub>a\<^esub> s (X \<tau>))) \<mapsto> (\<lambda>t. 0) at x)"
      using D by (auto simp add: has_vderiv_on_def has_vector_derivative_def)
                 (metis (full_types) ODE_Auxiliarities.closed_segment_eq_real_ivl 
                  atLeastAtMost_iff at_within_Icc_at ends_in_segment(1) not_le t0Hyp)
    have "\<parallel>\<mu> (put\<^bsub>a\<^esub> s (X t)) - \<nu> (put\<^bsub>a\<^esub> s (X t)) - (\<mu> (put\<^bsub>a\<^esub> s (X t\<^sub>0)) - \<nu> (put\<^bsub>a\<^esub> s (X t\<^sub>0)))\<parallel> \<le> \<parallel>0\<parallel>"
      using mvt_general[where f="(\<lambda>\<tau>. \<mu> (put\<^bsub>a\<^esub> s (X \<tau>))-\<nu>(put\<^bsub>a\<^esub> s (X \<tau>)))" and f'="\<lambda> _ t. 0", OF t0 cont DR]
      by auto
    thus "\<mu> (put\<^bsub>a\<^esub> s (X t)) = \<nu> (put\<^bsub>a\<^esub> s (X t))" 
      using xivp(2) assms(1) init by simp
  qed
qed

lemma diff_invariant_on_le_rule_expr [diff_invariant_on_rules]:
  fixes \<mu>::"'a \<Rightarrow> real"
  assumes "vwb_lens a"
    and Uhyp: "\<And>s. s \<in> S \<Longrightarrow> is_interval (U s)"
    and Gg: "\<And>X s. D X = (\<lambda>\<tau>. get\<^bsub>a\<^esub> (f \<tau> (put\<^bsub>a\<^esub> s (X \<tau>)))) on U (get\<^bsub>a\<^esub> s) \<Longrightarrow> 
  (\<forall>\<tau>\<in>U(get\<^bsub>a\<^esub> s). \<tau> > t\<^sub>0 \<longrightarrow> G (put\<^bsub>a\<^esub> s (X \<tau>)) \<longrightarrow> \<mu>' (put\<^bsub>a\<^esub> s (X \<tau>)) \<ge> \<nu>' (put\<^bsub>a\<^esub> s (X \<tau>)))"
    and Gl: "\<And>X s. D X = (\<lambda>\<tau>. get\<^bsub>a\<^esub> (f \<tau> (put\<^bsub>a\<^esub> s (X \<tau>)))) on U (get\<^bsub>a\<^esub> s) \<Longrightarrow> 
  (\<forall>\<tau>\<in>U(get\<^bsub>a\<^esub> s). \<tau> < t\<^sub>0 \<longrightarrow> \<mu>' (put\<^bsub>a\<^esub> s (X \<tau>)) \<le> \<nu>' (put\<^bsub>a\<^esub> s (X \<tau>)))"
    and dX: "\<And>X s. D X = (\<lambda>\<tau>. get\<^bsub>a\<^esub> (f \<tau> (put\<^bsub>a\<^esub> s (X \<tau>)))) on U (get\<^bsub>a\<^esub> s) \<Longrightarrow> 
  D (\<lambda>\<tau>. \<mu>(put\<^bsub>a\<^esub> s (X \<tau>))-\<nu>(put\<^bsub>a\<^esub> s (X \<tau>))) = (\<lambda>\<tau>. \<mu>'(put\<^bsub>a\<^esub> s (X \<tau>))-\<nu>'(put\<^bsub>a\<^esub> s (X \<tau>))) on U(get\<^bsub>a\<^esub> s)"
  shows diff_invariant_on_leq_rule_expr: "diff_invariant_on (\<nu> \<le> \<mu>)\<^sub>e a f U S t\<^sub>0 G"
    and diff_invariant_on_less_rule_expr: "diff_invariant_on (\<nu> < \<mu>)\<^sub>e a f U S t\<^sub>0 G"
proof(simp_all add: diff_invariant_on_eq ivp_sols_def, safe)
  fix s X t assume Ghyp: "\<forall>\<tau>. \<tau> \<in> U (get\<^bsub>a\<^esub> s) \<and> \<tau> \<le> t \<longrightarrow> G (put\<^bsub>a\<^esub> s (X \<tau>))"
  assume xivp: "D X = (\<lambda>\<tau>. get\<^bsub>a\<^esub> (f \<tau> (put\<^bsub>a\<^esub> s (X \<tau>)))) on (U (get\<^bsub>a\<^esub> s))" "X \<in> U (get\<^bsub>a\<^esub> s) \<rightarrow> S"
  assume tHyp: "t \<in> U (get\<^bsub>a\<^esub> s)" and t0Hyp: "t\<^sub>0 \<in> U (get\<^bsub>a\<^esub> s)" "X t\<^sub>0 = get\<^bsub>a\<^esub> s"
  hence obs1: "{t\<^sub>0--t} \<subseteq> U (get\<^bsub>a\<^esub> s)" "{t\<^sub>0<--<t} \<subseteq> U (get\<^bsub>a\<^esub> s)"
    using closed_segment_subset_interval[OF Uhyp t0Hyp(1) tHyp] xivp(2) 
    by (metis Pi_iff, metis PiE \<open>get\<^bsub>a\<^esub> s \<in> S \<Longrightarrow> {t\<^sub>0--t} \<subseteq> U (get\<^bsub>a\<^esub> s)\<close> 
        dual_order.trans segment_open_subset_closed)
  hence obs2: "D (\<lambda>\<tau>. \<mu> (put\<^bsub>a\<^esub> s (X \<tau>)) - \<nu> (put\<^bsub>a\<^esub> s (X \<tau>))) = 
  (\<lambda>\<tau>. \<mu>' (put\<^bsub>a\<^esub> s (X \<tau>)) - \<nu>' (put\<^bsub>a\<^esub> s (X \<tau>))) on {t\<^sub>0--t}"
    using t0Hyp has_vderiv_on_subset[OF dX[OF xivp(1)]] by auto
  {assume "t \<noteq> t\<^sub>0"
    then obtain r where rHyp: "r \<in> {t\<^sub>0<--<t}" 
      and "(\<mu>(put\<^bsub>a\<^esub> s (X t))-\<nu>(put\<^bsub>a\<^esub> s (X t))) - (\<mu>(put\<^bsub>a\<^esub> s (X t\<^sub>0))-\<nu>(put\<^bsub>a\<^esub> s (X t\<^sub>0))) = 
      (\<lambda>\<tau>. \<tau>*(\<mu>'(put\<^bsub>a\<^esub> s (X r))-\<nu>'(put\<^bsub>a\<^esub> s (X r)))) (t - t\<^sub>0)"
      using mvt_simple_closed_segmentE obs2 by blast
    hence mvt: "\<mu>(put\<^bsub>a\<^esub> s (X t))-\<nu>(put\<^bsub>a\<^esub> s (X t)) = 
  (t - t\<^sub>0)*(\<mu>'(put\<^bsub>a\<^esub> s (X r))-\<nu>'(put\<^bsub>a\<^esub> s (X r))) + (\<mu>(put\<^bsub>a\<^esub> s (X t\<^sub>0))-\<nu>(put\<^bsub>a\<^esub> s (X t\<^sub>0)))"
      by force
    have primed: "\<And>\<tau>. \<tau> \<in> U (get\<^bsub>a\<^esub> s) \<Longrightarrow> \<tau> > t\<^sub>0 \<Longrightarrow> G (put\<^bsub>a\<^esub> s (X \<tau>)) \<Longrightarrow> 
      \<mu>' (put\<^bsub>a\<^esub> s (X \<tau>)) \<ge> \<nu>' (put\<^bsub>a\<^esub> s (X \<tau>))" 
      "\<And>\<tau>. \<tau> \<in> U (get\<^bsub>a\<^esub> s) \<Longrightarrow> \<tau> < t\<^sub>0 \<Longrightarrow> \<mu>' (put\<^bsub>a\<^esub> s (X \<tau>)) \<le> \<nu>' (put\<^bsub>a\<^esub> s (X \<tau>))"
      using Gg[OF xivp(1)] Gl[OF xivp(1)] by auto
    have "t > t\<^sub>0 \<Longrightarrow> r > t\<^sub>0 \<and> G (put\<^bsub>a\<^esub> s (X r))" "\<not> t\<^sub>0 \<le> t \<Longrightarrow> r < t\<^sub>0" "r \<in> U (get\<^bsub>a\<^esub> s)"
      using \<open>r \<in> {t\<^sub>0<--<t}\<close> obs1 Ghyp
      unfolding open_segment_eq_real_ivl closed_segment_eq_real_ivl by auto
    moreover have "r > t\<^sub>0 \<Longrightarrow> G (put\<^bsub>a\<^esub> s (X r)) \<Longrightarrow> (\<mu>'(put\<^bsub>a\<^esub> s (X r))- \<nu>'(put\<^bsub>a\<^esub> s (X r))) \<ge> 0" 
      "r < t\<^sub>0 \<Longrightarrow> (\<mu>'(put\<^bsub>a\<^esub> s (X r))-\<nu>'(put\<^bsub>a\<^esub> s (X r))) \<le> 0"
      using primed(1,2)[OF \<open>r \<in> U (get\<^bsub>a\<^esub> s)\<close>] by auto
    ultimately have "(t - t\<^sub>0) * (\<mu>'(put\<^bsub>a\<^esub> s (X r))-\<nu>'(put\<^bsub>a\<^esub> s (X r))) \<ge> 0"
      by (case_tac "t \<ge> t\<^sub>0", force, auto simp: split_mult_pos_le)
    hence "\<nu> s \<le> \<mu> s \<Longrightarrow> 
  (t - t\<^sub>0) * (\<mu>'(put\<^bsub>a\<^esub> s (X r))-\<nu>'(put\<^bsub>a\<^esub> s (X r))) + (\<mu>(put\<^bsub>a\<^esub> s (X t\<^sub>0))-\<nu>(put\<^bsub>a\<^esub> s (X t\<^sub>0))) \<ge> 0"
      and "\<nu> s < \<mu> s \<Longrightarrow> 
  (t - t\<^sub>0) * (\<mu>'(put\<^bsub>a\<^esub> s (X r))-\<nu>'(put\<^bsub>a\<^esub> s (X r))) + (\<mu>(put\<^bsub>a\<^esub> s (X t\<^sub>0))-\<nu>(put\<^bsub>a\<^esub> s (X t\<^sub>0))) > 0"
      using xivp(2) assms(1) t0Hyp(2) by auto
    hence "\<nu> s \<le> \<mu> s \<Longrightarrow> \<nu> (put\<^bsub>a\<^esub> s (X t)) \<le> \<mu> (put\<^bsub>a\<^esub> s (X t))"
      and "\<nu> s < \<mu> s \<Longrightarrow> \<nu> (put\<^bsub>a\<^esub> s (X t)) < \<mu> (put\<^bsub>a\<^esub> s (X t))"
      using mvt by auto}
  thus "\<nu> s \<le> \<mu> s \<Longrightarrow> \<nu> (put\<^bsub>a\<^esub> s (X t)) \<le> \<mu> (put\<^bsub>a\<^esub> s (X t))"
    and "\<nu> s < \<mu> s \<Longrightarrow> \<nu> (put\<^bsub>a\<^esub> s (X t)) < \<mu> (put\<^bsub>a\<^esub> s (X t))"
    using assms(1) t0Hyp(2) xivp(2) by (force, force)
qed

lemma 
  assumes "diff_invariant_on (I\<^sub>1)\<^sub>e a f U S t\<^sub>0 G"
    and "diff_invariant_on (I\<^sub>2)\<^sub>e a f U S t\<^sub>0 G"
  shows diff_invariant_on_conj_rule_expr: "diff_invariant_on (I\<^sub>1 \<and> I\<^sub>2)\<^sub>e a f U S t\<^sub>0 G"
    and diff_invariant_on_disj_rule_expr: "diff_invariant_on (I\<^sub>1 \<or> I\<^sub>2)\<^sub>e a f U S t\<^sub>0 G"
  using assms unfolding diff_invariant_on_eq by auto

named_theorems diff_invariant_rule_expr "encapsulating rules for (non-localised) differential invariants"

lemma diff_invariant_eq_rule_expr [diff_invariant_rule_expr]:
  fixes \<mu>::"'a::banach \<Rightarrow> real"
  assumes Uhyp: "\<And>s. s \<in> S \<Longrightarrow> is_interval (U s)"
    and dX: "\<And>X t. (D X = (\<lambda>\<tau>. f \<tau> (X \<tau>)) on U(X t\<^sub>0)) \<Longrightarrow> 
  \<forall>\<tau>\<in>(down (U(X t\<^sub>0)) t). G (X \<tau>) \<Longrightarrow> D (\<lambda>\<tau>. \<mu> (X \<tau>) - \<nu> (X \<tau>)) = (\<lambda>\<tau>. \<tau> *\<^sub>R 0) on U(X t\<^sub>0)"
  shows "diff_invariant (\<mu> = \<nu>)\<^sub>e f U S t\<^sub>0 G"
  using assms by (simp add: SEXP_def, rule diff_invariant_eq_rule, simp_all)

lemma diff_invariant_leq_rule_expr [diff_invariant_rule_expr]:
  fixes \<mu>::"'a::banach \<Rightarrow> real"
  assumes Uhyp: "\<And>s. s \<in> S \<Longrightarrow> is_interval (U s)"
    and Gg: "\<And>X. (D X = (\<lambda>\<tau>. f \<tau> (X \<tau>)) on U (X t\<^sub>0)) \<Longrightarrow> (\<forall>\<tau>\<in>U (X t\<^sub>0). \<tau> > t\<^sub>0 \<longrightarrow> G (X \<tau>) \<longrightarrow> \<mu>' (X \<tau>) \<ge> \<nu>' (X \<tau>))"
    and Gl: "\<And>X. (D X = (\<lambda>\<tau>. f \<tau> (X \<tau>)) on U (X t\<^sub>0)) \<Longrightarrow> (\<forall>\<tau>\<in>U (X t\<^sub>0). \<tau> < t\<^sub>0 \<longrightarrow> \<mu>' (X \<tau>) \<le> \<nu>' (X \<tau>))"
    and dX: "\<And>X. (D X = (\<lambda>\<tau>. f \<tau> (X \<tau>)) on U (X t\<^sub>0)) \<Longrightarrow> D (\<lambda>\<tau>. \<mu>(X \<tau>)-\<nu>(X \<tau>)) = (\<lambda>\<tau>. \<mu>'(X \<tau>)-\<nu>'(X \<tau>)) on U (X t\<^sub>0)"
  shows "diff_invariant (\<nu> \<le> \<mu>)\<^sub>e f U S t\<^sub>0 G"
  using assms
  by (simp add: SEXP_def, rule diff_invariant_leq_rule, simp_all)

lemma diff_invariant_less_rule_expr [diff_invariant_rule_expr]:
  fixes \<mu>::"'a::banach \<Rightarrow> real"
  assumes Uhyp: "\<And>s. s \<in> S \<Longrightarrow> is_interval (U s)"
    and Gg: "\<And>X. (D X = (\<lambda>\<tau>. f \<tau> (X \<tau>)) on U (X t\<^sub>0)) \<Longrightarrow> (\<forall>\<tau>\<in>U (X t\<^sub>0). \<tau> > t\<^sub>0 \<longrightarrow> G (X \<tau>) \<longrightarrow> \<mu>' (X \<tau>) \<ge> \<nu>' (X \<tau>))"
    and Gl: "\<And>X. (D X = (\<lambda>\<tau>. f \<tau> (X \<tau>)) on U (X t\<^sub>0)) \<Longrightarrow> (\<forall>\<tau>\<in>U (X t\<^sub>0). \<tau> < t\<^sub>0 \<longrightarrow> \<mu>' (X \<tau>) \<le> \<nu>' (X \<tau>))"
    and dX: "\<And>X. (D X = (\<lambda>\<tau>. f \<tau> (X \<tau>)) on U (X t\<^sub>0)) \<Longrightarrow> D (\<lambda>\<tau>. \<mu>(X \<tau>)-\<nu>(X \<tau>)) = (\<lambda>\<tau>. \<mu>'(X \<tau>)-\<nu>'(X \<tau>)) on U (X t\<^sub>0)"
  shows "diff_invariant (\<nu> < \<mu>)\<^sub>e f U S t\<^sub>0 G"
  using assms
  by (simp add: SEXP_def, rule diff_invariant_less_rule, simp_all)

lemma diff_invariant_nleq_rule_expr:
  fixes \<mu>::"'a::banach \<Rightarrow> real"
  shows "diff_invariant (\<not> \<nu> \<le> \<mu>)\<^sub>e f U S t\<^sub>0 G \<longleftrightarrow> diff_invariant (\<nu> > \<mu>)\<^sub>e f U S t\<^sub>0 G"
  by (simp add: SEXP_def, subst diff_invariant_nleq_rule, simp_all)

lemma diff_invariant_neq_rule_expr [diff_invariant_rule_expr]:
  fixes \<mu>::"'a::banach \<Rightarrow> real"
  assumes "diff_invariant (\<nu> < \<mu>)\<^sub>e f U S t\<^sub>0 G"
    and "diff_invariant (\<nu> > \<mu>)\<^sub>e f U S t\<^sub>0 G"
  shows "diff_invariant (\<nu> \<noteq> \<mu>)\<^sub>e f U S t\<^sub>0 G"
  using assms apply(simp add: SEXP_def)
  by (rule diff_invariant_neq_rule, simp_all)

lemma diff_invariant_neq_rule_expr_converse:
  fixes \<mu>::"'a::banach \<Rightarrow> real"
  assumes Uhyp: "\<And>s. s \<in> S \<Longrightarrow> is_interval (U s)" "\<And>s t. s \<in> S \<Longrightarrow> t \<in> U s \<Longrightarrow> t\<^sub>0 \<le> t"
    and conts: "\<And>X. (D X = (\<lambda>\<tau>. f \<tau> (X \<tau>)) on U (X t\<^sub>0)) \<Longrightarrow> continuous_on (\<P> X (U (X t\<^sub>0))) \<nu>"
      "\<And>X. (D X = (\<lambda>\<tau>. f \<tau> (X \<tau>)) on U (X t\<^sub>0)) \<Longrightarrow> continuous_on (\<P> X (U (X t\<^sub>0))) \<mu>"
    and dI:"diff_invariant (\<nu> \<noteq> \<mu>)\<^sub>e f U S t\<^sub>0 G"
  shows "diff_invariant (\<nu> < \<mu>)\<^sub>e f U S t\<^sub>0 G"
  using assms apply(simp add: SEXP_def)
  by (rule diff_invariant_neq_rule_converse, simp_all)

lemma diff_invariant_cnn_rule_expr:
  assumes "diff_invariant (I\<^sub>1)\<^sub>e f U S t\<^sub>0 G"
    and "diff_invariant (I\<^sub>2)\<^sub>e f U S t\<^sub>0 G"
  shows diff_invariant_conj_rule_expr [diff_invariant_rule_expr]: "diff_invariant (I\<^sub>1 \<and> I\<^sub>2)\<^sub>e f U S t\<^sub>0 G"
    and diff_invariant_disj_rule_expr [diff_invariant_rule_expr]: "diff_invariant (I\<^sub>1 \<or> I\<^sub>2)\<^sub>e f U S t\<^sub>0 G"
  using assms unfolding diff_invariant_eq by auto

lemma diff_ghost_very_simple:
  assumes 
    "vwb_lens y" "y \<bowtie> a" "y \<sharp>\<^sub>s \<sigma>" "$y \<sharp> B"
    "diff_invariant_on (G)\<^sub>e (a +\<^sub>L y) (\<lambda>t. \<sigma>(y \<leadsto> \<guillemotleft>k\<guillemotright> *\<^sub>R $y)) (Collect ((\<le>) 0))\<^sub>e UNIV 0 B"
  shows "diff_invariant_on (G \\ $y)\<^sub>e a (\<lambda>t. \<sigma>) (Collect ((\<le>) 0))\<^sub>e UNIV 0 B"
  using assms(5)
  apply (simp add: expr_defs diff_invariant_on_eq)
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