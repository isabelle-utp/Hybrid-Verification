(*  Title: HS verification with lenses *)

section \<open> HS verification with lenses \<close>

text \<open> We use shallow expressions to rephrase hybrid systems properties. Each operator below 
includes lemmas for verification condition generation. \<close>

theory Diff_Dyn_Logic
  imports Evolution_Commands
    Regular_Programs
    "Matrix_ODE_Verify.MTX_Flows"
begin


subsection \<open> Derivation of the rules of dL \<close>

lemma nmods_g_orbital_on_discrete [closure]:
  assumes "\<And> v. (a)\<^sub>e\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk> = (a)\<^sub>e"
  shows "(g_orbital_on x f G U S t\<^sub>0) nmods a"
  using assms
  by (auto simp add: not_modifies_def g_orbital_on_eq expr_defs fun_eq_iff)

(*
lemma nmods_g_orbital_on_discrete' [closure]:
  assumes "vwb_lens x" 
  shows "(g_orbital_on x f G U S t\<^sub>0) nmods (- $x)"
  by (rule nmods_g_orbital_on_discrete) 
    (simp_all add: assms lens_override_def scene_indep_self_compl var_alpha_def)

lemma nmods_g_orbital_on_discrete_lens [closure]:
  assumes "vwb_lens A" "vwb_lens x" "x \<bowtie> A"
  shows "(g_orbital_on A f G U S t\<^sub>0) nmods $x"
  by (rule nmods_g_orbital_on_discrete) 
    (simp_all add: assms lens_indep_sym scene_indep_sym var_alpha_def) 
*)

subsection \<open> Derivation of the rules of dL \<close>

text \<open> We derive rules of differential dynamic logic (dL). First we present a
general version, then we show the rules as instances of the general ones.\<close>

notation g_orbital ("(1x\<acute>=_ & _ on _ _ @ _)")

abbreviation g_dl_ode ::"(('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> 'a \<Rightarrow> 'a set" 
  ("(1x\<acute>=_ & _)") where "(x\<acute>=f & G) \<equiv> (x\<acute>=(\<lambda>t. f) & G on (\<lambda>s. {t. t \<ge> 0}) UNIV @ 0)"

abbreviation g_dl_ode_inv ::"(('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> 'a pred \<Rightarrow> 'a \<Rightarrow> 'a set" ("(1x\<acute>=_ & _ DINV _)") 
  where "(x\<acute>=f & G DINV I) \<equiv> (x\<acute>=(\<lambda>t. f) & G on (\<lambda>s. {t. t \<ge> 0}) UNIV @ 0 DINV I)"

lemma diff_solve_axiom1: 
  assumes "local_flow f UNIV UNIV \<phi>"
  shows "|x\<acute>= f & G] Q = 
  (\<lambda>s. \<forall>t\<ge>0. (\<forall>\<tau>\<in>{0..t}. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s))"
  by (subst local_flow.fbox_g_ode_subset[OF assms], auto)

lemma diff_solve_axiom2: 
  fixes c::"'a::{heine_borel, banach}"
  shows "|x\<acute>=(\<lambda>s. c) & G] Q = 
  (\<lambda>s. \<forall>t\<ge>0. (\<forall>\<tau>\<in>{0..t}. G (s + \<tau> *\<^sub>R c)) \<longrightarrow> Q (s + t *\<^sub>R c))"
  by (subst local_flow.fbox_g_ode_subset[OF line_is_local_flow, of UNIV], auto)

lemma diff_solve_rule:
  assumes "local_flow f UNIV UNIV \<phi>"
    and "\<forall>s. P s \<longrightarrow> (\<forall>t\<ge>0. (\<forall>\<tau>\<in>{0..t}. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s))"
  shows "P \<le> |x\<acute>= f & G] Q"
  using assms by(subst local_flow.fbox_g_ode_subset[OF assms(1)]) auto

lemma diff_weak_axiom1: "( |x\<acute>= f & G on U S @ t\<^sub>0] G) s"
  unfolding fbox_def g_orbital_eq by auto

lemma diff_weak_axiom2: "|x\<acute>= f & G on T S @ t\<^sub>0] Q = |x\<acute>= f & G on T S @ t\<^sub>0] (G \<longrightarrow> Q)"
  unfolding fbox_g_orbital image_def by force
  
lemma diff_weak_rule: "G \<le> Q \<Longrightarrow> P \<le> |x\<acute>= f & G on T S @ t\<^sub>0] Q"
  by(auto intro: g_orbitalD simp: le_fun_def g_orbital_eq fbox_def)

lemma diff_weak_on_axiom1: "( |{x` = f | G on U S @ t\<^sub>0}] G) s"
  unfolding fbox_def g_orbital_on_eq by auto

lemma diff_weak_on_axiom2: "|{x` = f | G on T S @ t\<^sub>0}] Q = |{x` = f | G on T S @ t\<^sub>0}] (G \<longrightarrow> Q)"
  by (auto simp add: le_fun_def g_orbital_on_eq fbox_def fun_eq_iff)

lemma diff_weak_on_rule: "`G \<longrightarrow> Q` \<Longrightarrow> P \<le> |g_orbital_on a f (G)\<^sub>e U S t\<^sub>0] Q"
  by (auto simp add: le_fun_def g_orbital_on_eq fbox_def expr_defs)

lemma diff_cut_on_axiom:
  assumes "|{x` = f | G on U S @ t\<^sub>0}] C = (True)\<^sub>e"
  shows "|{x` = f | G on U S @ t\<^sub>0}] Q = |{x` = f | (G \<and> C) on U S @ t\<^sub>0}] Q"
proof(rule_tac f="\<lambda> x. |x] Q" in HOL.arg_cong, rule ext, rule subset_antisym)
  fix s::'a
  {fix s' assume "s' \<in> {x` = f | G on U S @ t\<^sub>0} s"
    then obtain \<tau>::real and X where "s' = put\<^bsub>x\<^esub> s (X \<tau>)" and "\<tau> \<in> (U (get\<^bsub>x\<^esub> s))" 
      and  x_ivp: "X \<in> Sols (U)\<^sub>e S (\<lambda>t c. get\<^bsub>x\<^esub> ([x \<leadsto> f] (put\<^bsub>x\<^esub> s c))) t\<^sub>0 (get\<^bsub>x\<^esub> s)"  
      and guard_x: "\<P> (\<lambda>t. put\<^bsub>x\<^esub> s (X t)) (down (U (get\<^bsub>x\<^esub> s)) \<tau>) \<subseteq> Collect (G)\<^sub>e"
      unfolding g_orbital_on_eq SEXP_def by (auto simp: tsubst2vecf_eq)
    have "\<forall>t\<in>(down (U (get\<^bsub>x\<^esub> s)) \<tau>). \<P> (\<lambda>t. put\<^bsub>x\<^esub> s (X t)) (down (U (get\<^bsub>x\<^esub> s)) t) \<subseteq> {s. G s}"
      using guard_x by (force simp: image_def)
    also have "\<forall>t\<in>(down (U (get\<^bsub>x\<^esub> s)) \<tau>). t \<in> U (get\<^bsub>x\<^esub> s)"
      using \<open>\<tau> \<in> U (get\<^bsub>x\<^esub> s)\<close> closed_segment_subset_interval by auto
    ultimately have "\<forall>t\<in>(down (U (get\<^bsub>x\<^esub> s)) \<tau>). put\<^bsub>x\<^esub> s (X t) \<in> {x` = f | G on U S @ t\<^sub>0} s"
      using g_orbital_onI[OF x_ivp] apply(simp only: SEXP_def)
       by (metis (mono_tags, lifting))
    hence "\<forall>t\<in>(down (U (get\<^bsub>x\<^esub> s)) \<tau>). C (put\<^bsub>x\<^esub> s (X t))" 
      using assms unfolding fbox_def SEXP_def by meson
    hence "s' \<in> {x` = f | (G \<and> C) on U S @ t\<^sub>0} s"
      using g_orbital_onI[OF x_ivp] \<open>\<tau> \<in> (U (get\<^bsub>x\<^esub> s))\<close>
        guard_x \<open>s' = put\<^bsub>x\<^esub> s (X \<tau>)\<close> by (fastforce simp add: SEXP_def)}
  thus "{x` = f | G on U S @ t\<^sub>0} s \<subseteq> {x` = f | G \<and> C on U S @ t\<^sub>0} s"
    by blast
next show "\<And>s. {x` = f | G \<and> C on U S @ t\<^sub>0} s \<subseteq> {x` = f | G on U S @ t\<^sub>0} s" 
    by (auto simp: g_orbital_on_eq)
qed

lemma diff_cut_on_rule:
  assumes fbox_C: "\<^bold>{P\<^bold>} g_orbital_on a f (G)\<^sub>e (U)\<^sub>e S t\<^sub>0 \<^bold>{C\<^bold>}"
    and fbox_Q: "\<^bold>{P\<^bold>} g_orbital_on a f (G \<and> C)\<^sub>e (U)\<^sub>e S t\<^sub>0 \<^bold>{Q\<^bold>}"
  shows "\<^bold>{P\<^bold>} g_orbital_on a f (G)\<^sub>e (U)\<^sub>e S t\<^sub>0 \<^bold>{Q\<^bold>}"
proof(subst fbox_def, subst g_orbital_on_eq, clarsimp simp: tsubst2vecf_eq)
  fix t::real and X::"real \<Rightarrow> 'b" and s   
  assume "P s" and "t \<in> U (get\<^bsub>a\<^esub> s)"
    and x_ivp:"X \<in> Sols (U)\<^sub>e S (\<lambda>t c. get\<^bsub>a\<^esub> (f t (put\<^bsub>a\<^esub> s c))) t\<^sub>0 (get\<^bsub>a\<^esub> s)" 
    and guard_x:"\<forall>\<tau>. \<tau> \<in> U (get\<^bsub>a\<^esub> s) \<and> \<tau> \<le> t \<longrightarrow> G (put\<^bsub>a\<^esub> s (X \<tau>))"
  have a: "\<forall>\<tau>\<in>(down (U (get\<^bsub>a\<^esub> s)) t). put\<^bsub>a\<^esub> s (X \<tau>) \<in> g_orbital_on a f (G)\<^sub>e U S t\<^sub>0 s"
    using g_orbital_onI[OF x_ivp] guard_x unfolding image_le_pred by (auto simp: SEXP_def)
  hence "\<forall>\<tau>\<in>(down (U (get\<^bsub>a\<^esub> s)) t). C (put\<^bsub>a\<^esub> s (X \<tau>))" 
    using fbox_C \<open>P s\<close> by (subst (asm) fbox_def, auto simp add: SEXP_def)
  hence "put\<^bsub>a\<^esub> s (X t) \<in> g_orbital_on a f (G \<and> C)\<^sub>e U S t\<^sub>0 s"
    using guard_x \<open>t \<in> U (get\<^bsub>a\<^esub> s)\<close> x_ivp
    by (auto simp add: SEXP_def intro!: g_orbital_onI)
  thus "Q (put\<^bsub>a\<^esub> s (X t))"
    using \<open>P s\<close> fbox_Q by (subst (asm) fbox_def) (auto simp add: SEXP_def)
qed

lemma diff_cut_on_split:
  assumes "\<^bold>{P\<^bold>} g_orbital_on a f (G)\<^sub>e (U)\<^sub>e S t\<^sub>0 \<^bold>{P\<^bold>}" "\<^bold>{Q\<^bold>} g_orbital_on a f (G \<and> P)\<^sub>e (U)\<^sub>e S t\<^sub>0\<^bold>{Q\<^bold>}"
  shows "\<^bold>{P \<and> Q\<^bold>} g_orbital_on a f (G)\<^sub>e (U)\<^sub>e S t\<^sub>0 \<^bold>{P \<and> Q\<^bold>}"
  apply (rule diff_cut_on_rule[where C="P"])
  using assms(1) apply (force intro!: hoare_conj_preI)
  apply (clarsimp simp: hoare_conj_pos)
  apply (intro conjI)
   apply (rule diff_weak_on_rule, simp)
  using assms(2) 
  by (force intro!: hoare_conj_preI)

lemma diff_cut_on_split':
  assumes "\<^bold>{P\<^bold>} g_orbital_on a f (G)\<^sub>e (U)\<^sub>e S t\<^sub>0 \<^bold>{P\<^bold>}" "\<^bold>{Q\<^bold>} g_orbital_on a f (G \<and> P)\<^sub>e (U)\<^sub>e S t\<^sub>0 \<^bold>{Q\<^bold>}"
  shows "\<^bold>{P \<and> Q\<^bold>} g_orbital_on a f (G)\<^sub>e (U)\<^sub>e S t\<^sub>0 \<^bold>{Q\<^bold>}"
  by (metis (mono_tags) assms diff_cut_on_split hoare_conj_pos)

lemma diff_inv_axiom1:
  assumes "G s \<longrightarrow> I s" and "diff_inv (\<lambda>s. {t. t \<ge> 0}) UNIV G (\<lambda>t. f) 0 I"
  shows "( |x\<acute>= f & G] I) s"
  using assms unfolding fbox_g_orbital diff_inv_eq apply clarsimp
  by (erule_tac x=s in allE, frule ivp_solsD(2), clarsimp)

lemma diff_inv_axiom2:
  assumes "picard_lindeloef (\<lambda>t. f) UNIV UNIV 0"
    and "\<And>s. {t::real. t \<ge> 0} \<subseteq> picard_lindeloef.ex_ivl (\<lambda>t. f) UNIV UNIV 0 s"
    and "diff_inv (\<lambda>s. {t. t \<ge> 0}) UNIV G (\<lambda>t. f) 0 I"
  shows "|x\<acute>= f & G] I = |(\<lambda>s. {x. s = x \<and> G s})] I"
proof(unfold fbox_g_orbital, subst fbox_def, clarsimp simp: fun_eq_iff)
  fix s
  let "?ex_ivl s" = "picard_lindeloef.ex_ivl (\<lambda>t. f) UNIV UNIV 0 s"
  let "?lhs s" = 
    "\<forall>X\<in>Sols (\<lambda>s. {t. t \<ge> 0}) UNIV (\<lambda>t. f) 0 s. \<forall>t\<ge>0. (\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> G (X \<tau>)) \<longrightarrow> I (X t)"
  obtain X where xivp1: "X \<in> Sols (\<lambda>s. ?ex_ivl s) UNIV (\<lambda>t. f) 0 s"
    using picard_lindeloef.flow_in_ivp_sols_ex_ivl[OF assms(1)] by auto
  have xivp2: "X \<in> Sols (\<lambda>s. Collect ((\<le>) 0)) UNIV (\<lambda>t. f) 0 s"
    by (rule in_ivp_sols_subset[OF _ _ xivp1], simp_all add: assms(2))
  hence shyp: "X 0 = s"
    using ivp_solsD by auto
  have dinv: "\<forall>s. I s \<longrightarrow> ?lhs s"
    using assms(3) unfolding diff_inv_eq by auto
  {assume "?lhs s" and "G s"
    hence "I s"
      by (erule_tac x=X in ballE, erule_tac x=0 in allE, auto simp: shyp xivp2)}
  hence "?lhs s \<longrightarrow> (G s \<longrightarrow> I s)" 
    by blast
  moreover
  {assume "G s \<longrightarrow> I s"
    hence "?lhs s"
      apply(clarify, subgoal_tac "\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> G (X \<tau>)")
       apply(erule_tac x=0 in allE, frule ivp_solsD(2), simp)
      using dinv by blast+}
  ultimately show "?lhs s = (G s \<longrightarrow> I s)"
    by blast
qed

lemma diff_inv_rule:
  assumes "P \<le> I" and "diff_inv U S G f t\<^sub>0 I" and "I \<le> Q"
  shows "P \<le> |x\<acute>= f & G on U S @ t\<^sub>0] Q"
  apply(rule fbox_inv[OF assms(1) _ assms(3)])
  unfolding fbox_diff_inv using assms(2) .

lemma diff_inv_on_rule:
  assumes "`P \<longrightarrow> I`" and "diff_inv_on a f G U S t\<^sub>0 I" and "`I \<longrightarrow> Q`"
  shows "\<^bold>{P\<^bold>} (g_orbital_on a f G U S t\<^sub>0) \<^bold>{Q\<^bold>}"
  using assms unfolding fbox_diff_inv_on[THEN sym] refine_iff_implies[THEN sym]
  by (metis (mono_tags, lifting) SEXP_def fbox_iso order.trans)


subsubsection \<open> Differential ghosts \<close>

lemma diff_ghost_gen_rule:
  assumes hyp: "\<^bold>{P\<^bold>} (g_orbital_on (x +\<^sub>L y) (\<lambda>t. f(y \<leadsto> \<guillemotleft>\<eta>\<guillemotright> ($y))) G (U \<circ> fst) UNIV 0) \<^bold>{Q\<^bold>}"
    and x_hyps: "vwb_lens x" and y_hyps: "vwb_lens y" "y \<bowtie> x" "($y \<sharp>\<^sub>s f)" "$y \<sharp> G" 
  (* assumes "\<^bold>{G\<^bold>} g_dl_ode_frame (a +\<^sub>L y) (\<sigma>(y \<leadsto> \<eta>)) B \<^bold>{G\<^bold>}"
  shows "\<^bold>{G \\ $y\<^bold>} g_dl_ode_frame a \<sigma> B \<^bold>{G \\ $y\<^bold>}" *)
  shows "\<^bold>{P \\ $y\<^bold>} (g_orbital_on x (\<lambda>t. f) G U S 0) \<^bold>{Q \\ $y\<^bold>}"
  oops (* generalise and finish proof *)

lemma diff_ghost_gen_rule:
  fixes A :: "('n::finite) sq_mtx" and b :: "real ^ 'n" 
  fixes x :: "'c :: real_normed_vector \<Longrightarrow> 's"
  defines "gen_sol \<equiv> (\<lambda>\<tau> \<s>. exp (\<tau> *\<^sub>R A) *\<^sub>V  \<s> + exp (\<tau> *\<^sub>R A) *\<^sub>V (\<integral>\<^sub>0\<^sup>\<tau>(exp (- r *\<^sub>R A) *\<^sub>V b)\<partial>r))" 
  assumes hyp: "\<^bold>{P\<^bold>} (g_orbital_on (x +\<^sub>L y) (\<lambda>t. f(y \<leadsto> (\<guillemotleft>A\<guillemotright> *\<^sub>V ($y) + \<guillemotleft>b\<guillemotright>))) G (U \<circ> fst) UNIV 0) \<^bold>{Q\<^bold>}" (* S' \<times> UNIV where S \<subseteq> S'*)
    and y_hyps: "vwb_lens y" "y \<bowtie> x" "($y \<sharp>\<^sub>s f)" "$y \<sharp> G"
  shows "\<^bold>{P \\ $y\<^bold>} (g_orbital_on x (\<lambda>t. f) G U S 0) \<^bold>{Q \\ $y\<^bold>}"
  using hyp
    (* unfolding defs *)
  apply (clarsimp simp: fbox_g_orbital_on taut_def le_fun_def)
  apply (simp add: liberate_lens'[OF vwb_lens_mwb[OF y_hyps(1)]])
    (* simplifying notation *)
  using y_hyps apply expr_simp
  apply (subst (asm) lens_indep_comm[of x y, OF lens_indep_sym], expr_simp?)+
  apply expr_simp
  apply (subst (asm) lens_indep_comm[of y x], expr_simp?)+
  apply (expr_simp add: ivp_sols_def, clarsimp)
    (* proof *)
  apply (rename_tac s X t v)
  apply (erule_tac x="put\<^bsub>y\<^esub> s v" in allE, clarsimp)
  apply (drule_tac x="\<lambda>t. (X t, gen_sol t v)" in spec, elim conjE impE; (intro conjI)?)
  (* for S': subgoal for s X t v by (clarsimp simp add: lens_indep.lens_put_irr2 Pi_def image_iff) *)
     prefer 4 subgoal for s X t v
    apply (clarsimp simp: lens_indep.lens_put_irr2 )
    apply (erule_tac x=t in ballE; clarsimp?)
    apply (subst (asm) lens_indep_comm[of x y, OF lens_indep_sym], expr_simp)+
    by expr_auto
    prefer 3 subgoal for s X t by (simp add: lens_indep.lens_put_irr2)
    prefer 2 subgoal for s X t by (simp add: lens_indep.lens_put_irr2 gen_sol_def)
  apply expr_simp
  apply (rule vderiv_pairI, force simp: lens_indep.lens_put_irr2)
   apply (subgoal_tac "D (\<lambda>t. gen_sol t v) 
  = (\<lambda>t. A *\<^sub>V (gen_sol t v) + b) on (U (get\<^bsub>x\<^esub> (put\<^bsub>y\<^esub> s v)))", assumption)
  subgoal for s X t
    unfolding gen_sol_def
    by (rule has_vderiv_on_subset[OF
        local_flow.has_vderiv_on_domain[OF
          local_flow_sq_mtx_affine, of _ "A" "b"]]; expr_simp)
  by (auto simp: lens_indep.lens_put_irr2 tsubst2vecf_eq
      lens_indep_comm[of x y, OF lens_indep_sym])

lemma diff_ghost_rule:
  fixes b :: "real ^ 'n" 
  assumes hyp: "\<^bold>{P\<^bold>} (g_orbital_on (x +\<^sub>L y) (\<lambda>t. f(y \<leadsto> (\<guillemotleft>A\<guillemotright> *\<^sub>V ($y) + \<guillemotleft>b\<guillemotright>))) G (U \<circ> fst) UNIV 0) \<^bold>{Q'\<^bold>}"
    and y_hyps: "vwb_lens y" "y \<bowtie> x" "($y \<sharp>\<^sub>s f)" "$y \<sharp> G" and q_eq: "Q = Q' \\ $y"
  shows "\<^bold>{P\<^bold>} (g_orbital_on x (\<lambda>t. f) G U S 0) \<^bold>{Q\<^bold>}"
  unfolding SEXP_def q_eq
  apply (rule order.trans[OF _ diff_ghost_gen_rule[OF hyp y_hyps, where S=S, unfolded SEXP_def]])
  by (clarsimp simp add: liberate_lens'[OF vwb_lens_mwb[OF y_hyps(1)]] le_fun_def)
    (metis lens_override_def lens_override_idem y_hyps(1))

lemma diff_ghost_inv_rule:
  fixes b :: "real ^ 'n"
  assumes inv_hyp: "diff_inv_on (x +\<^sub>L y) (\<lambda>t. f(y \<leadsto> (\<guillemotleft>A\<guillemotright> *\<^sub>V ($y) + \<guillemotleft>b\<guillemotright>))) G (U \<circ> fst) UNIV 0 (J)\<^sub>e"
    and y_hyps: "vwb_lens y" "y \<bowtie> x" "($y \<sharp>\<^sub>s f)" "$y \<sharp> G" and I_eq: "I = (J \\ $y)"
  shows "diff_inv_on x (\<lambda>t. f) G U S 0 I"
  using inv_hyp unfolding hoare_diff_inv_on[symmetric] SEXP_def I_eq
  by (rule diff_ghost_gen_rule[OF _ y_hyps, unfolded SEXP_def])

lemma has_vderiv_linear:
  fixes k :: real and b :: "'b :: real_normed_vector"
  assumes "k \<noteq> 0"
  defines "sol \<equiv> (\<lambda>s t. (- b + exp (k * t) *\<^sub>R (b + k *\<^sub>R s))/\<^sub>R k)"
  shows "D (sol s) = (\<lambda>t. k *\<^sub>R (sol s t) + b) on S"
  using assms unfolding sol_def
  by (auto simp: field_simps intro!: vderiv_intros)

lemma diff_ghost_gen_1rule:
  fixes b :: "'d :: real_normed_vector" and k :: real
  fixes x :: "'c :: real_normed_vector \<Longrightarrow> 's"
  defines "sol \<equiv> (\<lambda>s t. (- b + exp (k * t) *\<^sub>R (b + k *\<^sub>R s))/\<^sub>R k)"
  assumes hyp: "\<^bold>{P\<^bold>} (g_orbital_on (x +\<^sub>L y) (\<lambda>t. f(y \<leadsto> (\<guillemotleft>k\<guillemotright> *\<^sub>R ($y) + \<guillemotleft>b\<guillemotright>))) G (U \<circ> fst) UNIV 0) \<^bold>{Q\<^bold>}" (* S' \<times> UNIV where S \<subseteq> S'*)
    and y_hyps: "vwb_lens y" "y \<bowtie> x" "($y \<sharp>\<^sub>s f)" "$y \<sharp> G"
  shows "\<^bold>{P \\ $y\<^bold>} (g_orbital_on x (\<lambda>t. f) G U S 0) \<^bold>{Q \\ $y\<^bold>}"
  using hyp
    (* unfolding defs *)
  apply (clarsimp simp: fbox_g_orbital_on taut_def le_fun_def)
  apply (simp add: liberate_lens'[OF vwb_lens_mwb[OF y_hyps(1)]])
    (* simplifying notation *)
  using y_hyps apply expr_simp
  apply (subst (asm) lens_indep_comm[of x y, OF lens_indep_sym], expr_simp?)+
  apply expr_simp
  apply (subst (asm) lens_indep_comm[of y x], expr_simp?)+
  apply (expr_simp add: ivp_sols_def, clarsimp)
    (* proof *)
  apply (cases "k \<noteq> 0")
  subgoal for s X t s'
  apply (erule allE[where x="put\<^bsub>y\<^esub> s s'"] impE; expr_simp)
  apply (drule_tac x="\<lambda>t. (X t, sol s' t)" in spec, elim conjE impE; (intro conjI)?)
  prefer 4 subgoal
    apply (clarsimp simp: lens_indep.lens_put_irr2 )
    apply (erule_tac x=t in ballE; clarsimp?)
    apply (subst (asm) lens_indep_comm[of x y, OF lens_indep_sym], expr_simp)+
    by expr_auto
    prefer 3 subgoal by (simp add: lens_indep.lens_put_irr2)
   prefer 2 subgoal by (simp_all add: lens_indep.lens_put_irr2 sol_def)
  apply expr_simp
  apply (rule vderiv_pairI, force simp: lens_indep.lens_put_irr2)
   apply (subgoal_tac "D (sol s') = (\<lambda>t. k *\<^sub>R (sol s' t) + b) on (U (get\<^bsub>x\<^esub> (put\<^bsub>y\<^esub> s s')))", assumption)
  subgoal unfolding sol_def by (rule has_vderiv_linear)
  by (auto simp: lens_indep.lens_put_irr2 tsubst2vecf_eq
      lens_indep_comm[of x y, OF lens_indep_sym])
  apply expr_simp
  subgoal for s X t s'
    apply (erule allE[where x="put\<^bsub>y\<^esub> s s'"] impE; expr_simp)
    apply (drule_tac x="\<lambda> t. (X t, t *\<^sub>R b + s')" in spec, elim conjE impE; (intro conjI)?)
       prefer 4 subgoal
      apply (clarsimp simp: lens_indep.lens_put_irr2 )
      apply (erule_tac x=t in ballE; clarsimp?)
      apply (subst (asm) lens_indep_comm[of x y, OF lens_indep_sym], expr_simp)+
      by expr_auto
    by (auto simp: expr_defs lens_indep.lens_put_irr2
        lens_indep_comm[of x y, OF lens_indep_sym] intro!: vderiv_intros)
  done

lemma diff_ghost_1rule:
  fixes b :: "'d :: real_normed_vector"
  assumes hyp: "\<^bold>{P\<^bold>} (g_orbital_on (x +\<^sub>L y) (\<lambda>t. f(y \<leadsto> (\<guillemotleft>k\<guillemotright> *\<^sub>R ($y) + \<guillemotleft>b\<guillemotright>))) G (U \<circ> fst) UNIV 0) \<^bold>{Q'\<^bold>}"
    and y_hyps: "vwb_lens y" "y \<bowtie> x" "($y \<sharp>\<^sub>s f)" "$y \<sharp> G" and Q_eq: "Q = Q' \\ $y"
  shows "\<^bold>{P\<^bold>} (g_orbital_on x (\<lambda>t. f) G U S 0) \<^bold>{Q\<^bold>}"
  unfolding SEXP_def Q_eq
  apply (rule order.trans[OF _ diff_ghost_gen_1rule[OF hyp y_hyps, where S=S, unfolded SEXP_def]])
  by (clarsimp simp add: liberate_lens'[OF vwb_lens_mwb[OF y_hyps(1)]] le_fun_def)
    (metis lens_override_def lens_override_idem y_hyps(1))

lemma diag_mult_eq_scaleR: "(\<d>\<i>\<a>\<g> i. k) *\<^sub>V s = k *\<^sub>R s"
  by (auto simp: vec_eq_iff sq_mtx_vec_mult_eq)

lemma \<comment> \<open>2 one-line proofs means there is a more general result \<close>
  fixes b :: "real ^ ('n::finite)" 
  assumes hyp: "\<^bold>{P\<^bold>} (g_orbital_on (x +\<^sub>L y) (\<lambda>t. f(y \<leadsto> (\<guillemotleft>k\<guillemotright> *\<^sub>R ($y) + \<guillemotleft>b\<guillemotright>))) G (U \<circ> fst) UNIV 0) \<^bold>{Q\<^bold>}"
    and y_hyps: "vwb_lens y" "y \<bowtie> x" "($y \<sharp>\<^sub>s f)" "$y \<sharp> G"
  shows "\<^bold>{P \\ $y\<^bold>} (g_orbital_on x (\<lambda>t. f) G U S 0) \<^bold>{Q \\ $y\<^bold>}"
  thm diff_ghost_gen_rule diff_ghost_gen_1rule
  \<comment> \<open> this also works: @{text "by (rule diff_ghost_gen_1rule[OF hyp y_hyps])"}\<close>
  by (rule diff_ghost_gen_rule[OF hyp[folded diag_mult_eq_scaleR] y_hyps])

lemma diff_ghost_inv_1rule:
  fixes b :: "'d :: real_normed_vector" 
  assumes inv_hyp: "diff_inv_on (x +\<^sub>L y) (\<lambda>t. f(y \<leadsto> \<guillemotleft>k\<guillemotright> *\<^sub>R $y + \<guillemotleft>c\<guillemotright>)) G (U \<circ> fst) UNIV 0 J"
    and y_hyps: "vwb_lens y" "y \<bowtie> x" "$y \<sharp>\<^sub>s f" "$y \<sharp> G" and I_eq: "I = J \\ $y"
  shows "diff_inv_on x (\<lambda>t. f) G U UNIV 0 I"
  using inv_hyp unfolding hoare_diff_inv_on[symmetric] SEXP_def I_eq
  by (rule diff_ghost_gen_1rule[OF _ y_hyps, unfolded SEXP_def])

lemma diff_ghost_inv_very_simple:
  assumes y_hyps: "vwb_lens y" "y \<bowtie> a" "$y \<sharp>\<^sub>s f" "$y \<sharp> G"
    and inv_hyp: "diff_inv_on (a +\<^sub>L y) (\<lambda>t. f(y \<leadsto> \<guillemotleft>k\<guillemotright> *\<^sub>R $y)) G (Collect ((\<le>) 0))\<^sub>e UNIV 0 (I)\<^sub>e"
  shows "diff_inv_on a (\<lambda>t. f) G (Collect ((\<le>) 0))\<^sub>e UNIV 0 (I \\ $y)\<^sub>e"
  using diff_ghost_inv_1rule[OF _ y_hyps, where c=0 and k=k]
  using inv_hyp
  by expr_simp

lemma diff_ghost_rule_very_simple:
  assumes inv_hyp:"\<^bold>{J\<^bold>} g_dl_ode_frame (a +\<^sub>L y) (f(y \<leadsto> \<guillemotleft>k\<guillemotright> *\<^sub>R $y)) G \<^bold>{J\<^bold>}"
    and y_hyps: "vwb_lens y" "y \<bowtie> a" "$y \<sharp>\<^sub>s f" "$y \<sharp> G"
    and I_eq:  "(I)\<^sub>e = J \\ $y" 
  shows "\<^bold>{I\<^bold>} g_dl_ode_frame a f G \<^bold>{I\<^bold>}"
  using assms
  by (metis SEXP_def diff_ghost_inv_very_simple fbox_diff_inv_on) 

no_notation Union ("\<mu>")


subsection \<open> Darboux rule \<close>

(* ongoing work *)
thm derivative_quotient_bound derivative_quotient_bound_left
thm gronwall_general gronwall_general_left

lemma strengthen: "`Q1 \<longrightarrow> Q2` \<Longrightarrow> P \<le> |X] Q1 \<Longrightarrow> P \<le> |X] Q2"
  by (expr_simp add: fbox_def le_fun_def)

lemma weaken: "`P1 \<longrightarrow> P2` \<Longrightarrow> P2 \<le> |X] Q \<Longrightarrow> P1 \<le> |X] Q"
  by (expr_auto add: fbox_def le_fun_def)

lemma get_put_put_indep:
  assumes vwbs: "vwb_lens y"
    and indeps: "z \<bowtie> y"
  shows "get\<^bsub>y\<^esub>
          (put\<^bsub>z\<^esub> 
            (put\<^bsub>y\<^esub> something expr4y) expr4z) = expr4y"
  by (metis indeps lens_indep.lens_put_irr2 mwb_lens_weak 
      vwb_lens_def vwbs weak_lens.put_get)

thm vderiv_composeI vderiv_compI

lemma has_vderiv_put:
  "bounded_linear (put\<^bsub>x\<^esub> s) \<Longrightarrow> D X = X' on T \<Longrightarrow> D (\<lambda>t. put\<^bsub>x\<^esub> s (X t)) = (\<lambda>t. put\<^bsub>x\<^esub> s (X' t)) on T"
  apply (subst comp_def[symmetric, where g=X])
  apply (rule_tac vderiv_compI, force, clarsimp)
  by (rule bounded_linear_imp_has_derivative, auto)

lemmas vderiv_putI = has_vderiv_put[THEN has_vderiv_on_eq_rhs]

lemma SEXP_const_fst: "(\<guillemotleft>P\<guillemotright>)\<^sub>e \<circ> fst = (\<guillemotleft>P\<guillemotright>)\<^sub>e"
  by expr_simp

lemma darboux: 
  fixes y :: "'b \<Longrightarrow> 'b :: banach"
  assumes y_hyps: "vwb_lens y" "y \<bowtie> x" "$y \<sharp>\<^sub>s f" "$y \<sharp> G"
  shows "(e \<ge> 0)\<^sub>e \<le> |g_dl_ode_frame x f G] (e \<ge> 0)"
  apply (rule diff_ghost_1rule)
  oops

lemma darboux: 
  fixes x y z :: "real \<Longrightarrow> ('a::real_normed_vector)"
    and e e' :: "'a \<Rightarrow> real"
    and g :: real
  assumes vwbs: "vwb_lens x" "vwb_lens y" "vwb_lens z" 
    and indeps: "y \<bowtie> x" "z \<bowtie> x" "z \<bowtie> y"
    and yGhost: "$y \<sharp>\<^sub>s f" "$y \<sharp> G" "(e \<ge> 0)\<^sub>e = (y > 0 \<and> e \<ge> 0)\<^sup>e \\ $y"
    and zGhost: "$z \<sharp>\<^sub>s f(y \<leadsto> - \<guillemotleft>g\<guillemotright> *\<^sub>R $y)" "$z \<sharp> (G)\<^sub>e" "(0 < y)\<^sub>e = (y*z\<^sup>2 = 1)\<^sup>e \\ $z"
    and dbx_hyp: "e' \<ge> (\<guillemotleft>g\<guillemotright> * e)\<^sub>e"
    and deriv: "\<And>s. D e \<mapsto> e' (at s)" "\<And>s. (\<lambda>c. e (put\<^bsub>x +\<^sub>L y\<^esub> s c)) differentiable (at (get\<^bsub>x +\<^sub>L y\<^esub> s))"
    and bdd_linear_gety: "bounded_linear get\<^bsub>y\<^esub>"
    and bdd_linear_put: "\<And>s. bounded_linear (put\<^bsub>x +\<^sub>L y\<^esub> s)"
  shows "(e \<ge> 0)\<^sub>e \<le> |g_dl_ode_frame x f G] (e \<ge> 0)"
  thm has_vderiv_on_iff
  apply (rule diff_ghost_rule_very_simple[where k="-g", OF _ vwbs(2) indeps(1) yGhost])
  apply (rule strengthen[of "(y > 0 \<and> e * y \<ge> 0)\<^sup>e"])
  using indeps apply (expr_simp, clarsimp simp add: zero_le_mult_iff) 
  apply (subst SEXP_def[symmetric, of G])
  apply (rule_tac C="(y > 0)\<^sup>e" in diff_cut_on_rule)
   apply (rule_tac weaken[of _ "(y > 0)\<^sub>e"])
  using indeps apply (expr_simp)
  apply (rule diff_ghost_rule_very_simple[where k="g/2", OF _ vwbs(3) _ zGhost])
    prefer 2 using indeps apply expr_simp
    apply (subst hoare_diff_inv_on)
  apply (rule diff_inv_on_raw_eqI; (clarsimp simp: lframe_subst_def)?)
  using vwbs indeps
    apply (meson lens_indep_sym plus_pres_lens_indep plus_vwb_lens) 
  using vwbs indeps apply (expr_simp add: lens_indep.lens_put_irr2)
   apply (intro vderiv_intros; force?)
   apply (rule has_vderiv_on_const[THEN has_vderiv_on_eq_rhs])
  using vwbs indeps apply (expr_simp add: power2_eq_square)
  apply (rule_tac I="\<lambda>\<s>. 0 \<le> e \<s> * $y" in fbox_diff_invI)
    prefer 3 apply (expr_simp add: le_fun_def)
   prefer 2 apply (expr_simp add: le_fun_def)
  apply (simp only: hoare_diff_inv_on fbox_diff_inv_on) (* proof correct up to here *)
  apply (subgoal_tac "vwb_lens (x +\<^sub>L y)")
   prefer 2 using assms(1-5) lens_indep_sym plus_vwb_lens apply blast

 (*  (* approach using deriv(2) *)
  apply (rule_tac \<nu>'="(0)\<^sup>e" in diff_inv_on_leqI; clarsimp?)
   prefer 2
   apply (rule_tac g'="\<lambda>t. get\<^bsub>y\<^esub> (put\<^bsub>x +\<^sub>L y\<^esub> s (get\<^bsub>x +\<^sub>L y\<^esub> ((f(y \<leadsto> - (\<guillemotleft>g\<guillemotright> * $y))) (put\<^bsub>x +\<^sub>L y\<^esub> s (X t)))))" in vderiv_intros(5))
     prefer 2 using vwbs indeps apply (expr_simp add: lens_indep.lens_put_irr2)
  using vderiv_sndI apply fastforce
    apply (clarsimp simp: has_vderiv_on_iff)
    apply (rule has_derivative_subset)
  using deriv(2)[unfolded differentiable_def] *)

  (* trying to make Isabelle give the solution, approach where I suggest solution below *)
 (* apply (rule_tac \<nu>'="(0)\<^sup>e" in diff_inv_on_leqI; clarsimp?)
   prefer 2
  term "e (put\<^bsub>x +\<^sub>L y\<^esub> s (X x)) * get\<^bsub>y\<^esub> (put\<^bsub>x +\<^sub>L y\<^esub> s (X x))"
  thm vderiv_intros(5)
   apply (rule_tac vderiv_intros(5))
      apply (rule vderiv_compI[unfolded comp_def, where f=e and g="\<lambda>\<tau>. put\<^bsub>x +\<^sub>L y\<^esub> _ (_ \<tau>)"])
        apply (rule vderiv_putI[OF bdd_linear_put]; force)
      apply (rule ballI, rule has_derivative_subset[OF deriv(1)], force, force)
     apply (rule vderiv_compI[unfolded comp_def, where f="get\<^bsub>y\<^esub>" and g="\<lambda>t. put\<^bsub>x +\<^sub>L y\<^esub> _ (_ t)"])
      apply (rule vderiv_putI[OF bdd_linear_put]; force)
     apply (subst bdd_linear_iff_has_derivative[symmetric])
  using bdd_linear_gety apply (force, force)
  term "\<lambda>s'. e s' * get\<^bsub>y\<^esub> (put\<^bsub>x +\<^sub>L y\<^esub> s (get\<^bsub>x +\<^sub>L y\<^esub> (put\<^bsub>y\<^esub> (f s') (- (g * get\<^bsub>y\<^esub> s'))))) +
       e' (put\<^bsub>x +\<^sub>L y\<^esub> s (get\<^bsub>x +\<^sub>L y\<^esub> (put\<^bsub>y\<^esub> (f s') (- (g * get\<^bsub>y\<^esub> s'))))) * get\<^bsub>y\<^esub> s'"
  using wb_lens.get_put[of "x +\<^sub>L y"] weak_lens.put_get[of "x +\<^sub>L y"] lens_plus_def
    using assms(1-5) yGhost(1) (* lens_indep_sym plus_vwb_lens *)
    apply (expr_simp add: lens_indep.lens_put_irr2)
     apply (subst lens_indep_comm[of x y, OF lens_indep_sym]; expr_simp?)
     apply (subst lens_indep_comm[of x y, OF lens_indep_sym]; expr_simp?)

    apply (expr_simp add: lens_indep.lens_put_irr2)

    oops *)

  (* approach where I suggest solution *)
  apply (rule_tac \<nu>'="(0)\<^sup>e" and \<mu>'="(e' * y + e * (- \<guillemotleft>g\<guillemotright> *\<^sub>R y))\<^sup>e" in diff_inv_on_leqI; clarsimp?)
  using indeps dbx_hyp apply (expr_simp add: le_fun_def mult.commute)
  subgoal for X s
    apply (rule_tac vderiv_intros(5))
      apply (rule vderiv_compI[unfolded comp_def, where f=e and g="\<lambda>\<tau>. put\<^bsub>x +\<^sub>L y\<^esub> s (X \<tau>)"])
        apply (rule vderiv_putI[OF bdd_linear_put]; force)
       apply (rule ballI, rule has_derivative_subset[OF deriv(1)], force, force)
     apply (rule vderiv_compI[unfolded comp_def, where f="get\<^bsub>y\<^esub>" and g="\<lambda>t. put\<^bsub>x +\<^sub>L y\<^esub> s (X t)"])
       apply (rule vderiv_putI[OF bdd_linear_put]; force)
      apply (subst bdd_linear_iff_has_derivative[symmetric])
    using bdd_linear_gety apply (force, force)
    using assms(1-5) yGhost(1) (* lens_indep_sym plus_vwb_lens *)
    apply (expr_simp add: lens_indep.lens_put_irr2)
    apply (subst lens_indep_comm[of x y, OF lens_indep_sym], expr_simp?)+
    apply (subst (asm) lens_indep_comm[of x y, OF lens_indep_sym], expr_simp?)+
    apply (expr_simp add: lens_indep.lens_put_irr2)
    using weak_lens.put_get
    using bdd_linear_gety bdd_linear_put
    find_theorems name: put_get
    find_theorems name: get_put

    thm at_within_open_subset (* needs *)
      at_le at_within_open (* needs *)
      filter_eq_iff eventually_at_topological (* needs *)
      eventually_nhds eventually_at_filter (* needs *)
      (* unfold *) nhds_def 
      (* subst *) eventually_INF_base 
      (* auto simp: *) eventually_principal
    oops

lemma darboux_geq: 
  fixes y z :: "real \<Longrightarrow> 'a"
    and e e' :: "'a \<Rightarrow> real"
    and g :: real
  assumes vwbs: "vwb_lens a" "vwb_lens y" "vwb_lens z" 
    and indeps: "y \<bowtie> a" "z \<bowtie> a" "z \<bowtie> y"
    and yGhost: "$y \<sharp>\<^sub>s f" "$y \<sharp> G" "(e \<ge> 0)\<^sub>e = (y > 0 \<and> e \<ge> 0)\<^sup>e \\ $y"
    and zGhost: "$z \<sharp>\<^sub>s f(y \<leadsto> - \<guillemotleft>g\<guillemotright> *\<^sub>R $y)" "$z \<sharp> (G)\<^sub>e"
    and dbx_hyp: "(\<D>\<^bsub>a +\<^sub>L y\<^esub>\<langle>f(y \<leadsto> - \<guillemotleft>g\<guillemotright> * $y)\<rangle> e) \<ge> (\<guillemotleft>g\<guillemotright> * e)\<^sub>e"
    and deriv: "differentiable\<^sub>e e on (a +\<^sub>L y)"
  shows "(e \<ge> 0)\<^sub>e \<le> |g_dl_ode_frame a f G] (e \<ge> 0)"
  apply (rule diff_ghost_rule_very_simple[where k="-g", OF _ vwbs(2) indeps(1) yGhost])
  apply (rule strengthen[of "(y > 0 \<and> e * y \<ge> 0)\<^sup>e"])
  using indeps apply (expr_simp, clarsimp simp add: zero_le_mult_iff) 
  apply (subst SEXP_def[symmetric, of G])
  apply (rule_tac C="(y > 0)\<^sup>e" in diff_cut_on_rule)
   apply (rule_tac weaken[of _ "(y > 0)\<^sub>e"])
  using indeps apply (expr_simp)
  apply (rule diff_ghost_rule_very_simple[where k="g/2" and J="($y * ($z)\<^sup>2 = 1)\<^sup>e", OF _ vwbs(3) _ zGhost])
    prefer 2 using indeps apply expr_simp
    apply (subst hoare_diff_inv_on)
  apply (rule diff_inv_on_raw_eqI; (clarsimp simp: tsubst2vecf_eq)?)
  using vwbs indeps
    apply (meson lens_indep_sym plus_pres_lens_indep plus_vwb_lens) 
  using vwbs indeps apply (expr_simp add: lens_indep.lens_put_irr2)
   apply (intro vderiv_intros; force?)
   apply (rule has_vderiv_on_const[THEN has_vderiv_on_eq_rhs])
  using vwbs indeps apply (expr_simp add: power2_eq_square)
  using vwbs indeps apply expr_auto
     apply (rule_tac x="put\<^bsub>z\<^esub> x (1/sqrt (get\<^bsub>y\<^esub> x))" in exI, expr_simp add: field_simps lens_indep.lens_put_irr2)
    apply (expr_simp add: lens_indep.lens_put_irr2)
  apply (metis power2_less_0 zero_less_mult_iff zero_less_one)
  apply (rule_tac I="\<lambda>\<s>. 0 \<le> e \<s> * $y" in fbox_diff_invI)
    prefer 3 apply (expr_simp add: le_fun_def)
   prefer 2 apply (expr_simp add: le_fun_def)
  apply (simp only: hoare_diff_inv_on fbox_diff_inv_on)
  apply (subgoal_tac "vwb_lens (a +\<^sub>L y)")
  prefer 2 using vwbs indeps
    apply (meson lens_indep_sym plus_pres_lens_indep plus_vwb_lens) 
  using vwbs indeps deriv apply - 
  apply(rule ldiff_inv_on_le_rule; clarsimp?)
    apply (rule differentiable_times; clarsimp?)
     apply (rule differentiable_cvar; (clarsimp simp: indeps(1) lens_indep_sym vwbs(1))?)
    apply expr_simp
   apply (subst lframeD_zero)
   apply (subst lframeD_times; clarsimp?)
   apply (rule differentiable_cvar; (clarsimp simp: indeps(1) lens_indep_sym vwbs(1))?)
  apply (subst lframeD_cont_var; (clarsimp simp: indeps(1) lens_indep_sym vwbs(1))?)
  using yGhost(1,2) indeps vwbs dbx_hyp apply expr_simp
  by (clarsimp simp: framed_derivs ldifferentiable usubst 
      unrest_ssubst unrest usubst_eval le_fun_def mult.commute)

lemma darboux_ge: 
  fixes y z :: "real \<Longrightarrow> 'a"
    and e e' :: "'a \<Rightarrow> real"
    and g :: real
  assumes vwbs: "vwb_lens a" "vwb_lens y" "vwb_lens z" 
    and indeps: "y \<bowtie> a" "z \<bowtie> a" "z \<bowtie> y"
    and yGhost: "$y \<sharp>\<^sub>s f" "$y \<sharp> G" "(e > 0)\<^sub>e = (y > 0 \<and> e > 0)\<^sup>e \\ $y"
    and zGhost: "$z \<sharp>\<^sub>s f(y \<leadsto> - \<guillemotleft>g\<guillemotright> *\<^sub>R $y)" "$z \<sharp> (G)\<^sub>e"
    and dbx_hyp: "(\<D>\<^bsub>a +\<^sub>L y\<^esub>\<langle>f(y \<leadsto> - \<guillemotleft>g\<guillemotright> * $y)\<rangle> e) \<ge> (\<guillemotleft>g\<guillemotright> * e)\<^sub>e"
    and deriv: "differentiable\<^sub>e e on (a +\<^sub>L y)"
  shows "(e > 0)\<^sub>e \<le> |g_dl_ode_frame a f G] (e > 0)"
  apply (rule diff_ghost_rule_very_simple[where k="-g", OF _ vwbs(2) indeps(1) yGhost])
  apply (rule strengthen[of "(y > 0 \<and> e * y > 0)\<^sup>e"])
  using indeps apply (expr_simp, clarsimp simp add: zero_less_mult_iff) 
  apply (subst SEXP_def[symmetric, of G])
  apply (rule_tac C="(y > 0)\<^sup>e" in diff_cut_on_rule)
   apply (rule_tac weaken[of _ "(y > 0)\<^sub>e"])
  using indeps apply (expr_simp)
  apply (rule diff_ghost_rule_very_simple[where k="g/2" and J="($y * ($z)\<^sup>2 = 1)\<^sup>e", OF _ vwbs(3) _ zGhost])
    prefer 2 using indeps apply expr_simp
    apply (subst hoare_diff_inv_on)
  apply (rule diff_inv_on_raw_eqI; (clarsimp simp: tsubst2vecf_eq)?)
  using vwbs indeps
    apply (meson lens_indep_sym plus_pres_lens_indep plus_vwb_lens) 
  using vwbs indeps apply (expr_simp add: lens_indep.lens_put_irr2)
   apply (intro vderiv_intros; force?)
   apply (rule has_vderiv_on_const[THEN has_vderiv_on_eq_rhs])
  using vwbs indeps apply (expr_simp add: power2_eq_square)
  using vwbs indeps apply expr_auto
     apply (rule_tac x="put\<^bsub>z\<^esub> x (1/sqrt (get\<^bsub>y\<^esub> x))" in exI, expr_simp add: field_simps lens_indep.lens_put_irr2)
    apply (expr_simp add: lens_indep.lens_put_irr2)
  apply (metis power2_less_0 zero_less_mult_iff zero_less_one)
  apply (rule_tac I="\<lambda>\<s>. 0 < e \<s> * $y" in fbox_diff_invI)
    prefer 3 apply (expr_simp add: le_fun_def)
   prefer 2 apply (expr_simp add: le_fun_def)
  apply (simp only: hoare_diff_inv_on fbox_diff_inv_on)
  apply (subgoal_tac "vwb_lens (a +\<^sub>L y)")
  prefer 2 using vwbs indeps
    apply (meson lens_indep_sym plus_pres_lens_indep plus_vwb_lens) 
  using vwbs indeps deriv apply - 
  apply(rule ldiff_inv_on_less_rule; clarsimp?)
    apply (rule differentiable_times; clarsimp?)
     apply (rule differentiable_cvar; (clarsimp simp: indeps(1) lens_indep_sym vwbs(1))?)
    apply expr_simp
   apply (subst lframeD_zero)
   apply (subst lframeD_times; clarsimp?)
   apply (rule differentiable_cvar; (clarsimp simp: indeps(1) lens_indep_sym vwbs(1))?)
  apply (subst lframeD_cont_var; (clarsimp simp: indeps(1) lens_indep_sym vwbs(1))?)
  using yGhost(1,2) indeps vwbs dbx_hyp apply expr_simp
  by (clarsimp simp: framed_derivs ldifferentiable usubst 
      unrest_ssubst unrest usubst_eval le_fun_def mult.commute)

lemma darboux_eq: 
  fixes y z :: "'v::{real_inner, banach, real_normed_algebra_1, division_ring} \<Longrightarrow> 'a"
    and e e' :: "'a \<Rightarrow> 'v"
  assumes vwbs: "vwb_lens a" "vwb_lens y" "vwb_lens z" 
    and indeps: "y \<bowtie> a" "z \<bowtie> a" "z \<bowtie> y"
    and yGhost: "$y \<sharp>\<^sub>s f" "$y \<sharp> G" "(e = 0)\<^sub>e = (y \<noteq> 0 \<and> e * y = 0)\<^sup>e \\ $y"
    and zGhost: "$z \<sharp>\<^sub>s f(y \<leadsto> - \<guillemotleft>g\<guillemotright> *\<^sub>R $y)" "$z \<sharp> (G)\<^sub>e"
    and dbx_hyp: "(\<D>\<^bsub>a +\<^sub>L y\<^esub>\<langle>f(y \<leadsto> - \<guillemotleft>g\<guillemotright> *\<^sub>R $y)\<rangle> e) = (\<guillemotleft>g\<guillemotright> *\<^sub>R e)\<^sub>e"
    and deriv: "differentiable\<^sub>e e on (a +\<^sub>L y)"
  shows "(e = 0)\<^sub>e \<le> |g_dl_ode_frame a f G] (e = 0)"
  apply (rule diff_ghost_rule_very_simple[where k="-g", OF _ vwbs(2) indeps(1) yGhost])
  apply (rule strengthen[of "(y \<noteq> 0 \<and> e * y = 0)\<^sup>e"])
  using indeps apply (expr_auto add: zero_less_mult_iff)
  apply (subst SEXP_def[symmetric, of G])
  apply (rule_tac C="(y \<noteq> 0)\<^sup>e" in diff_cut_on_rule)
   apply (rule_tac weaken[of _ "(y \<noteq> 0)\<^sub>e"])
  using indeps apply (expr_simp)
  apply (rule diff_ghost_rule_very_simple[where k="g" and J="($y * $z = 1)\<^sup>e", OF _ vwbs(3) _ zGhost])
    prefer 2 using indeps apply expr_simp
   apply (subst hoare_diff_inv_on)
  apply (rule diff_inv_on_raw_eqI; (clarsimp simp: tsubst2vecf_eq)?)
  using vwbs indeps
    apply (meson lens_indep_sym plus_pres_lens_indep plus_vwb_lens) 
  using vwbs indeps apply (expr_simp add: lens_indep.lens_put_irr2)
    apply (intro vderiv_intros; force?)
   apply (rule has_vderiv_on_const[THEN has_vderiv_on_eq_rhs])
  using vwbs indeps apply (expr_simp add: power2_eq_square)
  using vwbs indeps apply expr_auto
     apply (rule_tac x="put\<^bsub>z\<^esub> x (1/get\<^bsub>y\<^esub> x)" in exI, expr_simp add: field_simps lens_indep.lens_put_irr2)
    apply (expr_simp add: lens_indep.lens_put_irr2)

  apply (rule_tac I="\<lambda>\<s>. 0 = e \<s> * $y" in fbox_diff_invI)
    prefer 3 apply (expr_auto add: le_fun_def)
   prefer 2 apply (expr_auto add: le_fun_def)
  apply (simp only: hoare_diff_inv_on fbox_diff_inv_on)
  apply (subgoal_tac "vwb_lens (a +\<^sub>L y)")
  prefer 2 using vwbs indeps
    apply (meson lens_indep_sym plus_pres_lens_indep plus_vwb_lens) 
  using vwbs indeps deriv apply - 
  apply(rule ldiff_inv_on_eq_rule; clarsimp?)
    apply (simp add: framed_derivs ldifferentiable)
    apply (rule differentiable_times; clarsimp?)
   apply (rule differentiable_cvar; (clarsimp simp: indeps(1) lens_indep_sym vwbs(1))?)
  apply (subst lframeD_zero)
   apply (subst lframeD_times; clarsimp?)
   apply (rule differentiable_cvar; (clarsimp simp: indeps(1) lens_indep_sym vwbs(1))?)
  apply (subst lframeD_cont_var; (clarsimp simp: indeps(1) lens_indep_sym vwbs(1))?)
  using yGhost(1,2) indeps vwbs dbx_hyp by expr_simp

end