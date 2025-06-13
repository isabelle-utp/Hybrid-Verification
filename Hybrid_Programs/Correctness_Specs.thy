(*  Title: HS verification with lenses *)

section \<open> HS verification with lenses \<close>

text \<open> We use shallow expressions to rephrase hybrid systems properties. Each operator below 
includes lemmas for verification condition generation. \<close>

theory Correctness_Specs
  imports "Shallow_Expressions.Shallow_Expressions"

begin

type_synonym 'a pred = "'a \<Rightarrow> bool"
type_synonym 's prog = "'s \<Rightarrow> 's set"

notation Union ("\<mu>")

lemma impl_eq_leq: "`@P \<longrightarrow> @Q` = (P \<le> Q)"
  by (auto simp: taut_def)

lemma pred_iffI: 
  "`P \<longrightarrow> Q` \<Longrightarrow> `Q \<longrightarrow> P` \<Longrightarrow> P = Q"
  "`P \<longrightarrow> Q` \<Longrightarrow> `Q \<longrightarrow> P` \<Longrightarrow> `P \<longleftrightarrow> Q`"
  by expr_auto+

lemma pred_conjI: "`P` \<Longrightarrow> `Q` \<Longrightarrow> `P \<and> Q`"
  by expr_auto+


subsection \<open> Forward box operator \<close>

named_theorems prog_defs

named_theorems wlp "simplification rules for equational reasoning with weakest liberal preconditions"

definition fbox :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'b pred \<Rightarrow> 'a pred"
  where "fbox F P = (\<lambda>s. (\<forall>s'. s' \<in> F s \<longrightarrow> P s'))"

syntax "_fbox" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("|_] _" [0,81] 82)
translations "_fbox F P" == "CONST fbox F (P)\<^sub>e"

expr_constructor fbox

lemma clarify_fbox: "|F] P = fbox F P"
  by (clarsimp simp: fbox_def)

lemma fbox_iso: "P \<le> Q \<Longrightarrow> |F] P \<le> |F] Q"
  unfolding fbox_def by auto

lemma fbox_mono: 
  "( |F] P) s \<Longrightarrow> `P \<longrightarrow> Q` \<Longrightarrow> ( |F] Q) s"
  "`P \<longrightarrow> Q` \<Longrightarrow> `|F] P \<longrightarrow> |F] Q`"
  "`P \<longrightarrow> Q` \<Longrightarrow> `|F] P` \<Longrightarrow> `|F] Q`"
  by (auto simp: taut_def fbox_def)

lemma fbox_anti: "\<forall>s. F\<^sub>1 s \<subseteq> F\<^sub>2 s \<Longrightarrow> |F\<^sub>2] P \<le> |F\<^sub>1] P"
  unfolding fbox_def by auto


subsection \<open> Forward diamond operator \<close>

definition fdia :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'b pred \<Rightarrow> 'a pred"
  where "fdia F P = (\<lambda>s. (\<exists>s'. s' \<in> F s \<and> P s'))"

expr_constructor fdia

syntax "_fdia" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("|_\<rangle> _" [0,81] 82)
translations "_fdia F P" == "CONST fdia F (P)\<^sub>e"

lemma clarify_fdia: "|F\<rangle> P = fdia F P"
  by (clarsimp simp: fdia_def)

lemma fdia_iso: "P \<le> Q \<Longrightarrow> |F\<rangle> P \<le> |F\<rangle> Q"
  unfolding fdia_def by auto

lemma fdia_mono: 
  "( |F\<rangle> P) s \<Longrightarrow> `P \<longrightarrow> Q` \<Longrightarrow> ( |F\<rangle> Q) s"
  "`P \<longrightarrow> Q` \<Longrightarrow> `|F\<rangle> P \<longrightarrow> |F\<rangle> Q`"
  "`P \<longrightarrow> Q` \<Longrightarrow> `|F\<rangle> P` \<Longrightarrow> `|F\<rangle> Q`"
  by (auto simp: taut_def fdia_def) blast

lemma determ_fdia_fboxI: "\<forall>s. \<exists>s'. F s \<subseteq> {s'} \<Longrightarrow> |F\<rangle> Q \<le> |F] Q"
  using subset_singletonD
  by (auto simp: fdia_def fbox_def taut_def)
    fastforce


subsection \<open> Backward diamond operator \<close>

definition bdia :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a pred \<Rightarrow> 'b pred"
  where "bdia F P = (\<lambda>s'. (\<exists>s. s' \<in> F s \<and> P s))"

expr_constructor bdia

syntax "_bdia" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("\<langle>_| _" [0,81] 82)
translations "_bdia F P" == "CONST bdia F (P)\<^sub>e"

lemma clarify_bdia: "\<langle>F| P = bdia F P"
  by (clarsimp simp: bdia_def)

lemma bdia_iso: "P \<le> Q \<Longrightarrow> \<langle>F| P \<le> \<langle>F| Q"
  unfolding bdia_def by auto

lemma bdia_mono: 
  "( \<langle>F| P) s \<Longrightarrow> `P \<longrightarrow> Q` \<Longrightarrow> ( \<langle>F| Q) s"
  "`P \<longrightarrow> Q` \<Longrightarrow> `\<langle>F| P \<longrightarrow> \<langle>F| Q`"
  "`P \<longrightarrow> Q` \<Longrightarrow> `\<langle>F| P` \<Longrightarrow> `\<langle>F| Q`"
  by (auto simp: taut_def bdia_def) blast

(* galois connection: f(P) \<le> Q \<longleftrightarrow> P \<le> g(Q).  *)
lemma bdia_dual_fbox: "( \<langle>F| P \<le> Q) \<longleftrightarrow> P \<le> |F] Q"
  by (auto simp: bdia_def fbox_def)

(* TODO: Define incorrectness logic triple (under-approximation) \<langle>P\<rangle> F \<langle>Q\<rangle> \<longleftrightarrow> Q \<le> \<langle>F| P *)
(* That is, Q implies the "strongest (liberal) precondition" *)
(* Recall that, in contrast, {P} F {Q} states that Q is an over-approximation: \<langle>F| P \<le> Q *)
(* In this setting, if Q is something we want to avoid, then showing \<langle>P\<rangle> F \<langle>Q\<rangle> means 
noticing that P is a condition that might lead to Q, and thus we might want to avoid it 
too (\<forall>s'. Q s' \<longrightarrow> (\<exists>s. s' \<in> F s \<and> P s)). *)


subsection \<open> Hoare triple \<close>

syntax
  "_hoare" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(2H{_} /_) /{_}")

translations
  "H{p} S {q}" == "(p)\<^sub>e \<le> |S] q"

lemma fbox_to_hoare: "P \<le> |F] Q \<longleftrightarrow> H{P} F {Q}"
  by auto

ML_file \<open>Spec_Utils.ML\<close>

text \<open> Need to generalise these laws \<close>

lemma hoare_conj_preI: 
  "H{@a}X{@Q} \<Longrightarrow> P = (@a \<and> @b)\<^sub>e \<Longrightarrow> H{@P}X{@Q}"
  by (auto simp: fun_eq_iff)

lemma hoare_conj_posI: 
  "H{@P}X{@a} \<Longrightarrow> H{@P}X{@b} \<Longrightarrow> Q = (@a \<and> @b)\<^sub>e \<Longrightarrow> H{@P}X{@Q}"
  by (auto simp: fun_eq_iff fbox_def)

lemma hoare_conj_pos: 
  "(H{@P} X {@Q1 \<and> @Q2}) = (H{@P} X {@Q1} \<and> H{@P} X {@Q2})"
  by (auto simp: fbox_def)

lemma hoare_disj_preI:
  "H{@a \<and> @b}X{@Q} \<Longrightarrow> H{@a \<and> @c}X{@Q} \<Longrightarrow> P = (@a \<and> (@b \<or> @c))\<^sub>e \<Longrightarrow> H{@P}X{@Q}"
  by (auto simp: le_fun_def fbox_def)

lemma hoare_disj_posI: 
  "H{P}X{a} \<Longrightarrow> Q = (a \<or> b)\<^sub>e \<Longrightarrow> H{P}X{Q}"
  by (auto simp: le_fun_def fbox_def)

lemma hoare_neg_cases: 
  "H{@p \<and> I}S{@p \<and> I} \<Longrightarrow> H{\<not> @p \<and> I}S{\<not> @p \<and> I} \<Longrightarrow> H{I}S{I}"
  by (auto simp: fbox_def SEXP_def)

lemma hoare_post_invariant:
  assumes "H{I} C {I}" "`P \<longrightarrow> I`"
  shows "H{P} C {I}"
  by (metis SEXP_def assms(1,2) order.trans refine_iff_implies)

lemma fbox_conseq:
  assumes "P\<^sub>2 \<le> |X] Q\<^sub>2" "`P\<^sub>1 \<longrightarrow> P\<^sub>2`" "`Q\<^sub>2 \<longrightarrow> Q\<^sub>1`"
  shows "P\<^sub>1 \<le> |X] Q\<^sub>1"
  using assms 
  by (auto simp add: fbox_def expr_defs)

lemma hoare_conseq: 
  assumes "H{p\<^sub>2}S{q\<^sub>2}" "`p\<^sub>1 \<longrightarrow> p\<^sub>2`" "`q\<^sub>2 \<longrightarrow> q\<^sub>1`"
  shows "H{p\<^sub>1}S{q\<^sub>1}"
  using assms 
  by (auto simp add: fbox_def expr_defs)

lemma hoare_invariant:
  assumes "H{I} S {I}" "`P \<longrightarrow> I`" "`I \<longrightarrow> Q`"
  shows "H{P} S {Q}"
  using assms by (fact hoare_conseq)

lemma fdia_conseq:
  assumes "P\<^sub>2 \<le> |X\<rangle> Q\<^sub>2" "`P\<^sub>1 \<longrightarrow> P\<^sub>2`" "`Q\<^sub>2 \<longrightarrow> Q\<^sub>1`"
  shows "P\<^sub>1 \<le> |X\<rangle> Q\<^sub>1"
  using assms 
  by (auto simp add: fdia_def expr_defs)
    blast


subsection \<open> Program invariants \<close>

lemma fbox_inv:
  assumes "P \<le> I" and "I \<le> |F] I" and "I \<le> Q"
  shows "P \<le> |F] Q"
  by (rule order.trans[OF assms(1) order.trans[OF assms(2)]])
    (rule fbox_iso[OF assms(3)])

lemma fdia_inv:
  assumes "P \<le> I" and "I \<le> |F\<rangle> I" and "I \<le> Q"
  shows "P \<le> |F\<rangle> Q"
  apply (rule fdia_conseq[OF assms(2)])
  using assms by expr_auto+

lemma fbox_invs: 
  assumes "(I)\<^sub>e \<le> |F] I" and "(J)\<^sub>e \<le> |F] J"
  shows "(I \<and> J)\<^sub>e \<le> |F] (I \<and> J)"
    and "(I \<or> J)\<^sub>e \<le> |F] (I \<or> J)"
  using assms unfolding fbox_def SEXP_def by auto

lemmas fbox_invs_raw = fbox_invs[unfolded expr_defs]

lemma hoare_invs:
  assumes "H{I\<^sub>1}F{I\<^sub>1}" and "H{I\<^sub>2}F{I\<^sub>2}"
  shows hoare_conj_inv: "H{I\<^sub>1 \<and> I\<^sub>2}F{I\<^sub>1 \<and> I\<^sub>2}"
    and hoare_disj_inv: "H{I\<^sub>1 \<or> I\<^sub>2}F{I\<^sub>1 \<or> I\<^sub>2}" 
  using fbox_invs[OF assms] by auto

lemma hoare_disj_split:
  "H{P} F {R} \<Longrightarrow> H{Q} F {R} \<Longrightarrow> H{P \<or> Q} F {R}"
  unfolding fbox_def by (auto simp add: le_fun_def)

definition invar :: "('a \<Rightarrow> 'a set) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a set)"
  where "invar F I \<equiv> F"

expr_constructor fdia

syntax "_invar" :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infix "INV" 63)
translations "_invar F I" == "CONST invar F (I)\<^sub>e"

lemma insert_invar: "F = (F INV I)"
  by (simp add: invar_def)

lemma change_invar: "(F INV I) = (F INV J)"
  by (simp add: invar_def)

lemma conj_invar: "(F INV I) = (F INV (I \<and> J))"
  by (simp add: invar_def)

lemma fbox_invI:
  assumes "P \<le> I" and "I \<le> |F] I" and "I \<le> Q"
  shows "P \<le> |F INV I] Q"
  using fbox_inv[OF assms]
  by (auto simp: invar_def)

lemma fdia_invI:
  assumes "P \<le> I" and "I \<le> |F\<rangle> I" and "I \<le> Q"
  shows "P \<le> |F INV I\<rangle> Q"
  unfolding invar_def
  by (rule fdia_inv[OF assms])


end