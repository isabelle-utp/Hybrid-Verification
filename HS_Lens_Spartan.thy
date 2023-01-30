(*  Title: HS verification with lenses *)

section \<open> HS verification with lenses \<close>

text \<open> We use shallow expressions to rephrase hybrid systems properties. Each operator below 
includes lemmas for verification condition generation. \<close>

theory HS_Lens_Spartan
  imports 
    "HS_Lens_ODEs"
    "Matrices/MTX_Flows"

begin

type_synonym 'a pred = "'a \<Rightarrow> bool"
type_synonym 's prog = "'s \<Rightarrow> 's set"

no_notation Transitive_Closure.rtrancl ("(_\<^sup>*)" [1000] 999)

notation Union ("\<mu>")

lemma impl_eq_leq: "`@P \<longrightarrow> @Q` = (P \<le> Q)"
  by (auto simp: taut_def)


subsection \<open> Forward box operator \<close>

named_theorems prog_defs

named_theorems wp "simplification rules for equational reasoning with weakest liberal preconditions"

definition fbox :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'b pred \<Rightarrow> 'a pred"
  where "fbox F P = (\<lambda>s. (\<forall>s'. s' \<in> F s \<longrightarrow> P s'))"

syntax "_fbox" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("|_] _" [0,81] 82)
translations "_fbox F P" == "CONST fbox F (P)\<^sub>e"

expr_ctr fbox

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

lemma fbox_invs: 
  assumes "(I)\<^sub>e \<le> |F] I" and "(J)\<^sub>e \<le> |F] J"
  shows "(I \<and> J)\<^sub>e \<le> |F] (I \<and> J)"
    and "(I \<or> J)\<^sub>e \<le> |F] (I \<or> J)"
  using assms unfolding fbox_def SEXP_def by auto

lemmas fbox_invs_raw = fbox_invs[unfolded expr_defs]

subsection \<open> Forward diamond operator \<close>

definition fdia :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'b pred \<Rightarrow> 'a pred"
  where "fdia F P = (\<lambda>s. (\<exists>s'. s' \<in> F s \<and> P s'))"

expr_ctr fdia

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


subsection \<open> Hoare triple \<close>

syntax
  "_hoare" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("\<^bold>{_\<^bold>}/ _ /\<^bold>{_\<^bold>}")

translations
  "\<^bold>{p\<^bold>}S\<^bold>{q\<^bold>}" == "(p)\<^sub>e \<le> |S] q"

lemma fbox_to_hoare: "P \<le> |F] Q \<longleftrightarrow> \<^bold>{P\<^bold>}F\<^bold>{Q\<^bold>}"
  by auto

lemma hoare_invs:
  assumes "\<^bold>{I\<^sub>1\<^bold>}F\<^bold>{I\<^sub>1\<^bold>}" and "\<^bold>{I\<^sub>2\<^bold>}F\<^bold>{I\<^sub>2\<^bold>}"
  shows hoare_conj_inv: "\<^bold>{I\<^sub>1 \<and> I\<^sub>2\<^bold>}F\<^bold>{I\<^sub>1 \<and> I\<^sub>2\<^bold>}"
    and hoare_disj_inv: "\<^bold>{I\<^sub>1 \<or> I\<^sub>2\<^bold>}F\<^bold>{I\<^sub>1 \<or> I\<^sub>2\<^bold>}"
  using fbox_invs[OF assms] by auto

text \<open> Need to generalise these laws \<close>

lemma hoare_conj_preI: 
  "\<^bold>{@a\<^bold>}X\<^bold>{@Q\<^bold>} \<Longrightarrow> P = (@a \<and> @b)\<^sub>e \<Longrightarrow> \<^bold>{@P\<^bold>}X\<^bold>{@Q\<^bold>}"
  by (auto simp: fun_eq_iff)

lemma hoare_conj_posI: 
  "\<^bold>{@P\<^bold>}X\<^bold>{@a\<^bold>} \<Longrightarrow> \<^bold>{@P\<^bold>}X\<^bold>{@b\<^bold>} \<Longrightarrow> Q = (@a \<and> @b)\<^sub>e \<Longrightarrow> \<^bold>{@P\<^bold>}X\<^bold>{@Q\<^bold>}"
  by (auto simp: fun_eq_iff fbox_def)

lemma hoare_conj_pos: 
  "(\<^bold>{@P\<^bold>} X \<^bold>{@Q1 \<and> @Q2\<^bold>}) = (\<^bold>{@P\<^bold>} X \<^bold>{@Q1\<^bold>} \<and> \<^bold>{@P\<^bold>} X \<^bold>{@Q2\<^bold>})"
  by (auto simp: fbox_def)

lemma hoare_disj_preI:
  "\<^bold>{@a \<and> @b\<^bold>}X\<^bold>{@Q\<^bold>} \<Longrightarrow> \<^bold>{@a \<and> @c\<^bold>}X\<^bold>{@Q\<^bold>} \<Longrightarrow> P = (@a \<and> (@b \<or> @c))\<^sub>e \<Longrightarrow> \<^bold>{@P\<^bold>}X\<^bold>{@Q\<^bold>}"
  by (auto simp: le_fun_def fbox_def)

lemma hoare_disj_posI: 
  "\<^bold>{@P\<^bold>}X\<^bold>{@a\<^bold>} \<Longrightarrow> Q = (@a \<or> @b)\<^sub>e \<Longrightarrow> \<^bold>{@P\<^bold>}X\<^bold>{@Q\<^bold>}"
  by (auto simp: le_fun_def fbox_def)

lemma hoare_conseq: 
  assumes "\<^bold>{p\<^sub>2\<^bold>}S\<^bold>{q\<^sub>2\<^bold>}" "`p\<^sub>1 \<longrightarrow> p\<^sub>2`" "`q\<^sub>2 \<longrightarrow> q\<^sub>1`"
  shows "\<^bold>{p\<^sub>1\<^bold>}S\<^bold>{q\<^sub>1\<^bold>}"
  using assms 
  by (auto simp add: fbox_def expr_defs)


subsection \<open> Skip \<close>

definition [prog_defs]: "skip = (\<lambda>s. {s})"

lemma fbox_skip [wp]: "|skip] P = P"
  unfolding fbox_def skip_def by simp

lemma fdia_skip: "|skip\<rangle> P = P"
  unfolding fdia_def skip_def by simp

lemma hoare_skip: "\<^bold>{P\<^bold>} skip \<^bold>{P\<^bold>}"
  by (auto simp: fbox_skip)

subsection \<open> Abort \<close>

definition [prog_defs]: "abort = (\<lambda>s. {})"

lemma fbox_abort [wp]: "|abort] P = (True)\<^sub>e"
  unfolding fbox_def abort_def by auto

lemma fdia_abort: "|abort\<rangle> P = (False)\<^sub>e"
  unfolding fdia_def abort_def by expr_simp

lemma hoare_abort: "\<^bold>{P\<^bold>} abort \<^bold>{Q\<^bold>}"
  by (auto simp: fbox_abort)

subsection \<open> Tests \<close>

definition test :: "'a pred \<Rightarrow> 'a \<Rightarrow> 'a set"
  where [prog_defs]: "test P = (\<lambda>s. {x. x = s \<and> P x})"

syntax 
  "_test" :: "logic \<Rightarrow> logic" ("(1\<questiondown>_?)")

translations
  "_test P" == "CONST test (P)\<^sub>e"

lemma fbox_test [wp]: "|\<questiondown>P?] Q = (P \<longrightarrow> Q)\<^sub>e"
  unfolding fbox_def test_def by (simp add: expr_defs)

lemma fdia_test: "|\<questiondown>P?\<rangle> Q = (P \<and> Q)\<^sub>e"
  unfolding fdia_def test_def by expr_simp

lemma hoare_test: "\<^bold>{P\<^bold>} \<questiondown>T? \<^bold>{P \<and> T\<^bold>}"
  by (auto simp: fbox_test)

subsection \<open> Assignments \<close>

thm subst_nil_def subst_bop
thm subst_basic_ops
thm subst_lookup_def subst_app_def lens_update_def

definition assigns :: "'s subst \<Rightarrow> 's \<Rightarrow> 's set" ("\<langle>_\<rangle>") 
  where [prog_defs]: "\<langle>\<sigma>\<rangle> = (\<lambda> s. {\<sigma> s})"

syntax
  "_assign" :: "svid \<Rightarrow> logic \<Rightarrow> logic" ("(2_ ::= _)" [65, 64] 64)

translations
  "_assign x e" == "\<langle>CONST subst_upd [\<leadsto>] x (e)\<^sub>e\<rangle>" (* "\<langle>[x \<leadsto>\<^sub>s e]\<rangle>" *)

lemma fbox_assign: "|x ::= e] Q = (Q\<lbrakk>e/x\<rbrakk>)\<^sub>e"
  by (simp add: assigns_def subst_app_def fbox_def fun_eq_iff)

lemma hoare_assign: "\<^bold>{Q\<lbrakk>e/x\<rbrakk>\<^bold>} (x ::= e) \<^bold>{Q\<^bold>}"
  by (auto simp: fbox_assign)

lemma fbox_assigns [wp]: "|\<langle>\<sigma>\<rangle>] Q = \<sigma> \<dagger> (Q)\<^sub>e"
  by (simp add: assigns_def expr_defs fbox_def)

lemma H_assign_floyd_hoare:
  assumes "vwb_lens x"
  shows "\<^bold>{p\<^bold>} x ::= e \<^bold>{\<exists> v . p\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk> \<and> $x = e\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>\<^bold>}"
  using assms apply (simp add: wp, expr_auto)
  by (metis vwb_lens_def wb_lens.source_stability)

lemma fdia_assign: "|x ::= e\<rangle> P = (P\<lbrakk>e/x\<rbrakk>)\<^sub>e"
  by (simp add: assigns_def expr_defs fdia_def)

subsection \<open> Nondeterministic assignments \<close>

definition nondet_assign :: "('a \<Longrightarrow> 's) \<Rightarrow> 's prog" ("(2_ ::= ?)" [64] 65)
  where [prog_defs]: "(x ::= ?) = (\<lambda>s. {(put\<^bsub>x\<^esub> s k)|k. True})"

lemma fbox_nondet_assign [wp]: "|x ::= ?] P = (\<forall>k. P\<lbrakk>k/x\<rbrakk>)\<^sub>e"
  unfolding fbox_def nondet_assign_def vec_upd_eq 
  by (auto simp add: fun_eq_iff expr_defs)

lemma hoare_nondet_assign: "\<^bold>{\<forall>k. Q\<lbrakk>k/x\<rbrakk>\<^bold>} (x ::= ?) \<^bold>{Q\<^bold>}"
  by (simp add: fbox_nondet_assign)

lemma fdia_nondet_assign: "|x ::= ?\<rangle> P = (\<exists>k. P\<lbrakk>k/x\<rbrakk>)\<^sub>e"
  unfolding fdia_def nondet_assign_def vec_upd_eq 
  by (auto simp add: fun_eq_iff expr_defs)

subsection \<open> Nondeterministic choice \<close>

definition nondet_choice :: "'s prog \<Rightarrow> 's prog \<Rightarrow> 's prog" (infixr "\<sqinter>" 60) 
  where [prog_defs]: "nondet_choice F G = (\<lambda> s. F s \<union> G s)"

lemma fbox_choice [wp]: "|F \<sqinter> G] P = ( |F] P \<and> |G] P)\<^sub>e"
  unfolding fbox_def nondet_choice_def by auto

lemma le_fbox_choice_iff: "P \<le> |F \<sqinter> G] Q \<longleftrightarrow> P \<le> |F] Q \<and> P \<le> |G] Q"
  unfolding fbox_def nondet_choice_def by auto

lemma hoare_choice: 
  "\<^bold>{P\<^bold>} F \<^bold>{Q\<^bold>} \<Longrightarrow> \<^bold>{P\<^bold>} G \<^bold>{Q\<^bold>} \<Longrightarrow> \<^bold>{P\<^bold>} (F \<sqinter> G) \<^bold>{Q\<^bold>}"
  by (subst le_fbox_choice_iff, simp)

lemma fdia_choice: "|F \<sqinter> G\<rangle> P = ( |F\<rangle> P \<or> |G\<rangle> P)\<^sub>e"
  unfolding fdia_def nondet_choice_def by expr_auto

definition Nondet_choice :: "('i \<Rightarrow> 's prog) \<Rightarrow> 'i set \<Rightarrow> 's prog"
  where "Nondet_choice F I = (\<lambda>s. \<Union> i\<in>I. F i s)"

syntax
  "_Nondet_choice" :: "idt \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("\<Sqinter> _ \<in> _./ _" [0, 0, 10] 10)

translations "_Nondet_choice i I P" == "CONST Nondet_choice (\<lambda> i. P) I"

lemma fbox_Choice [wp]: "|\<Sqinter> i\<in>I. F(i)] P = (\<forall> i\<in>\<guillemotleft>I\<guillemotright>. |F(i)] P)\<^sub>e"
  by (auto simp add: fbox_def Nondet_choice_def fun_eq_iff)

subsection \<open> Sequential composition \<close>

definition kcomp :: "('a \<Rightarrow> 'b set) \<Rightarrow> ('b \<Rightarrow> 'c set) \<Rightarrow> ('a  \<Rightarrow> 'c set)" (infixl ";" 62) 
  where [prog_defs]: "F ; G = \<mu> \<circ> \<P> G \<circ> F"

lemma kcomp_eq: "(f ; g) x = \<Union> {g y |y. y \<in> f x}"
  unfolding kcomp_def image_def by auto

lemma kcomp_id: 
  shows "f ; (\<lambda>s. {s}) = f"
    and "(\<lambda>s. {s}) ; f = f"
  unfolding kcomp_eq 
  by auto

lemmas kcomp_skip = kcomp_id[unfolded skip_def[symmetric]]

lemma kcomp_assoc: "f ; g ; h = f ; (g ; h)"
  unfolding kcomp_eq 
  by (auto simp: fun_eq_iff)

lemma fbox_kcomp[wp]: "|G ; F] P = |G] |F] P"
  unfolding fbox_def kcomp_def by auto

lemma hoare_kcomp:
  assumes "\<^bold>{P\<^bold>} G \<^bold>{R\<^bold>}" and "\<^bold>{R\<^bold>} F \<^bold>{Q\<^bold>}"
  shows "\<^bold>{P\<^bold>} G ; F \<^bold>{Q\<^bold>}"
  apply(subst fbox_kcomp)
  using assms fbox_iso
  by (metis (mono_tags, lifting) SEXP_def predicate1D predicate1I) 

lemma hoare_kcomp_inv:
  assumes "\<^bold>{I\<^bold>} G \<^bold>{I\<^bold>}" and "\<^bold>{I\<^bold>} F \<^bold>{I\<^bold>}"
  shows "\<^bold>{I\<^bold>} G ; F \<^bold>{I\<^bold>}"
  using assms hoare_kcomp by fastforce

lemma fdia_kcomp:
  assumes "H = |F\<rangle> P"
  shows"|G ; F\<rangle> P = |G\<rangle> H"
  unfolding fdia_def kcomp_def assms by auto

lemma hoare_fwd_assign:
  assumes "vwb_lens x" "\<And> x\<^sub>0. \<^bold>{$x = e\<lbrakk>\<guillemotleft>x\<^sub>0\<guillemotright>/x\<rbrakk> \<and> P\<lbrakk>\<guillemotleft>x\<^sub>0\<guillemotright>/x\<rbrakk>\<^bold>} S \<^bold>{Q\<^bold>}"
  shows "\<^bold>{P\<^bold>} x ::= e ; S \<^bold>{Q\<^bold>}"
  using assms
  unfolding kcomp_def assigns_def fbox_def le_fun_def
  by (expr_simp) (metis vwb_lens.put_eq vwb_lens_wb wb_lens_def weak_lens.put_get)

subsection \<open> Conditional statement \<close>

definition ifthenelse :: "'a pred \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> 'b set)" where
  [prog_defs]: "ifthenelse P X Y \<equiv> (\<lambda>s. if P s then X s else Y s)"

syntax "_ifthenelse" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("IF _ THEN _ ELSE _" [0,0,63] 64)
translations "IF P THEN X ELSE Y" == "CONST ifthenelse (P)\<^sub>e X Y"

lemma "IF T THEN X ELSE Y = \<questiondown>T? ; X \<sqinter> \<questiondown>\<not> T? ; Y"
  by (auto simp: fun_eq_iff test_def kcomp_def ifthenelse_def nondet_choice_def)

lemma fbox_if_then_else [simp]:
  "|IF T THEN X ELSE Y] Q = ((T \<longrightarrow> |X] Q) \<and> (\<not> T \<longrightarrow> |Y] Q))\<^sub>e"
  unfolding fbox_def ifthenelse_def by auto

lemma hoare_if_then_else:
  assumes "\<^bold>{P \<and> T\<^bold>} X \<^bold>{Q\<^bold>}"
    and "\<^bold>{P \<and> \<not> T\<^bold>} Y \<^bold>{Q\<^bold>}"
  shows "\<^bold>{P\<^bold>} (IF T THEN X ELSE Y) \<^bold>{Q\<^bold>}"
  using assms unfolding fbox_def ifthenelse_def by auto

lemma hoare_if_then_else_inv:
  assumes "\<^bold>{b \<and> I\<^bold>}P\<^bold>{b \<and> I\<^bold>}" "\<^bold>{\<not>b \<and> I\<^bold>}Q\<^bold>{\<not>b \<and> I\<^bold>}" 
  shows "\<^bold>{I\<^bold>}IF b THEN P ELSE Q\<^bold>{I\<^bold>}"
  using assms
  by (auto simp add: fbox_def expr_defs ifthenelse_def)

lemma fdia_if_then_else:
  assumes "H1 = |X\<rangle> Q"
  assumes "H2 = |Y\<rangle> Q"
  shows"|IF T THEN X ELSE Y\<rangle> Q = ((T \<and> H1) \<or> (\<not> T \<and> H2))\<^sub>e"
  unfolding fdia_def ifthenelse_def assms by expr_auto


subsection \<open> Finite iteration \<close>

definition kpower :: "('a \<Rightarrow> 'a set) \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> 'a set)" 
  where [prog_defs]: "kpower f n = (\<lambda>s. (((;) f ^^ n) skip) s)"

lemma kpower_base:
  shows kpower_0: "kpower f 0 = (\<lambda>s. {s})" 
    and kpower_Suc_0: "kpower f (Suc 0) = (\<lambda>s. f s)"
  unfolding kpower_def 
  by (auto simp: kcomp_eq skip_def fun_eq_iff)

lemmas kpower_0' = kpower_0[unfolded skip_def[symmetric]]

lemma kpower_Suc: "kpower f (Suc n) = (f ; kpower f n)"
  apply (induct n)
  unfolding kcomp_eq kpower_base
   apply(force simp: subset_antisym)
  unfolding kpower_def kcomp_eq by simp

lemma kpower_Suc': "kpower f (Suc n) = (kpower f n; f)"
  apply (induct n)
  by (simp add: kpower_base kcomp_def)
    (simp add: kpower_Suc kcomp_assoc[symmetric])

lemma "kpower f 2 s = (\<Union> {f s' |s'. s' \<in> f s})"
  by (subgoal_tac "2 = Suc (Suc 0)", erule ssubst)
    (auto simp: kpower_Suc kpower_base kcomp_id kcomp_eq)

lemma kpower_nil: "kpower (\<lambda>s. {}) (Suc n) = (\<lambda>s. {})"
  by (induct n) 
    (simp_all add: kpower_base kpower_Suc kcomp_eq)

lemmas kpower_abort = kpower_nil[unfolded abort_def[symmetric]]

lemma kpower_id: "kpower (\<lambda>s. {s}) n = (\<lambda>s. {s})"
  by (induct n) 
    (simp_all add: kpower_base kpower_Suc kcomp_eq)

lemmas kpower_skip = kpower_id[unfolded skip_def[symmetric]]

lemma kcomp_kpower: "(f ; kpower f n) = (kpower f n; f)"
  by (induct n, simp_all add: kpower_base kcomp_id 
      kpower_Suc kpower_Suc' kcomp_assoc[symmetric])

definition kstar :: "('a \<Rightarrow> 'a set) \<Rightarrow> ('a \<Rightarrow> 'a set)" ("(_\<^sup>*)" [1000] 999)
  where [prog_defs]: "(f\<^sup>*) s = \<Union> {kpower f n s |n. n \<in> UNIV}"

lemma kstar_alt: "f\<^sup>* = (\<Sqinter>i\<in>UNIV. kpower f i)"
  by (auto simp add: fun_eq_iff kstar_def Nondet_choice_def)

lemma in_kstar_self: "s \<in> (f\<^sup>*) s"
  unfolding kstar_def apply clarsimp
  by (rule_tac x="{s}" in exI, clarsimp)
    (rule_tac x=0 in exI, clarsimp simp: kpower_base)

lemma kstar_nil: "(\<lambda>s. {})\<^sup>* = (\<lambda>s. {s})"
  unfolding kstar_def apply (intro ext set_eqI iffI; clarsimp)
  subgoal for s' s n by (induct n, simp_all add: kpower_id kpower_nil kpower_base)
  by (rule_tac x="{s}" in exI, clarsimp)
    (rule_tac x=0 in exI, clarsimp simp: kpower_base)

lemmas kstar_abort = kstar_nil[unfolded abort_def[symmetric] skip_def[symmetric]]

lemma kstar_id: "(\<lambda>s. {s})\<^sup>* = (\<lambda>s. {s})"
  unfolding kstar_def 
  by (auto simp: fun_eq_iff kpower_base kpower_id)

lemmas kstar_skip = kstar_id[unfolded skip_def[symmetric]]

lemma kcomp_kstar: "f ; f\<^sup>* = f\<^sup>* ; f"
proof(intro ext set_eqI iffI conjI impI, goal_cases "\<subseteq>" "\<supseteq>")
  case ("\<subseteq>" s s')
  then obtain n where "s' \<in> (f ; kpower f n) s"
    unfolding kcomp_eq kstar_def 
    by auto
  hence "s' \<in> (kpower f n; f) s"
    unfolding kcomp_kpower by simp
  then show "s' \<in> (f\<^sup>*; f) s" 
    unfolding kcomp_eq kstar_def 
    by auto
next
  case ("\<supseteq>" s s')
  then obtain n where "s' \<in> (kpower f n; f) s"
    unfolding kcomp_eq kstar_def 
    by auto
  hence "s' \<in> (f; kpower f n) s"
    unfolding kcomp_kpower by simp
  then show "s' \<in> (f; f\<^sup>*) s" 
    unfolding kcomp_eq kstar_def 
    by auto
qed

lemma kpower_inv: 
  fixes F :: "'a \<Rightarrow> 'a set"
  assumes "\<forall>s. I s \<longrightarrow> (\<forall>s'. s' \<in> F s \<longrightarrow> I s')" 
  shows "\<forall>s. I s \<longrightarrow> (\<forall>s'. s' \<in> (kpower F n s) \<longrightarrow> I s')"
  apply(clarsimp, induct n)
  unfolding kpower_base kpower_Suc
   apply(simp_all add: kcomp_eq, clarsimp) 
  apply(subgoal_tac "I y", simp)
  using assms by blast

lemma kstar_inv: "I \<le> |F] I \<Longrightarrow> I \<le> |F\<^sup>*] I"
  unfolding kstar_def fbox_def 
  apply clarsimp
  apply(unfold le_fun_def, subgoal_tac "\<forall>x. I x \<longrightarrow> (\<forall>s'. s' \<in> F x \<longrightarrow> I s')")
  using kpower_inv[of I F] by blast simp

lemma fdia_kstar_inv: "I \<le> |F\<rangle> I \<Longrightarrow> I \<le> |F\<^sup>*\<rangle> I"
  unfolding kstar_def fdia_def apply(clarsimp simp: le_fun_def)
  apply(erule_tac x=x in allE, clarsimp, rule_tac x=s' in exI, simp)
  apply(rule_tac x="kpower F 1 x" in exI, simp add: kpower_base)
  by (rule_tac x=1 in exI, simp add: kpower_base)

lemma kstar_inv_rule: "\<^bold>{I\<^bold>} F \<^bold>{I\<^bold>} \<Longrightarrow> \<^bold>{I\<^bold>} F\<^sup>* \<^bold>{I\<^bold>}"
  by (metis SEXP_def kstar_inv)

lemma fbox_kstarI:
  assumes "P \<le> I" and "I \<le> Q" and "I \<le> |F] I" 
  shows "P \<le> |F\<^sup>*] Q"
proof-
  have "I \<le> |F\<^sup>*] I"
    using assms(3) kstar_inv by blast
  hence "P \<le> |F\<^sup>*] I"
    using assms(1) by auto
  also have "|F\<^sup>*] I \<le> |F\<^sup>*] Q"
    by (rule fbox_iso[OF assms(2)])
  finally show ?thesis .
qed

lemma hoare_kstarI: "`P \<longrightarrow> I` \<Longrightarrow> `I \<longrightarrow> Q` \<Longrightarrow> \<^bold>{I\<^bold>} F \<^bold>{I\<^bold>} \<Longrightarrow> \<^bold>{P\<^bold>} F\<^sup>* \<^bold>{Q\<^bold>}"
  by (rule fbox_kstarI) (auto simp: SEXP_def taut_def)

lemma le_fdia_kstarI:
  assumes "P \<le> I" and "I \<le> Q" and "I \<le> |F\<rangle> I" 
  shows "P \<le> |F\<^sup>*\<rangle> Q"
proof-
  have "I \<le> |F\<^sup>*\<rangle> I"
    using assms(3) fdia_kstar_inv by blast
  hence "P \<le> |F\<^sup>*\<rangle> I"
    using assms(1) by auto
  also have "|F\<^sup>*\<rangle> I \<le> |F\<^sup>*\<rangle> Q"
    by (rule fdia_iso[OF assms(2)])
  finally show ?thesis .
qed

lemma fdia_kpower_kstar: "( |kpower F n\<rangle> Q) s \<Longrightarrow> ( |F\<^sup>*\<rangle> Q) s"
  by (clarsimp simp: kstar_def fdia_def) 
    (rule_tac x=s' in exI, force)

lemma fdia_kstar_kpower: "( |F\<^sup>*\<rangle> Q) s \<Longrightarrow> \<exists>n. ( |kpower F n\<rangle> Q) s"
  by (auto simp: kstar_def fdia_def) 

lemma fdia_unfoldI: "( |F\<rangle> Q) s \<or> ( |F\<rangle> |F\<^sup>*\<rangle> Q) s \<Longrightarrow> ( |F\<^sup>*\<rangle> Q) s"
proof-
  assume "( |F\<rangle> Q) s \<or> ( |F\<rangle> |F\<^sup>*\<rangle> Q) s"
  moreover
  {assume "( |F\<rangle> Q) s"
    hence "( |kpower F (Suc 0)\<rangle> Q) s"
      unfolding fdia_def kpower_base .
    hence "( |F\<^sup>*\<rangle> Q) s"
      using fdia_kpower_kstar[of F "Suc 0"] 
      by blast}
  moreover
  {assume hyp: "( |F\<rangle> |F\<^sup>*\<rangle> Q) s"
    then obtain n s' \<sigma> where fst_step: "\<sigma> \<in> F s" 
      and end_step: "Q s'" and nth_step: "s' \<in> kpower F n \<sigma>"
      by (clarsimp simp: kstar_def fdia_def)
    hence "( |F\<^sup>*\<rangle> Q) s"
    proof (clarsimp simp: kstar_def fdia_def, cases "n=0")
      case True
      then show "\<exists>s'. (\<exists>x. (\<exists>m. x = kpower F m s) \<and> s' \<in> x) \<and> Q s'"
        using nth_step fst_step end_step
        apply (rule_tac x=s' in exI, clarsimp)
        by (rule_tac x="kpower F 1 s" in exI, simp add: kpower_base)
          (rule_tac x=1 in exI, simp add: kpower_base)
    next
      case False
      hence "\<exists>m. \<mu> {kpower F n y |y. y \<in> F s} = kpower F m s"
        apply (rule_tac x="Suc n" in exI, subst kcomp_eq[of F "kpower F n", symmetric])
        by (auto simp: kpower_Suc)
      then show "\<exists>s'. (\<exists>x. (\<exists>m. x = kpower F m s) \<and> s' \<in> x) \<and> Q s'" 
        using nth_step fst_step end_step
        apply (rule_tac x=s' in exI, clarsimp)
        by (rule_tac x="kpower F (Suc n) s" in exI)
          (auto simp add: kpower_Suc kcomp_eq)
    qed
  }
  ultimately show ?thesis
    by blast
qed

lemma fdia_kstar_convergence:
  fixes P::"real \<Rightarrow> 'a \<Rightarrow> bool"
  defines "Q \<equiv> (\<lambda>s. \<exists>r::real\<le>0. P r s)"
  assumes init: "`\<exists>r. @(P r)`"
    and iter: "`\<forall>r>0. @(P r) \<longrightarrow> ( |F\<rangle> @(P (r - 1)))`"
  shows "( |F\<^sup>*\<rangle> Q) s"
proof-
  have iter': "\<And>s. \<forall>r>0. P r s \<longrightarrow> ( |F\<rangle> @(P (r - 1))) s"
    using iter by (auto simp: taut_def)
  have init': "\<forall>\<s>. \<exists>r. P r \<s>"
    using init by expr_simp
  then obtain r where "P r s"
    by blast
  hence "r \<le> 0 \<Longrightarrow> Q s"
    using assms by blast
  hence case1: "r \<le> 0 \<Longrightarrow> ( |F\<^sup>*\<rangle> Q) s"
    by (clarsimp simp: fdia_def)
      (rule_tac x=s in exI, simp add: in_kstar_self)
  have obs_induct: 
    "`\<forall>t::real. t - \<guillemotleft>n\<guillemotright> > 0 \<longrightarrow> @(P t) \<longrightarrow> ( |kpower F n\<rangle> @(P (t - n)))`" for n::nat
  proof (induct n )
    case 0
    then show ?case 
      using iter'[rule_format]
      by (simp add: kpower_base fdia_def taut_def)
  next
    case (Suc n)
    show ?case
    proof(clarsimp simp only: taut_def, clarsimp)
      fix s t
      assume hyps: "1 + real n < t" "P t s"
      hence "t > 0" "0 < t - real n"
        by auto
      hence induct': "\<And>m s t. 0 < t - real n \<Longrightarrow> P t s 
        \<Longrightarrow> ( |kpower F n\<rangle> @(P (t - real n))) s"
        using Suc
        by expr_simp
      hence case_eq0: "n = 0 \<Longrightarrow> ( |kpower F (Suc n)\<rangle> @(P (t - (1 + real n)))) s"
        using iter'[rule_format, OF \<open>t > 0\<close> \<open>P t s\<close>]
        by (subst kpower_Suc, subst fdia_kcomp[OF refl])
          (simp add: kpower_base skip_def[symmetric] fdia_skip)
      have "( |kpower F n\<rangle> @(P (t - real n))) s"
        using hyps induct'[OF \<open>0 < t - real n\<close>]
        by force
      moreover note iter'[rule_format, OF \<open>0 < t - real n\<close>]
      ultimately have "n \<noteq> 0 \<Longrightarrow> ( |kpower F (Suc n)\<rangle> @(P (t - (1 + real n)))) s"
        apply -
        apply (frule not0_implies_Suc, clarsimp)
        apply (subst kpower_Suc, subst fdia_kcomp[OF refl])
        apply (subst (asm) kpower_Suc, subst (asm) fdia_kcomp[OF refl])
        apply (rule fdia_mono, force)
        apply (subst kpower_Suc, subst kcomp_kpower, subst fdia_kcomp[OF refl])
        by (rule fdia_mono) (auto simp: taut_def diff_add_eq_diff_diff_swap)
      thus "( |kpower F (Suc n)\<rangle> @(P (t - (1 + real n)))) s"
        using case_eq0 by blast
    qed
  qed
  moreover
  {assume "r > 0"
    then obtain n::nat where r_hyps: "Suc n \<ge> r" "r - n > 0"
      using pos_real_within_Suc 
      by auto
    hence "( |kpower F n\<rangle> @(P (r - n))) s"
      using obs_induct[unfolded taut_def, rule_format, 
          simplified, rule_format, OF _ \<open>P r s\<close>]
      by simp
    hence "( |F\<^sup>*\<rangle> @(P (r - n))) s"
      using fdia_kpower_kstar[of F "n"] 
      by force
    hence "( |F\<^sup>*\<rangle> @(P (r - (Suc n)))) s"
      apply (intro fdia_unfoldI disjI2)
      apply (subst fdia_kcomp[OF refl, symmetric])
      apply (subst kcomp_kstar, subst fdia_kcomp[OF refl])
      apply (rule fdia_mono, force)
      using iter'[rule_format, OF \<open>r - n > 0\<close>]
      by (auto simp: taut_def diff_add_eq_diff_diff_swap)
    hence "( |F\<^sup>*\<rangle> @Q) s"
      unfolding assms 
      apply (rule fdia_mono)
      using r_hyps
      by (clarsimp simp: taut_def)
        (rule_tac x="r - Suc n" in exI, force)}
  ultimately show "( |F\<^sup>*\<rangle> @Q) s"
    using case1 by linarith
qed

lemma fdia_kstarI:
  fixes P::"real \<Rightarrow> 'a \<Rightarrow> bool"
  assumes init: "`\<exists>r. @(P r)`"
    and iter: "`\<forall>r>0. @(P r) \<longrightarrow> ( |F\<rangle> @(P (r - 1)))`"
    and "`(\<exists>r\<le>0. @(P r)) \<longrightarrow> Q`"
  shows "( |F\<^sup>*\<rangle> Q) s"
  by (rule fdia_mono(1)[OF fdia_kstar_convergence[OF assms(1,2)] assms(3)])


subsection \<open> Loops with annotated invariants \<close>

definition loopi :: "('a \<Rightarrow> 'a set) \<Rightarrow> 'a pred \<Rightarrow> ('a \<Rightarrow> 'a set)" 
  where [prog_defs]: "loopi F I \<equiv> (F\<^sup>*)"

syntax "_loopi" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("LOOP _ INV _" [0, 63] 64)
translations "_loopi F I" == "CONST loopi F (I)\<^sub>e"

lemma change_loopI: "LOOP X INV G = LOOP X INV I"
  unfolding loopi_def by simp

lemma fbox_loopI: "P \<le> I \<Longrightarrow> I \<le> Q \<Longrightarrow> I \<le> |F] I \<Longrightarrow> P \<le> |LOOP F INV I] Q"
  unfolding loopi_def using fbox_kstarI[of "P"] by (auto simp: SEXP_def)

lemma in_fbox_loopI: "I s \<Longrightarrow> I \<le> Q \<Longrightarrow> I \<le> ( |R] @(I)) \<Longrightarrow> ( |LOOP R INV @I] (@Q)) s"
  using fbox_loopI[of I I Q R]
  by (clarsimp simp: le_fun_def)

lemma fbox_loopI': "P \<le> I \<Longrightarrow> I \<le> Q \<Longrightarrow> I \<le> fbox F I \<Longrightarrow> P \<le> fbox (loopi F I) Q"
  by (metis clarify_fbox fbox_kstarI loopi_def)

lemma hoare_loopI: "\<^bold>{I\<^bold>} F \<^bold>{I\<^bold>} \<Longrightarrow> `P \<longrightarrow> I` \<Longrightarrow> `I \<longrightarrow> Q` \<Longrightarrow> \<^bold>{P\<^bold>} LOOP F INV I \<^bold>{Q\<^bold>}"
  by (rule fbox_loopI) (auto simp: SEXP_def taut_def)

lemma hoare_loop_seqI: "\<^bold>{I\<^bold>} F \<^bold>{I\<^bold>} \<Longrightarrow> \<^bold>{I\<^bold>} G \<^bold>{I\<^bold>} \<Longrightarrow> `P \<longrightarrow> I` \<Longrightarrow> `I \<longrightarrow> Q` \<Longrightarrow> \<^bold>{P\<^bold>} LOOP (F ; G) INV I \<^bold>{Q\<^bold>}"
  by (rule fbox_loopI, simp_all add: wp refine_iff_implies)
     (metis (full_types) fbox_iso order.trans refine_iff_implies)

lemma fbox_loopI_break: 
  "P \<le> |Y] I \<Longrightarrow> I \<le> |X] I \<Longrightarrow> I \<le> Q \<Longrightarrow> P \<le> |Y ; (LOOP X INV I)] Q"
  apply(subst fbox_to_hoare, rule hoare_kcomp, force)
  by (rule hoare_loopI, auto simp: SEXP_def taut_def)

lemma hoare_loopI_break: 
  "\<^bold>{P\<^bold>} Y \<^bold>{I\<^bold>} \<Longrightarrow> \<^bold>{I\<^bold>} X \<^bold>{I\<^bold>} \<Longrightarrow> `I \<longrightarrow> Q` \<Longrightarrow> \<^bold>{P\<^bold>} (Y ; (LOOP X INV I)) \<^bold>{Q\<^bold>}"
  by (rule hoare_kcomp, force) (rule hoare_loopI, simp_all)

subsection \<open> While loop \<close>

definition while :: "'a pred \<Rightarrow> ('a \<Rightarrow> 'a set) \<Rightarrow> ('a \<Rightarrow> 'a set)" 
  where [prog_defs]: "while T X \<equiv> (\<questiondown>T? ; X)\<^sup>* ; \<questiondown>\<not>T?"

syntax "_while" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("WHILE _ DO _" [0,63] 64)
translations "WHILE T DO X" == "CONST while (T)\<^sub>e X"

lemma hoare_while:
  "\<^bold>{I\<^bold>} X \<^bold>{I\<^bold>} \<Longrightarrow> \<^bold>{I\<^bold>} (WHILE T DO X) \<^bold>{\<not> T \<and> I\<^bold>}"
  unfolding while_def 
  apply (simp add: fbox_test fbox_kcomp)
  apply (rule_tac p\<^sub>2=I and q\<^sub>2=I in hoare_conseq)
    prefer 3 apply expr_simp
  prefer 2 apply expr_simp
  apply (rule_tac I="I" in hoare_kstarI)
      apply expr_simp
   apply expr_simp
  apply (rule_tac R="(I \<and> T)\<^sup>e" in hoare_kcomp)
  by (auto simp: fbox_test fbox_kcomp)


subsection \<open> Framing \<close>

definition frame :: "'s scene \<Rightarrow> 's prog \<Rightarrow> 's prog"
  where [prog_defs]: "frame a P = (\<lambda> s. {s'. s = cp\<^bsub>a\<^esub> s s' \<and> s' \<in> P s})"

syntax "_frame" :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("_:[_]" [65] 65)
translations "_frame a P" == "CONST frame a P"

lemma frame_UNIV: "\<Sigma>:[P] = P"
  by (simp add: frame_def lens_defs)

lemma frame_skip: "idem_scene a \<Longrightarrow> a:[skip] = skip"
  by (auto simp add: skip_def frame_def fun_eq_iff)
  
lemma frame_assign_in:
  assumes "vwb_lens x" "idem_scene a" "\<lbrakk>x\<rbrakk>\<^sub>\<sim> \<le> a"
  shows "a:[x ::= v] = x ::= v"
  using assms
  by (auto simp add: prog_defs expr_defs fun_eq_iff put_scene_override_le)
  
definition not_modifies :: "'s prog \<Rightarrow> 's scene \<Rightarrow> bool" where
  "not_modifies P a = (\<forall> s s'. s' \<in> P s \<longrightarrow> s' \<approx>\<^sub>S s on a)" 

syntax "_not_modifies" :: "logic \<Rightarrow> salpha \<Rightarrow> logic" (infix "nmods" 30)
translations "_not_modifies P a" == "CONST not_modifies P a"

named_theorems closure

(* FIXME: The following rule is an inefficient way to calculate modification; 
  replace with scene membership laws. *)

lemma nmods_union [closure]:
  assumes "P nmods A" "P nmods B"
  shows "P nmods (A \<union> B)"
  using assms
  by (auto simp add: not_modifies_def prog_defs)
     (metis scene_equiv_def scene_override_union scene_union_incompat scene_union_unit(1))

lemma nmods_skip [closure]: "idem_scene a \<Longrightarrow> skip nmods a"
  by (simp add: not_modifies_def prog_defs scene_equiv_def)

lemma nmods_seq [closure]:
  assumes "P nmods a" "Q nmods a"
  shows "(P ; Q) nmods a"
  using assms 
  by (auto simp add: not_modifies_def prog_defs scene_equiv_def)
    (metis scene_override_overshadow_right)

lemma nmods_if [closure]:
  assumes "P nmods a" "Q nmods a"
  shows "IF b THEN P ELSE Q nmods a"
  using assms by (auto simp add: not_modifies_def prog_defs)

lemma nmods_choice [closure]:
  assumes "P nmods a" "Q nmods a"
  shows "P \<sqinter> Q nmods a"  
  using assms by (auto simp add: not_modifies_def prog_defs)

lemma nmods_Choice [closure]:
  assumes "\<And> i. i \<in> I \<Longrightarrow> P(i) nmods a"
  shows "(\<Sqinter> i\<in>I. P(i)) nmods a"
  using assms
  by (auto simp add: Nondet_choice_def not_modifies_def)

lemma nmods_kpower [closure]:
  assumes "idem_scene a" "P nmods a"
  shows "(kpower P n) nmods a"
proof (induct n)
  case 0
  then show ?case 
    by (simp add: kpower_def assms(1) nmods_skip)
next
  case (Suc n)
  then show ?case
    by (simp add: kpower_Suc nmods_seq assms)
qed

lemma nmods_star [closure]:
  assumes "idem_scene a" "P nmods a"
  shows "P\<^sup>* nmods a"
  by (simp add: assms kstar_alt nmods_Choice nmods_kpower)

lemma nmods_loop [closure]:
  assumes "idem_scene a" "P nmods a"
  shows "LOOP P INV B nmods a"
  by (simp add: assms loopi_def nmods_star)

lemma nmods_test [closure]:
  "idem_scene a \<Longrightarrow> \<questiondown>b? nmods a"
  by (auto simp add: not_modifies_def prog_defs scene_equiv_def)

lemma nmods_assign [closure]:
  assumes "vwb_lens x" "idem_scene a" "var_alpha x \<bowtie>\<^sub>S a"
  shows "x ::= e nmods a"
  using assms
  by (expr_simp add: not_modifies_def assigns_def put_scene_override_indep)

lemma nmods_g_orbital_on_discrete [closure]:
  assumes "vwb_lens x" "idem_scene a" "var_alpha x \<bowtie>\<^sub>S a"
  shows "(g_orbital_on x f G U S t\<^sub>0) nmods a"
  using assms
  by (auto simp add: g_orbital_on_def not_modifies_def scene_equiv_def put_scene_override_indep var_alpha_def)

lemma nmods_g_orbital_on_discrete' [closure]:
  assumes "vwb_lens x" 
  shows "(g_orbital_on x f G U S t\<^sub>0) nmods (- $x)"
  by (rule nmods_g_orbital_on_discrete, simp_all add: assms lens_override_def scene_indep_self_compl var_alpha_def)

lemma nmods_g_orbital_on_discrete_lens [closure]:
  assumes "vwb_lens A" "vwb_lens x" "x \<bowtie> A"
  shows "(g_orbital_on A f G U S t\<^sub>0) nmods $x"
  by (rule nmods_g_orbital_on_discrete, simp_all add: assms lens_indep_sym scene_indep_sym var_alpha_def) 

lemma nmods_via_fbox:
  "\<lbrakk> vwb_lens x; \<And> v. |P] ($x = \<guillemotleft>v\<guillemotright>) = ($x = \<guillemotleft>v\<guillemotright>)\<^sub>e \<rbrakk> \<Longrightarrow> P nmods $x"
  by (expr_simp add: fbox_def not_modifies_def, auto)
     (metis UNIV_I lens_override_def mwb_lens.weak_get_put vwb_lens_iff_mwb_UNIV_src)

text \<open> Important principle: If @{term P} does not modify @{term a}, and predicate @{term b} does
  not refers only variables outside of @{term a} then @{term b} is an invariant of @{term P}. \<close>

lemma nmods_frame_law:
  assumes "S nmods a" "(-a) \<sharp> (I)\<^sub>e" "\<^bold>{P\<^bold>}S\<^bold>{Q\<^bold>}"
  shows "\<^bold>{P \<and> I\<^bold>}S\<^bold>{Q \<and> I\<^bold>}"
  using assms
  by (auto simp add: prog_defs fbox_def expr_defs scene_override_commute not_modifies_def scene_equiv_def, metis)

lemma nmods_invariant:
  assumes "P nmods a" "(-a) \<sharp> (b)\<^sub>e"
  shows "\<^bold>{b\<^bold>}P\<^bold>{b\<^bold>}"
  using assms
  by (auto simp add: prog_defs fbox_def expr_defs scene_override_commute not_modifies_def scene_equiv_def, metis)

subsection \<open> Analytic dynamics \<close>

definition g_evol :: "(('a::ord) \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b pred \<Rightarrow> ('b \<Rightarrow> 'a set) \<Rightarrow> ('b \<Rightarrow> 'b set)" ("EVOL")
  where "g_evol \<phi> G U = (\<lambda>s. g_orbit (\<lambda>t. \<phi> t s) G (U s))"

lemma fbox_g_evol: 
  fixes \<phi> :: "('a::preorder) \<Rightarrow> 'b \<Rightarrow> 'b"
  shows "|EVOL \<phi> G U] Q = (\<lambda>s. \<forall>t\<in>U s. (\<forall>\<tau>\<in>down (U s) t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s))"
  unfolding g_evol_def g_orbit_eq fbox_def by auto

lemma fdia_g_evol: 
  fixes \<phi> :: "('a::preorder) \<Rightarrow> 'b \<Rightarrow> 'b"
  shows "|EVOL \<phi> G U\<rangle> Q = (\<lambda>s. \<exists>t\<in>U s. (\<forall>\<tau>\<in>down (U s) t. G (\<phi> \<tau> s)) \<and> Q (\<phi> t s))"
  unfolding g_evol_def g_orbit_eq fdia_def by auto

lemma fbox_g_evol_alt: 
  fixes \<phi> :: "('a::preorder) \<Rightarrow> 'b \<Rightarrow> 'b"
  shows "|EVOL \<phi> G U] Q = (\<forall>t\<in>U. ((\<forall>\<tau>\<in>down U \<guillemotleft>t\<guillemotright>. \<phi> \<tau> \<dagger> G) \<longrightarrow> \<phi> t \<dagger> Q))\<^sub>e"
  by (simp add: fbox_g_evol, simp add: expr_defs)

definition g_evol_on :: "('c::real_normed_vector \<Longrightarrow> 'a) \<Rightarrow> (real \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> bool) 
  \<Rightarrow> ('c \<Rightarrow> real set) \<Rightarrow> 'a \<Rightarrow> 'a set" 
  where "g_evol_on a \<phi> G U s \<equiv> 
  put\<^bsub>a\<^esub> s ` (g_evol (loc_subst a \<phi> s) (\<lambda> v. G (put\<^bsub>a\<^esub> s v)) U (get\<^bsub>a\<^esub> s))"

lemma g_evol_on_eq:
  "vwb_lens a \<Longrightarrow> g_evol_on a \<phi> G U s = 
  {(s \<triangleleft>\<^bsub>a\<^esub> \<phi> t s) |t. t \<in> U (get\<^bsub>a\<^esub> s) \<and> (\<forall>\<tau>. \<tau> \<in> down (U (get\<^bsub>a\<^esub> s)) t \<longrightarrow> G (s \<triangleleft>\<^bsub>a\<^esub> \<phi> \<tau> s))}"
  by (auto simp add: g_evol_on_def g_evol_def g_orbit_eq lens_defs)

abbreviation g_evol_eqs :: "('c::real_normed_vector \<Longrightarrow> 'b) \<Rightarrow> (real \<Rightarrow> ('c, 'b) expr) \<Rightarrow> 'b pred 
  \<Rightarrow> ('c \<Rightarrow> real set) \<Rightarrow> ('b \<Rightarrow> 'b set)" 
  where "g_evol_eqs a \<phi> G U \<equiv> g_evol_on a (\<lambda>\<tau>. subst_upd [\<leadsto>] a (\<phi> \<tau>)) G U"

no_notation disj (infixr "|" 30)

syntax
  "_time_var" :: id
  "_EVOL" :: "svid \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("{EVOL _ = _ | _ on _}")
  "_EVOL_ge" :: "svid \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("{EVOL _ = _ | _}")
  "_EVOL_simp" :: "svid \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("{EVOL _ = _}")

parse_translation 
  \<open>[(@{syntax_const "_time_var"}, fn ctx => fn term => Syntax.free "\<tau>")]\<close>

translations
  "_EVOL a f G U" => "CONST g_evol_eqs a (\<lambda> _time_var. (f)\<^sub>e) (G)\<^sub>e (U)\<^sub>e"
  "_EVOL a f G U" <= "CONST g_evol_eqs a (\<lambda> b. (f)\<^sub>e) (G)\<^sub>e (U)\<^sub>e"
  "_EVOL_ge a f G" == "_EVOL a f G {0..}"
  "_EVOL_simp a f" == "_EVOL_ge a f (CONST True)"

term "{EVOL x = 5 * \<guillemotleft>\<tau>\<guillemotright> + $x}"
term "{EVOL x = 5 * \<guillemotleft>\<tau>\<guillemotright> + $x | $x \<ge> 0 \<and> \<guillemotleft>\<tau>\<guillemotright> \<le> \<guillemotleft>max\<guillemotright>}"
term "{EVOL x = 5 * \<guillemotleft>\<tau>\<guillemotright> + $x | $x \<ge> 0 \<and> \<guillemotleft>\<tau>\<guillemotright> \<le> \<guillemotleft>max\<guillemotright> on {0--\<guillemotleft>t\<guillemotright>}}"
term "{EVOL (x, y) = ($x * cos \<guillemotleft>\<tau>\<guillemotright> + $y * sin \<guillemotleft>\<tau>\<guillemotright>, - $x * sin \<guillemotleft>\<tau>\<guillemotright> + $y * cos \<guillemotleft>\<tau>\<guillemotright>) | true on UNIV}"

lemma fbox_g_evol_on [wp]:
  assumes "vwb_lens a"
  shows "|g_evol_on a \<phi> G U] Q 
  = (\<forall>t\<in>\<guillemotleft>U\<guillemotright> ($a). (\<forall> \<tau>\<in>down (\<guillemotleft>U\<guillemotright> ($a)) \<guillemotleft>t\<guillemotright> . G\<lbrakk>\<langle>\<phi> \<tau>\<rangle>\<^sub>s a/a\<rbrakk>) \<longrightarrow> Q\<lbrakk>\<langle>\<phi> t\<rangle>\<^sub>s a/a\<rbrakk>)\<^sub>e"
  unfolding fbox_def fun_eq_iff g_evol_on_eq[OF assms]
  by expr_auto

lemma "vwb_lens a \<Longrightarrow> |g_evol_on a \<phi> G U] Q = 
  (\<lambda>s. \<forall>t\<in>U (get\<^bsub>a\<^esub> s). (\<forall>\<tau>\<in>down (U (get\<^bsub>a\<^esub> s)) t. G (s \<triangleleft>\<^bsub>a\<^esub> \<phi> \<tau> s)) \<longrightarrow> Q (s \<triangleleft>\<^bsub>a\<^esub> \<phi> t s))"
  by (auto simp add: g_evol_on_eq fbox_def fun_eq_iff)


subsection \<open> ODE-dynamics \<close>

text \<open> Verification by providing solutions \<close>

notation g_orbital ("(1x\<acute>=_ & _ on _ _ @ _)")

lemma fbox_g_orbital: "|g_orbital f G U S t\<^sub>0] Q = 
  (\<lambda>s. \<forall>X\<in>Sols U S f t\<^sub>0 s. \<forall>t\<in>U s. (\<forall>\<tau>\<in>down (U s) t. G (X \<tau>)) \<longrightarrow> Q (X t))"
  unfolding fbox_def g_orbital_eq 
  by (auto simp: fun_eq_iff)

lemma fdia_g_orbital: "|g_orbital f G U S t\<^sub>0\<rangle> Q = 
  (\<lambda>s. \<exists>X\<in>Sols U S f t\<^sub>0 s. \<exists>t\<in>U s. (\<forall>\<tau>\<in>down (U s) t. G (X \<tau>)) \<and> Q (X t))"
  unfolding fdia_def g_orbital_eq 
  by (auto simp: fun_eq_iff)

context local_flow \<comment> \<open> First we obtain the results for local flows and orbitals \<close>
begin

lemma fbox_g_ode_subset:
  assumes "\<And>s. s \<in> S \<Longrightarrow> 0 \<in> U s \<and> is_interval (U s) \<and> U s \<subseteq> T"
  shows "|g_orbital (\<lambda>t. f) G U S 0] Q = 
  (\<lambda>s. s \<in> S \<longrightarrow> (\<forall>t\<in>(U s). (\<forall>\<tau>\<in>down (U s) t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s)))"
  apply(unfold fbox_g_orbital fun_eq_iff)
  apply(intro iffI allI impI conjI; clarify)
   apply(force simp: in_ivp_sols assms)
  apply(frule ivp_solsD(2), frule ivp_solsD(3), frule ivp_solsD(4))
  apply(subgoal_tac "\<forall>\<tau>\<in>down (U x) t. X \<tau> = \<phi> \<tau> x")
   apply(clarsimp, fastforce, rule ballI)
  apply(rule ivp_unique_solution[OF _ _ _ _ _ in_ivp_sols])
  using assms by auto
                         
lemma fbox_g_ode: "|g_orbital (\<lambda>t. f) G (\<lambda>s. T) S 0] Q = 
  (\<lambda>s. s \<in> S \<longrightarrow> (\<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s)))"
  by (subst fbox_g_ode_subset, simp_all add: init_time interval_time)

lemma fbox_g_ode_ivl: "t \<ge> 0 \<Longrightarrow> t \<in> T \<Longrightarrow> |g_orbital (\<lambda>t. f) G (\<lambda>s. {0..t}) S 0] Q = 
  (\<lambda>s. s \<in> S \<longrightarrow> (\<forall>t\<in>{0..t}. (\<forall>\<tau>\<in>{0..t}. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s)))"
  apply(subst fbox_g_ode_subset, simp_all add: subintervalI init_time real_Icc_closed_segment)
  by (auto simp: closed_segment_eq_real_ivl)

lemma fbox_orbit: "|\<gamma>\<^sup>\<phi>] Q = (\<lambda>s. s \<in> S \<longrightarrow> (\<forall> t \<in> T. Q (\<phi> t s)))"
  unfolding orbit_def fbox_g_ode by simp

lemma fdia_g_ode_subset:
  assumes "\<And>s. s \<in> S \<Longrightarrow> 0 \<in> U s \<and> is_interval (U s) \<and> U s \<subseteq> T"
  shows "|g_orbital (\<lambda>t. f) G U S 0\<rangle> Q = 
  (\<lambda>s. if s \<in> S then (\<exists>t\<in>(U s). (\<forall>\<tau>\<in>down (U s) t. G (\<phi> \<tau> s)) \<and> Q (\<phi> t s)) 
    else (\<exists>X\<in>Sols U S (\<lambda>t. f) 0 s. \<exists>t\<in>U s. (\<forall>\<tau>\<in>down (U s) t. G (X \<tau>)) \<and> Q (X t)))"
  using assms
  apply(unfold fdia_g_orbital fun_eq_iff)
  apply (intro allI iffI impI conjI; (clarsimp split: if_splits)?)
   apply(subgoal_tac "\<forall>\<tau>\<in>down (U x) t. X \<tau> = \<phi> \<tau> x"; clarsimp?)
  apply (rule_tac x=t in bexI; force)
   apply(rule ivp_unique_solution[OF _ _ _ _ _ in_ivp_sols, of _ U _ _]; force?)
  apply (rule_tac x="\<lambda>t. \<phi> t x" in bexI, rule_tac x=t in bexI; force?)
  by (auto intro!: in_ivp_sols)

lemma fdia_g_ode:
  assumes "S = UNIV" 
  shows "|g_orbital (\<lambda>t. f) G (\<lambda>s. T) S 0\<rangle> Q = 
  (\<lambda>s. (\<exists>t\<in>T. (\<forall>\<tau>\<in>down T t. G (\<phi> \<tau> s)) \<and> Q (\<phi> t s)))"
  using init_time interval_time assms
  by (subst fdia_g_ode_subset; force)

end

text \<open> Then we relate both orbital operators:  \<close>

lemma fbox_g_orbital_on: "|g_orbital_on a f G U S t\<^sub>0] Q =
  (\<lambda>s. \<forall>X\<in>Sols U S (loc_subst a f s) t\<^sub>0 (get\<^bsub>a\<^esub> s).
        \<forall>t\<in>U (get\<^bsub>a\<^esub> s). (\<forall>x. x \<in> U (get\<^bsub>a\<^esub> s) \<and> x \<le> t \<longrightarrow> G (put\<^bsub>a\<^esub> s (X x))) \<longrightarrow> Q (put\<^bsub>a\<^esub> s (X t)))"
  by (auto simp add: g_orbital_on_def fbox_def g_orbital_eq fun_eq_iff)

lemma fdia_g_orbital_on: "|g_orbital_on a f G U S t\<^sub>0\<rangle> Q =
  (\<lambda>s. \<exists>X\<in>Sols U S (loc_subst a f s) t\<^sub>0 (get\<^bsub>a\<^esub> s).
        \<exists>t\<in>U (get\<^bsub>a\<^esub> s). (\<forall>x. x \<in> U (get\<^bsub>a\<^esub> s) \<and> x \<le> t \<longrightarrow> G (put\<^bsub>a\<^esub> s (X x))) \<and> Q (put\<^bsub>a\<^esub> s (X t)))"
  by (auto simp: fdia_def g_orbital_on_def g_orbital_eq fun_eq_iff)

lemma fbox_orbitals_prelim: "|g_orbital_on a f G U S t\<^sub>0] Q = 
  (\<lambda>s. (fbox (x\<acute>=(loc_subst a f s) & (\<lambda>c. G (put\<^bsub>a\<^esub> s c)) on U S @ t\<^sub>0) (Q \<circ> put\<^bsub>a\<^esub> s)) (get\<^bsub>a\<^esub> s))"
  unfolding fbox_g_orbital[unfolded clarify_fbox] fbox_g_orbital_on fun_eq_iff
  by (clarsimp simp: expr_defs)

lemma fdia_orbitals_prelim: "|g_orbital_on a f G U S t\<^sub>0\<rangle> Q =
  (\<lambda>s. (fdia (x\<acute>=(loc_subst a f s) & (\<lambda>c. G (put\<^bsub>a\<^esub> s c)) on U S @ t\<^sub>0) (Q \<circ> put\<^bsub>a\<^esub> s)) (get\<^bsub>a\<^esub> s))"
  by (auto simp: fdia_def g_orbital_on_def g_orbital_eq fun_eq_iff)

lemmas fbox_g_orbital_on_orbital = fbox_orbitals_prelim[
    unfolded clarify_fbox[of 
      "g_orbital (loc_subst _ _ _) (\<lambda>c. _ (put\<^bsub>_\<^esub> _ c)) _ _ _"
      "_ \<circ> put\<^bsub>_\<^esub> _", 
      symmetric
      ]
    ]

lemmas fdia_g_orbital_on_orbital = fdia_orbitals_prelim[
    unfolded clarify_fdia[of 
      "g_orbital (loc_subst _ _ _) (\<lambda>c. _ (put\<^bsub>_\<^esub> _ c)) _ _ _"
      "_ \<circ> put\<^bsub>_\<^esub> _", 
      symmetric
      ]
    ]

subsubsection \<open> ODE notation \<close>

text \<open> We add notation for the general version below.  \<close>

abbreviation g_ode_frame :: "('c::banach \<Longrightarrow> 'a) \<Rightarrow> 'a subst \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> real set) 
  \<Rightarrow> 'c set \<Rightarrow> real \<Rightarrow> 'a \<Rightarrow> 'a set" 
  where "g_ode_frame a \<sigma> G U S t\<^sub>0 \<equiv> g_orbital_on a (\<lambda>t. \<sigma>) G U S t\<^sub>0"

abbreviation g_ode_on :: "('c::banach \<Longrightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> real set) 
  \<Rightarrow> 'c set \<Rightarrow> real \<Rightarrow> 'a \<Rightarrow> 'a set"
  where "g_ode_on a f G U S t\<^sub>0 \<equiv> g_ode_frame a (subst_upd [\<leadsto>] a f) G U S t\<^sub>0"

abbreviation g_dl_ode_frame :: "('c::banach \<Longrightarrow> 'a) \<Rightarrow> 'a subst \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a set"
  where "g_dl_ode_frame a \<sigma> G \<equiv> g_ode_frame a \<sigma> G ({t. 0 \<le> t})\<^sub>e UNIV 0"

abbreviation g_dl_ode_on :: "('c::banach \<Longrightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a set"
  where "g_dl_ode_on a f G \<equiv> g_ode_on a f G ({t. 0 \<le> t})\<^sub>e UNIV 0"

no_notation (ASCII) disj (infixr "|" 30)

text \<open> We set up syntax for writing a list of derivatives. Internally, these are translated to
  a set of substitution maplets, but the user doesn't see that. \<close>

nonterminal deriv and derivs

syntax
  "_deriv"       :: "[svid, logic] => deriv"             ("_` = _")
  ""             :: "deriv => derivs"            ("_")
  "_Derivs"      :: "[deriv, derivs] => derivs" ("_,/ _")
  "_SDeriv"      :: "smaplets \<Rightarrow> derivs"

syntax
  "_ode_frame"       :: "svid \<Rightarrow> derivs \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_:{_ | _ on _ _ @ _}")
  "_dl_ode_frame"    :: "svid \<Rightarrow> derivs \<Rightarrow> logic \<Rightarrow> logic" ("_:{_ | _}")
  "_dl_ode_frame_ng" :: "svid \<Rightarrow> derivs \<Rightarrow> logic" ("_:{_}")
  "_g_dl_ode_on"     :: "derivs \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("{_ | _ on _ _ @ _}")
  "_ode"             :: "derivs \<Rightarrow> logic \<Rightarrow> logic" ("{_ | _}")
  "_ode_ng"          :: "derivs \<Rightarrow> logic" ("{_}")


(*  "_dl_derivs"       :: "derivs \<Rightarrow> logic" ("{_}") *)
(*
  "_g_dl_ode_on"     :: "svid \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("{(_)\<acute> = _ | _ on _ _ @ _}")
  "_ode"             :: "svid \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("{(_)\<acute> = _ | _}")
   "_ode_ng"          :: "svid \<Rightarrow> logic \<Rightarrow> logic" ("{(_)\<acute> = _}") *)

translations
  "_deriv x v"  => "_smaplet x v"
  "_Derivs d \<sigma>" => "_SMaplets d \<sigma>"
  "_deriv (_salphamk x) v"  <= "_SDeriv (_smaplet x v)"
  "_Derivs (_SDeriv d) (_SDeriv \<sigma>)"  <= "_SDeriv (_SMaplets d \<sigma>)"
  "_ode_frame a \<sigma> G U S t\<^sub>0" => "CONST g_ode_frame a (_Subst \<sigma>) (G)\<^sub>e (U)\<^sub>e S t\<^sub>0"
  "_ode_frame (_salphamk a) (_SDeriv \<sigma>) G U S t\<^sub>0" <= "CONST g_ode_frame a (_Subst \<sigma>) (G)\<^sub>e (U)\<^sub>e S t\<^sub>0"
  "_dl_ode_frame a \<sigma> G" => "CONST g_dl_ode_frame a (_Subst \<sigma>) (G)\<^sub>e"
  "_dl_ode_frame (_salphamk a) (_SDeriv \<sigma>) G" <= "CONST g_dl_ode_frame a (_Subst \<sigma>) (G)\<^sub>e"
  "_dl_ode_frame_ng a \<sigma>" == "_dl_ode_frame a \<sigma> (CONST True)"

  "_g_dl_ode_on \<sigma> G U S t\<^sub>0" => "CONST g_ode_frame (_smaplets_svids \<sigma>) (_Subst \<sigma>) (G)\<^sub>e (U)\<^sub>e S t\<^sub>0"
 
  "_ode \<sigma> G" => "CONST g_dl_ode_frame (_smaplets_svids \<sigma>) (_Subst \<sigma>) (G)\<^sub>e"
  "_ode (_deriv (_salphamk a) F) G" <= "CONST g_dl_ode_on a (F)\<^sub>e (G)\<^sub>e"
  "_ode_ng \<sigma>" == "_ode \<sigma> (CONST True)"

term "{x` = 1}"
term "{x` = $y, y` =$z + ($y)\<^sup>2 - $y | $y \<ge> 0}"
term "{(x, y)` = (1, 2*$x)}"
term "(x, y, z):{x` = 1, y` = 2*$x}"
term "(x,y):{(x, y)` = (1, 2*$x), z` = $y}"

lemma lens_upd_syntax_sugar: 
  "F (x \<leadsto> f) = (\<lambda>s. put\<^bsub>x\<^esub> (F s) (f s))"
  "F (x \<leadsto> f, y \<leadsto> g) = (\<lambda>s. put\<^bsub>y\<^esub> (put\<^bsub>x\<^esub> (F s) (f s)) (g s))"
  "F (x\<^sub>1 \<leadsto> f(x\<^sub>2 \<leadsto> g ($x\<^sub>3))) = (\<lambda>s. put\<^bsub>x\<^sub>1\<^esub> (F s) (put\<^bsub>x\<^sub>2\<^esub> (f s) (g s (get\<^bsub>x\<^sub>3\<^esub> s))))"
  by expr_simp+

lemma g_ode_frame_syntax_sugar:
  shows "(x,y):{x` = \<guillemotleft>f\<guillemotright> ($x), y` = g | G on U S @ t\<^sub>0} 
  = g_ode_frame (x +\<^sub>L y) (\<lambda>s. put\<^bsub>y\<^esub> (put\<^bsub>x\<^esub> s (f (get\<^bsub>x\<^esub> s))) (g s)) (G)\<^sub>e (U)\<^sub>e S t\<^sub>0"
    and "((x,y):{x` = f(y \<leadsto> h) | G on U S @ t\<^sub>0})
  = g_ode_frame (x +\<^sub>L y) (\<lambda>s. put\<^bsub>x\<^esub> s (put\<^bsub>y\<^esub> (f s) (h s))) (G)\<^sub>e (U)\<^sub>e S t\<^sub>0"
    and "g_ode_frame (x +\<^sub>L y) [x \<leadsto> \<guillemotleft>f\<guillemotright> ($x), y \<leadsto> g] (G)\<^sub>e (U)\<^sub>e S t\<^sub>0 
  = g_orbital_on (x +\<^sub>L y) (\<lambda>t s. put\<^bsub>y\<^esub> (put\<^bsub>x\<^esub> s (f (get\<^bsub>x\<^esub> s))) (g s)) G U S t\<^sub>0"
    and "g_ode_frame (x +\<^sub>L y) [x \<leadsto> f(y \<leadsto> h)] (G)\<^sub>e (U)\<^sub>e S t\<^sub>0 
  = g_orbital_on (x +\<^sub>L y) (\<lambda>t s. put\<^bsub>x\<^esub> s (put\<^bsub>y\<^esub> (f s) (h s))) G U S t\<^sub>0"
   apply (rule_tac f="\<lambda>s. g_ode_frame (x +\<^sub>L y) s (G)\<^sub>e (U)\<^sub>e S t\<^sub>0" in arg_cong)
  prefer 2 apply (rule_tac f="\<lambda>s. g_ode_frame (x +\<^sub>L y) s (G)\<^sub>e (U)\<^sub>e S t\<^sub>0" in arg_cong)
  using lens_indep_comm lens_indep_get lens_indep_get[OF lens_indep_sym]
  by expr_simp+

lemma g_ode_on_syntax_sugar:
  "g_ode_on x (f)\<^sub>e (G)\<^sub>e (U)\<^sub>e S t\<^sub>0 = g_orbital_on x (\<lambda>t. [x \<leadsto> f]) G U S t\<^sub>0"
  by (simp add: SEXP_def taut_def subst_upd_def subst_id_def)

lemma g_ode_frame_prod_sugar:
  "h \<bowtie> t \<Longrightarrow> {h` = \<guillemotleft>k\<guillemotright>, t` = 1 | $t \<le> (H\<^sub>u - h\<^sub>m)/\<guillemotleft>k\<guillemotright>} = {(h, t)` = (\<guillemotleft>k\<guillemotright>, 1) | $t \<le> (H\<^sub>u - h\<^sub>m)/\<guillemotleft>k\<guillemotright>}"
  unfolding g_orbital_on_def apply(clarsimp simp add: fun_eq_iff)
  by (rule_tac x="[h \<leadsto> \<guillemotleft>k\<guillemotright>, t \<leadsto> 1]" in arg_cong)
    (expr_simp add: lens_indep.lens_put_comm)

text \<open> We use the local-flow results to show the generalised counterparts. \<close>

definition local_flow_on :: "('s \<Rightarrow> 's) \<Rightarrow> ('c::{heine_borel, banach} \<Longrightarrow> 's) \<Rightarrow> real set 
  \<Rightarrow> 'c set \<Rightarrow> (real \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> bool"
  where "local_flow_on f A T S \<phi> = (\<forall>s. local_flow (loc_subst A (\<lambda>t. f) s 0) T S (loc_subst A \<phi> s))"

lemma fbox_g_ode_on: "|{x` = f | G on U S @ t\<^sub>0}] Q = 
  (\<lambda>s. \<forall>X \<in> Sols (U)\<^sub>e S (loc_subst x (\<lambda>t. [x \<leadsto> f]) s) t\<^sub>0 (get\<^bsub>x\<^esub> s). 
  \<forall>t\<in>U (get\<^bsub>x\<^esub> s). (\<forall>\<tau>\<in>down (U (get\<^bsub>x\<^esub> s)) t. G (put\<^bsub>x\<^esub> s (X \<tau>))) \<longrightarrow> Q (put\<^bsub>x\<^esub> s (X t)))"
  unfolding fbox_g_orbital_on_orbital fbox_g_orbital 
  by auto

lemma fdia_g_ode_on: "|{x` = f | G on U S @ t\<^sub>0}\<rangle> Q = 
  (\<lambda>s. \<exists>X \<in> Sols (U)\<^sub>e S (loc_subst x (\<lambda>t. [x \<leadsto> f]) s) t\<^sub>0 (get\<^bsub>x\<^esub> s). 
  \<exists>t\<in>U (get\<^bsub>x\<^esub> s). (\<forall>\<tau>\<in>down (U (get\<^bsub>x\<^esub> s)) t. G (put\<^bsub>x\<^esub> s (X \<tau>))) \<and> Q (put\<^bsub>x\<^esub> s (X t)))"
  unfolding fdia_g_orbital_on_orbital fdia_g_orbital
  by auto

lemma fbox_g_ode_frame_flow:
  fixes a::"'c::{heine_borel,banach} \<Longrightarrow> 's"
    and f::"'s \<Rightarrow> 's"
  assumes "local_flow_on f x T S \<phi>" and "vwb_lens x"
    and "\<And>s. s \<in> S \<Longrightarrow> 0 \<in> U s \<and> is_interval (U s) \<and> U s \<subseteq> T"
  shows "|g_ode_frame x f G U S 0] Q = (\<lambda>s. get\<^bsub>x\<^esub> s \<in> S 
    \<longrightarrow> (\<forall>t\<in>U (get\<^bsub>x\<^esub> s). (\<forall>\<tau>\<in>down (U (get\<^bsub>x\<^esub> s)) t. G (s \<triangleleft>\<^bsub>x\<^esub> \<phi> \<tau> s)) \<longrightarrow> Q (s \<triangleleft>\<^bsub>x\<^esub> \<phi> t s)))"
  apply (subst fbox_g_orbital_on_orbital, rule ext)
  apply (subst local_flow.fbox_g_ode_subset[OF assms(1,3)[unfolded local_flow_on_def, rule_format]])
  using assms(2) by expr_simp+

lemmas fbox_solve = fbox_g_ode_frame_flow[where T=UNIV]

lemma fdia_g_ode_frame_flow:
  fixes a::"'c::{heine_borel,banach} \<Longrightarrow> 's"
    and f::"'s \<Rightarrow> 's"
  assumes "local_flow_on f x T UNIV \<phi>" and "vwb_lens x"
    and "\<And>s. 0 \<in> U s \<and> is_interval (U s) \<and> U s \<subseteq> T"
  shows "|g_ode_frame x f G U UNIV 0\<rangle> Q = 
  (\<lambda>s. (\<exists>t\<in>U (get\<^bsub>x\<^esub> s). (\<forall>\<tau>\<in>down (U (get\<^bsub>x\<^esub> s)) t. G (s \<triangleleft>\<^bsub>x\<^esub> \<phi> \<tau> s)) \<and> Q (s \<triangleleft>\<^bsub>x\<^esub> \<phi> t s)))"
  apply (subst fdia_g_orbital_on_orbital, rule ext)
  apply (subst local_flow.fdia_g_ode_subset[OF assms(1,3)[unfolded local_flow_on_def, rule_format]])
  using assms(2) by expr_simp

lemma fbox_g_ode_on_flow:
  assumes "local_flow_on (subst_upd [\<leadsto>] A f) A T S \<phi>" and "vwb_lens A"
    and "\<And>s. 0 \<in> U s \<and> is_interval (U s) \<and> U s \<subseteq> T"
  shows "|g_ode_on A f G U S 0] Q = (\<lambda>s. get\<^bsub>A\<^esub> s \<in> S 
    \<longrightarrow> (\<forall>t\<in>U (get\<^bsub>A\<^esub> s). (\<forall>\<tau>\<in>down (U (get\<^bsub>A\<^esub> s)) t. G (s \<triangleleft>\<^bsub>A\<^esub> \<phi> \<tau> s)) \<longrightarrow> Q (s \<triangleleft>\<^bsub>A\<^esub> \<phi> t s)))"
  by (subst fbox_g_ode_frame_flow[OF assms], simp)

lemma fbox_g_dl_ode_frame_flow:
  assumes "local_flow_on f A T UNIV \<phi>"
    and "vwb_lens A" and "{t. 0 \<le> t} \<subseteq> T"
  shows "|g_dl_ode_frame A f G] Q = (\<lambda>s. 
  (\<forall>t\<ge>0. (\<forall>\<tau>\<in>{0..t}. G (s \<oplus>\<^sub>L \<phi> \<tau> s on A)) \<longrightarrow> Q (s \<oplus>\<^sub>L \<phi> t s on A)))"
  apply (subst fbox_g_ode_frame_flow[OF assms(1,2)])
  using assms(2,3) by auto

lemma fbox_g_dl_ode_on_flow:
  assumes "local_flow_on (subst_upd [\<leadsto>] A f) A T UNIV \<phi>"
    and "vwb_lens A" and "{t. 0 \<le> t} \<subseteq> T"
  shows "|g_dl_ode_on A f G] Q = (\<lambda>s. 
  (\<forall>t\<ge>0. (\<forall>\<tau>\<in>{0..t}. G (s \<oplus>\<^sub>L \<phi> \<tau> s on A)) \<longrightarrow> Q (s \<oplus>\<^sub>L \<phi> t s on A)))"
  by (subst fbox_g_dl_ode_frame_flow[OF assms], simp)

lemma "vwb_lens a \<Longrightarrow> g_dl_ode_frame a f G = g_dl_ode_on a f G"
proof
  fix s :: 'a
  assume hyp: "vwb_lens a"
  define T :: "'a \<Rightarrow> real set" where T_def: "T \<equiv> ({t. 0 \<le> t})\<^sub>e"
  define S :: "'a set" where S_def: "S \<equiv> UNIV"
  have "g_dl_ode_frame a f G s = g_ode_frame a f G T S 0 s" 
    by (simp add: T_def S_def)
  moreover have "g_dl_ode_on a f G s = g_ode_frame a (subst_upd [\<leadsto>] a f) G T S 0 s"
    by (simp add: T_def S_def)
  moreover have "g_ode_frame a f G T S 0 s = g_ode_frame a (subst_upd [\<leadsto>] a f) G T S 0 s"
    apply (rule_tac f="\<lambda>f. g_ode_frame a f G T S 0 s" in arg_cong)
    using hyp apply (auto simp: expr_defs lens_defs fun_eq_iff)
  oops (* vwb_lens a \<Longrightarrow> f x = put\<^bsub>a\<^esub> x (f x) *)

lemma fbox_g_ode_on_g_evol:
  assumes "local_flow_on (subst_upd [\<leadsto>] A f) A T UNIV \<phi>" and "vwb_lens A"
    and "\<And>s. 0 \<in> U s \<and> is_interval (U s) \<and> U s \<subseteq> T"
  shows "|g_ode_on A f G U UNIV 0] Q = |g_evol_on A \<phi> G U] Q"
  by (subst fbox_g_ode_on_flow[OF assms], subst fbox_g_evol_on[OF assms(2)])
    (auto simp: expr_defs lens_defs fun_eq_iff)

lemma fbox_g_dl_ode_frame_g_evol:
  assumes "local_flow_on f A T UNIV \<phi>"
    and "vwb_lens A" and "{t. 0 \<le> t} \<subseteq> T"
  shows "|g_dl_ode_frame A f G] Q = |g_evol_on A \<phi> G ({0..})\<^sub>e] Q"
  by (subst fbox_g_dl_ode_frame_flow[OF assms], subst fbox_g_evol_on[OF assms(2)])
    (auto simp: expr_defs lens_defs fun_eq_iff)

lemmas fbox_g_dL_easiest = fbox_g_dl_ode_frame_g_evol[of _ _ UNIV, simplified]

text \<open> A postcondition of a localised ODE is a postcondition of its unique localised solution. \<close>

definition local_lipschitz_on :: "('c::metric_space \<Longrightarrow> 's) \<Rightarrow> 'a::metric_space set 
  \<Rightarrow> 'c set \<Rightarrow> ('s \<Rightarrow> 's) \<Rightarrow> bool" 
  where "local_lipschitz_on A T S f = (\<forall> s. local_lipschitz T S (\<lambda>t c. get\<^bsub>A\<^esub> (f (put\<^bsub>A\<^esub> s c))))"


subsection \<open> Differential invariants \<close>

definition g_ode_inv :: "(real \<Rightarrow> 'a::real_normed_vector \<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> ('a \<Rightarrow> real set) \<Rightarrow> 'a set \<Rightarrow> 
  real \<Rightarrow> 'a pred \<Rightarrow> ('a \<Rightarrow> 'a set)" ("(1x\<acute>=_ & _ on _ _ @ _ DINV _ )") 
  where "(x\<acute>= f & G on U S @ t\<^sub>0 DINV I) = (x\<acute>= f & G on U S @ t\<^sub>0)"

lemma fbox_g_orbital_guard: 
  assumes "H = (\<lambda>s. G s \<and> Q s)"
  shows "|x\<acute>=f & G on U S @ t\<^sub>0] Q = |x\<acute>=f & G on U S @ t\<^sub>0] H "
  unfolding fbox_g_orbital using assms by auto

lemma fbox_g_orbital_on_guard: 
  assumes "H = (G \<and> Q)\<^sub>e"
  shows "|g_orbital_on a f G U S t\<^sub>0] Q = |g_orbital_on a f G U S t\<^sub>0] H "
  unfolding fbox_g_orbital_on
  using assms by auto

lemma fbox_inv:
  assumes "P \<le> I" and "I \<le> |F] I" and "I \<le> Q"
  shows "P \<le> |F] Q"
  by (rule order.trans[OF assms(1) order.trans[OF assms(2)]])
    (rule fbox_iso[OF assms(3)])

lemma
  assumes "P \<le> I" and "I \<le> |x\<acute>=f & G on U S @ t\<^sub>0] I" and "I \<le> Q"
  shows "P \<le> |x\<acute>=f & G on U S @ t\<^sub>0] Q"
  using fbox_inv[OF assms] .

lemma fbox_diff_inv: 
  "(I \<le> |x\<acute>=f & G on U S @ t\<^sub>0] I) = diff_inv U S G f t\<^sub>0 I"
  by (auto simp: diff_inv_def ivp_sols_def fbox_def g_orbital_eq)

lemma hoare_diff_inv:
  "\<^bold>{I\<^bold>} (x\<acute>=f & G on U S @ t\<^sub>0) \<^bold>{I\<^bold>} = diff_inv (U)\<^sub>e S (G)\<^sub>e f t\<^sub>0 (I)\<^sub>e"
  using fbox_diff_inv[of I f G U S t\<^sub>0] by (simp add: SEXP_def)

lemma fbox_diff_inv_on:
  "I \<le> fbox (g_orbital_on a f G U S t\<^sub>0) I = diff_inv_on I a f U S t\<^sub>0 G"
  by (auto simp: diff_inv_on_def ivp_sols_def fbox_def g_orbital_on_eq SEXP_def)

lemma fbox_diff_inv_on':
  "(I \<le> |g_orbital_on a f G U S t\<^sub>0] I) = diff_inv_on I a f U S t\<^sub>0 G"
  by (simp add: fbox_diff_inv_on expr_defs)

lemma hoare_diff_inv_on:
  "\<^bold>{I\<^bold>} (g_orbital_on a f G U S t\<^sub>0) \<^bold>{I\<^bold>} = diff_inv_on I a f U S t\<^sub>0 G"
  using fbox_diff_inv_on[of I a f G U S]
  by (simp add: SEXP_def)

lemma "(I \<le> |{a` = f | G on U S @ t\<^sub>0}] I) = diff_inv_on I a (\<lambda> _. [a \<leadsto> f]) (U)\<^sub>e S t\<^sub>0 (G)\<^sub>e"
  by (simp add: fbox_diff_inv_on expr_defs)

lemma dInduct_hoare_diff_inv_on:
  "\<^bold>{I\<^bold>} {a` = f | G on U S @ t\<^sub>0} \<^bold>{I\<^bold>} = diff_inv_on (I)\<^sub>e a (\<lambda>_. [a \<leadsto> f]) (U)\<^sub>e S t\<^sub>0 (G)\<^sub>e"
  using fbox_diff_inv_on[of I a "(\<lambda> _. [a \<leadsto> f])" G U S t\<^sub>0] by (simp add: SEXP_def)

lemma diff_inv_guard_ignore:
  assumes "I \<le> |x\<acute>= f & (\<lambda>s. True) on U S @ t\<^sub>0] I"
  shows "I \<le> |x\<acute>= f & G on U S @ t\<^sub>0] I"
  using assms 
  by (auto simp: fbox_diff_inv diff_inv_eq)

lemma diff_inv_on_guard_ignore:
  assumes "I \<le> |g_orbital_on a f (\<lambda>s. True) U S t\<^sub>0] I"
  shows "I \<le> |g_orbital_on a f G U S t\<^sub>0] I"
  using assms 
  by (auto simp: fbox_diff_inv_on diff_inv_on_eq expr_defs)

context local_flow
begin

lemma fbox_diff_inv_eq: 
  assumes "\<And>s. s \<in> S \<Longrightarrow> 0 \<in> U s \<and> is_interval (U s) \<and> U s \<subseteq> T"
  shows "diff_inv U S (\<lambda>s. True) (\<lambda>t. f) 0 I = 
  ((\<lambda>s. s \<in> S \<longrightarrow> I s) = |x\<acute>= (\<lambda>t. f) & (\<lambda>s. True) on U S @ 0] (\<guillemotleft>\<s>\<guillemotright> \<in> \<guillemotleft>S\<guillemotright> \<longrightarrow> I))"
  unfolding fbox_diff_inv[symmetric] 
  apply(subst fbox_g_ode_subset[OF assms], simp)+
  apply(clarsimp simp: le_fun_def fun_eq_iff, safe, force)
   apply(erule_tac x=0 in ballE)
  using init_time in_domain ivp(2) assms apply(force, force)
  apply(erule_tac x=x in allE, clarsimp, erule_tac x=t in ballE)
  using in_domain ivp(2) assms by force+

lemma diff_inv_eq_inv_set: 
  "diff_inv (\<lambda>s. T) S (\<lambda>s. True) (\<lambda>t. f) 0 I = (\<forall>s. I s \<longrightarrow> \<gamma>\<^sup>\<phi> s \<subseteq> {s. I s})"
  unfolding diff_inv_eq_inv_set orbit_def by simp

end

lemma fbox_g_odei: "P \<le> I \<Longrightarrow> I \<le> |x\<acute>= f & G on U S @ t\<^sub>0] I \<Longrightarrow> (\<lambda>s. I s \<and> G s) \<le> Q \<Longrightarrow> 
  P \<le> |x\<acute>= f & G on U S @ t\<^sub>0 DINV I] Q"
  unfolding g_ode_inv_def 
  apply(rule_tac b="|x\<acute>= f & G on U S @ t\<^sub>0] I" in order.trans)
   apply(rule_tac I="I" in fbox_inv, simp_all)
  apply(subst fbox_g_orbital_guard, simp)
  by (rule fbox_iso, force)

lemma hoare_g_odei: " \<^bold>{I\<^bold>} (x\<acute>= f & G on U S @ t\<^sub>0) \<^bold>{I\<^bold>}  \<Longrightarrow> `P \<longrightarrow> I` \<Longrightarrow> `I \<and> G \<longrightarrow> Q` \<Longrightarrow> 
 \<^bold>{P\<^bold>} (x\<acute>= f & G on U S @ t\<^sub>0 DINV I) \<^bold>{Q\<^bold>}"
  by (rule fbox_g_odei, simp_all add: SEXP_def taut_def le_fun_def)

lemma fbox_diff_invI: "(I)\<^sub>e \<le> |g_orbital_on a f G U S t\<^sub>0] I \<Longrightarrow> P \<le> (I)\<^sub>e \<Longrightarrow> (I \<and> G)\<^sub>e \<le> Q
  \<Longrightarrow> P \<le> |g_orbital_on a f G U S t\<^sub>0] Q"
  apply(rule_tac b="|g_orbital_on a f G U S t\<^sub>0] I" in order.trans)
   apply (rule_tac I=I in fbox_inv; expr_simp)
  by (subst fbox_g_orbital_on_guard, force)
    (rule fbox_iso, force)

lemmas fbox_diff_inv_rawI = fbox_diff_invI[unfolded clarify_fbox expr_defs]

lemma hoare_diff_inv_on_post_inv:
  assumes "`P \<longrightarrow> Q`" "\<^bold>{Q\<^bold>} {a` = f | G on U S @ t\<^sub>0} \<^bold>{Q\<^bold>}"
  shows "\<^bold>{P\<^bold>} {a` = f | G on U S @ t\<^sub>0} \<^bold>{Q\<^bold>}"
  using assms(2) by (rule hoare_conseq; simp add: assms)


subsection \<open> Derivation of the rules of dL \<close>

text \<open> We derive rules of differential dynamic logic (dL). First we present a
general version, then we show the rules as instances of the general ones.\<close>

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
      unfolding g_orbital_on_eq SEXP_def by auto
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
proof(subst fbox_def, subst g_orbital_on_eq, clarsimp)
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
  assumes "`P \<longrightarrow> I`" and "diff_inv_on I a f U S t\<^sub>0 G" and "`I \<longrightarrow> Q`"
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
  by (auto simp: lens_indep.lens_put_irr2 
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
  assumes inv_hyp: "diff_inv_on (J)\<^sub>e (x +\<^sub>L y) (\<lambda>t. f(y \<leadsto> (\<guillemotleft>A\<guillemotright> *\<^sub>V ($y) + \<guillemotleft>b\<guillemotright>))) (U \<circ> fst) UNIV 0 G"
    and y_hyps: "vwb_lens y" "y \<bowtie> x" "($y \<sharp>\<^sub>s f)" "$y \<sharp> G" and I_eq: "I = (J \\ $y)"
  shows "diff_inv_on I x (\<lambda>t. f) U S 0 G"
  using inv_hyp unfolding hoare_diff_inv_on[symmetric] SEXP_def I_eq
  by (rule diff_ghost_gen_rule[OF _ y_hyps, unfolded SEXP_def])

lemma has_vderiv_linear:
  fixes k :: real and b :: "'b :: real_normed_vector"
  assumes "k \<noteq> 0"
  defines "sol \<equiv> (\<lambda>s t. (- b + exp (k * t) *\<^sub>R (b + k *\<^sub>R s))/\<^sub>R k)"
  shows "D (sol s) = (\<lambda>t. k *\<^sub>R (sol s t) + b) on S"
  using assms unfolding sol_def
  by (auto simp: field_simps intro!: vderiv_intros)

lemma (* apparently we have to assume that (\<lambda>c. b (put\<^bsub>x + y\<^esub> s c)) 
  and (\<lambda>c. k (put\<^bsub>x + y\<^esub> s c)) is differentiable at (get\<^bsub>x + y\<^esub> s) ...
  see more about this in HS_Lie_Derivatives, same solution works for Darboux *)
  fixes k :: "'s \<Rightarrow> real" and b :: "'s \<Rightarrow> 'd::real_normed_vector"
  fixes x :: "'c::real_normed_vector \<Longrightarrow> 's"
    and y :: "'d::real_normed_vector \<Longrightarrow> 's"
  defines "sol \<equiv> (\<lambda>s t. (- b s + exp (k s * t) *\<^sub>R (b s + k s *\<^sub>R (get\<^bsub>y\<^esub> s)))/\<^sub>R (k s))"
  assumes "\<forall>s. D (\<lambda>c. b (put\<^bsub>y\<^esub> s c)) \<mapsto> (\<lambda>c. 0) (at (get\<^bsub>y\<^esub> s))"
    and "\<forall>s. D (\<lambda>c. k (put\<^bsub>y\<^esub> s c)) \<mapsto> (\<lambda>c. 0) (at (get\<^bsub>y\<^esub> s))"
    and "\<forall>s. k s \<noteq> 0"
  shows "D (sol s) = (\<lambda>t. (exp (k s * t)) *\<^sub>R (b s + k s *\<^sub>R get\<^bsub>y\<^esub> s)) on UNIV"
  using assms(2-) unfolding sol_def
  by (auto intro!: vderiv_intros)

lemma diff_ghost_gen_1rule:
  fixes x :: "'c::real_normed_vector \<Longrightarrow> 's"
    and y :: "'d::real_normed_vector \<Longrightarrow> 's"
    and k :: "'s \<Rightarrow> real" and b :: "'s \<Rightarrow> 'd"
(*   defines "sol \<equiv> (\<lambda>s c t. (- (b s) + exp ((k s) * t) *\<^sub>R ((b s) + (k s) *\<^sub>R c))/\<^sub>R (k s))"
 *)  
  assumes hyp: "\<^bold>{P\<^bold>} (g_orbital_on (x +\<^sub>L y) (\<lambda>t. f(y \<leadsto> (k *\<^sub>R ($y) + b))) G (U \<circ> fst) UNIV 0) \<^bold>{Q\<^bold>}" (* S' \<times> UNIV where S \<subseteq> S'*)
    and y_hyps: "vwb_lens y" "y \<bowtie> x" "($y \<sharp>\<^sub>s f)" "$y \<sharp> G"
    and x_hyps: "vwb_lens x"
    and expr_hyps: "\<forall>s d. k (put\<^bsub>y\<^esub> s d) = k s" "\<forall>s d. b (put\<^bsub>y\<^esub> s d) = b s" 
  shows "\<^bold>{P \\ $y\<^bold>} (g_orbital_on x (\<lambda>t. f) G U S 0) \<^bold>{Q \\ $y\<^bold>}"
  using hyp
  apply (clarsimp simp: fbox_g_orbital_on taut_def le_fun_def)
  apply (simp add: liberate_lens'[OF vwb_lens_mwb[OF y_hyps(1)]])
    (* simplifying notation *)
  using y_hyps x_hyps apply expr_simp
  apply (subst (asm) lens_indep_comm[of x y, OF lens_indep_sym], expr_simp?)+
  apply expr_simp
  apply (subst (asm) lens_indep_comm[of y x], expr_simp?)+
  apply (expr_simp add: ivp_sols_def, clarsimp)
  subgoal for s X t d
  apply (cases "k s \<noteq> 0")
    apply (erule allE[where x="put\<^bsub>y\<^esub> s d"] impE; expr_simp add: lens_indep.lens_put_irr2)
  apply (drule_tac x="\<lambda>t. (X t, Y t)" in spec, elim conjE impE; (intro conjI)?)
  prefer 3 subgoal
    apply (clarsimp simp: lens_indep.lens_put_irr2 )
    apply (erule_tac x=t in ballE; clarsimp?)
    apply (subst (asm) lens_indep_comm[of x y, OF lens_indep_sym], expr_simp)+
    by expr_auto
    prefer 2 subgoal
    apply  (simp_all add: lens_indep.lens_put_irr2) (* sol_def *)
    sorry
  subgoal
    apply (rule vderiv_pairI, force simp: lens_indep.lens_put_irr2)
     prefer 2 
apply (auto simp: lens_indep.lens_put_irr2 fun_eq_iff
      lens_indep_comm[of x y, OF lens_indep_sym])[1]

    apply (subgoal_tac "D (\<lambda>t. sol (put\<^bsub>x\<^esub> s (X t)) s' t) = (\<lambda>t. (k (put\<^bsub>x\<^esub> s (X t))) *\<^sub>R (sol (put\<^bsub>x\<^esub> s (X t)) s' t) + (b (put\<^bsub>x\<^esub> s (X t)))) on (U (get\<^bsub>x\<^esub> s))", assumption)
  subgoal unfolding sol_def by (rule has_vderiv_linear)
  apply (auto simp: lens_indep.lens_put_irr2 fun_eq_iff
      lens_indep_comm[of x y, OF lens_indep_sym])[1]
  apply expr_simp
    apply (erule allE[where x="put\<^bsub>y\<^esub> s s'"] impE; expr_simp)
    apply (drule_tac x="\<lambda> t. (X t, t *\<^sub>R (b (put\<^bsub>x\<^esub> s (X t))) + s')" in spec, elim conjE impE; (intro conjI)?)
       prefer 4 subgoal
      apply (clarsimp simp: lens_indep.lens_put_irr2 )
      apply (erule_tac x=t in ballE; clarsimp?)
      apply (subst (asm) lens_indep_comm[of x y, OF lens_indep_sym], expr_simp)+
      by expr_auto
    apply (auto simp: expr_defs lens_indep.lens_put_irr2 
        lens_indep_comm[of x y, OF lens_indep_sym] intro!: vderiv_intros)
  done
  oops


lemma diff_ghost_gen_1rule:
  fixes b :: "'b :: real_normed_vector" and k :: real
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
  by (auto simp: lens_indep.lens_put_irr2 
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
  fixes b :: "'b :: real_normed_vector"
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
  fixes b :: "'b :: real_normed_vector" 
  assumes inv_hyp: "diff_inv_on J (x +\<^sub>L y) (\<lambda>t. f(y \<leadsto> \<guillemotleft>k\<guillemotright> *\<^sub>R $y + \<guillemotleft>c\<guillemotright>)) (U \<circ> fst) UNIV 0 G"
    and y_hyps: "vwb_lens y" "y \<bowtie> x" "$y \<sharp>\<^sub>s f" "$y \<sharp> G" and I_eq: "I = J \\ $y"
  shows "diff_inv_on I x (\<lambda>t. f) U UNIV 0 G"
  using inv_hyp unfolding hoare_diff_inv_on[symmetric] SEXP_def I_eq
  by (rule diff_ghost_gen_1rule[OF _ y_hyps, unfolded SEXP_def])

lemma diff_ghost_inv_very_simple:
  assumes y_hyps: "vwb_lens y" "y \<bowtie> a" "$y \<sharp>\<^sub>s f" "$y \<sharp> G"
    and inv_hyp: "diff_inv_on (I)\<^sub>e (a +\<^sub>L y) (\<lambda>t. f(y \<leadsto> \<guillemotleft>k\<guillemotright> *\<^sub>R $y)) (Collect ((\<le>) 0))\<^sub>e UNIV 0 G"
  shows "diff_inv_on (I \\ $y)\<^sub>e a (\<lambda>t. f) (Collect ((\<le>) 0))\<^sub>e UNIV 0 G"
  using diff_ghost_inv_1rule[OF _ y_hyps, where c=0 and k=k]
  using inv_hyp
  by expr_simp

lemma diff_ghost_rule_very_simple:
  fixes y :: "real \<Longrightarrow> _"
  assumes inv_hyp:"\<^bold>{J\<^bold>} g_dl_ode_frame (a +\<^sub>L y) (f(y \<leadsto> \<guillemotleft>k\<guillemotright> *\<^sub>R $y)) G \<^bold>{J\<^bold>}"
    and y_hyps: "vwb_lens y" "y \<bowtie> a" "$y \<sharp>\<^sub>s f" "$y \<sharp> G"
    and I_eq:  "(I)\<^sub>e = J \\ $y" 
  shows "\<^bold>{I\<^bold>} g_dl_ode_frame a f G \<^bold>{I\<^bold>}"
  using assms
  by (metis SEXP_def diff_ghost_inv_very_simple fbox_diff_inv_on) 

no_notation Union ("\<mu>")


subsection \<open> Proof Methods \<close>

thm fbox_g_ode_frame_flow fbox_solve fbox_g_dL_easiest
(* most used solution theorems in arch2022:
  * fbox_g_ode_frame_flow
  * fbox_solve (which is essentially the one above)
  * fbox_g_dL_easiest (which transforms g_dl_ode_frames into g_evol_ons)
*)

text \<open> A simple tactic for Hoare logic that uses weakest liberal precondition calculations \<close>

method hoare_wp_simp uses local_flow = ((rule_tac hoare_loopI)?; simp add: unrest_ssubst 
    var_alpha_combine wp usubst usubst_eval 
    refine_iff_implies fbox_g_dL_easiest[OF local_flow])

method hoare_wp_auto uses local_flow = (hoare_wp_simp local_flow: local_flow; expr_auto)

method diff_inv_on_single_eq_intro = 
  (rule diff_inv_on_eqI
  | rule diff_inv_on_raw_eqI
  ) \<comment> \<open> applies @{term diff_inv_on}-rule \<close>

method diff_inv_on_eq = (
    (simp only: expr_defs hoare_diff_inv_on fbox_diff_inv_on)?, 
    (diff_inv_on_single_eq_intro; expr_auto),
    (force simp: power2_eq_square intro!: vderiv_intros)?)

method diff_inv_on_single_ineq_intro for dnu dmu::"'a \<Rightarrow> real" = 
  (rule diff_inv_on_leqI[where \<mu>'=dmu and \<nu>'=dnu]
  | rule diff_inv_on_lessI[where \<mu>'=dmu and \<nu>'=dnu]
  | rule diff_inv_on_raw_leqI[where \<mu>'=dmu and \<nu>'=dnu]
  | rule diff_inv_on_raw_lessI[where \<mu>'=dmu and \<nu>'=dnu]
  ) \<comment> \<open> applies @{term diff_inv_on}-rule \<close>

method diff_inv_on_ineq for dnu dmu::"'a \<Rightarrow> real" = (
    (simp only: expr_defs hoare_diff_inv_on fbox_diff_inv_on)?, 
    diff_inv_on_single_ineq_intro dnu dmu;
    (force intro!: vderiv_intros)?)

method vderiv = ((expr_simp)?; force intro!: vderiv_intros simp: vec_eq_iff field_simps)

method lipschitz for L :: real = 
  (unfold local_lipschitz_on_def local_lipschitz_def lipschitz_on_def dist_norm, clarify, 
    rule exI[where x="L"], expr_auto, (rule exI[where x="L"], auto)?)

method lens_c1_lipschitz for df uses typeI =
 ((rule_tac \<DD>=df in c1_local_lipschitz; expr_auto), fastforce intro: typeI intro!: derivative_intros, 
   fastforce intro: typeI continuous_intros)

method local_flow for L :: real =
  ((auto simp add: local_flow_on_def)?, (unfold_locales, auto), (lipschitz L, vderiv, expr_auto))

method local_flow_auto =
  (local_flow "1/4" | local_flow "1/2" | local_flow "1" | local_flow "2")

method dDiscr = (rule_tac nmods_invariant[OF nmods_g_orbital_on_discrete']; unrest)

method diff_inv_on_weaken_ineq for I::"'a \<Rightarrow> bool" 
  and dLeq dGeg::"'a \<Rightarrow> real" = (
    (rule fbox_inv[where I=I]),
    (expr_simp add: le_fun_def),
    (diff_inv_on_ineq dLeq dGeg),
    vderiv,
    (expr_simp add: le_fun_def)
    )

method diff_cut_ineq for I::"'a \<Rightarrow> bool" (* create tactic move to guard where nmods... *)
  and dLeq dGeg::"'a \<Rightarrow> real" = (
    (rule diff_cut_on_rule[where C=I]),
    (diff_inv_on_weaken_ineq I dLeq dGeg)
    )

method dGhost for y :: "real \<Longrightarrow> 's" and J :: "'s \<Rightarrow> bool" and k :: real 
  = (rule diff_ghost_rule_very_simple[where y="y" and J="J" and k="k"]
    ,simp_all add: unrest usubst usubst_eval unrest_ssubst liberate_as_subst)


(**** DARBOUX ****)


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
  apply (rule diff_inv_on_raw_eqI; clarsimp?)
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



end