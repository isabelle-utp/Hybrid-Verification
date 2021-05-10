(*  Title: HS verification with lenses *)

section \<open> HS verification with lenses \<close>

text \<open> We use shallow expressions to rephrase the properties for hybrid systems in a 
cleaner presentation. \<close>

theory HS_Lens_Spartan
  imports "HS_Lens_ODEs"

begin

subsection \<open> Verification components \<close>

type_synonym 'a pred = "'a \<Rightarrow> bool"
type_synonym 's prog = "'s \<Rightarrow> 's set"

named_theorems prog_defs

no_notation Transitive_Closure.rtrancl ("(_\<^sup>*)" [1000] 999)

notation Union ("\<mu>")

subsection \<open>Verification of regular programs\<close>

text \<open> Lemmas for verification condition generation \<close>

\<comment> \<open> Forward box operator \<close>

named_theorems wp

definition fbox :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'b pred \<Rightarrow> 'a pred"
  where "fbox F P = (\<lambda>s. (\<forall>s'. s' \<in> F s \<longrightarrow> P s'))"

syntax "_fbox" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("|_] _" [0,81] 82)
translations "_fbox F P" == "CONST fbox F (P)\<^sub>e"

expr_ctr fbox

lemma fbox_iso: "P \<le> Q \<Longrightarrow> |F] P \<le> |F] Q"
  unfolding fbox_def by auto

lemma fbox_anti: "\<forall>s. F\<^sub>1 s \<subseteq> F\<^sub>2 s \<Longrightarrow> |F\<^sub>2] P \<le> |F\<^sub>1] P"
  unfolding fbox_def by auto

lemma fbox_invs: 
  assumes "(I)\<^sub>e \<le> |F] I" and "(J)\<^sub>e \<le> |F] J"
  shows "(I \<and> J)\<^sub>e \<le> |F] (I \<and> J)"
    and "(I \<or> J)\<^sub>e \<le> |F] (I \<or> J)"
  using assms unfolding fbox_def SEXP_def by auto

definition fdia :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'b pred \<Rightarrow> 'a pred"
  where "fdia F P = (\<lambda>s. (\<exists>s'. s' \<in> F s \<and> P s'))"

syntax "_fdia" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("|_\<rangle> _" [0,81] 82)
translations "_fdia F P" == "CONST fdia F (P)\<^sub>e"

lemma fdia_iso: "P \<le> Q \<Longrightarrow> |F\<rangle> P \<le> |F\<rangle> Q"
  unfolding fdia_def by auto

\<comment> \<open> Hoare triple \<close>

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

lemma hoare_conj: 
  assumes "\<^bold>{p\<^bold>}Q\<^bold>{r\<^bold>}" "\<^bold>{p\<^bold>}Q\<^bold>{s\<^bold>}" 
  shows "\<^bold>{p\<^bold>}Q\<^bold>{r \<and> s\<^bold>}"
  using assms by (simp add: fbox_def le_fun_def)

lemma hoare_weaken_pre:
  "\<^bold>{p\<^bold>}Q\<^bold>{r\<^bold>} \<Longrightarrow> \<^bold>{p \<and> q\<^bold>}Q\<^bold>{r\<^bold>}"
  "\<^bold>{q\<^bold>}Q\<^bold>{r\<^bold>} \<Longrightarrow> \<^bold>{p \<and> q\<^bold>}Q\<^bold>{r\<^bold>}"
  by (simp_all add: le_fun_def)

lemma hoare_conseq: 
  assumes "\<^bold>{p\<^sub>2\<^bold>}S\<^bold>{q\<^sub>2\<^bold>}" "`p\<^sub>1 \<longrightarrow> p\<^sub>2`" "`q\<^sub>2 \<longrightarrow> q\<^sub>1`"
  shows "\<^bold>{p\<^sub>1\<^bold>}S\<^bold>{q\<^sub>1\<^bold>}"
  using assms by (auto simp add: fbox_def expr_defs)

\<comment> \<open> Skip \<close>

definition [prog_defs]: "skip = (\<lambda>s. {s})"

lemma fbox_skip [wp]: "|skip] P = P"
  unfolding fbox_def skip_def by simp

lemma fdia_skip [wp]: "|skip\<rangle> P = P"
  unfolding fdia_def skip_def by simp

lemma hoare_skip: "\<^bold>{P\<^bold>} skip \<^bold>{P\<^bold>}"
  by (auto simp: fbox_skip)

\<comment> \<open> Abort \<close>

definition [prog_defs]: "abort = (\<lambda>s. {})"

lemma fbox_abort [wp]: "|abort] P = (True)\<^sub>e"
  unfolding fbox_def abort_def by auto

lemma fdia_abort: "|abort\<rangle> P = (False)\<^sub>e"
  unfolding fdia_def abort_def by expr_simp

lemma hoare_abort: "\<^bold>{P\<^bold>} abort \<^bold>{Q\<^bold>}"
  by (auto simp: fbox_abort)

\<comment> \<open> Tests \<close>

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

\<comment> \<open> Assignments \<close>

definition assigns :: "'s subst \<Rightarrow> 's \<Rightarrow> 's set" ("\<langle>_\<rangle>") where 
[prog_defs]: "\<langle>\<sigma>\<rangle> = (\<lambda> s. {\<sigma> s})"

syntax
  "_assign" :: "svid \<Rightarrow> logic \<Rightarrow> logic" ("(2_ ::= _)" [65, 64] 64)

translations
  "_assign x e" == "\<langle>CONST subst_upd [\<leadsto>] x (e)\<^sub>e\<rangle>" (* "\<langle>[x \<leadsto>\<^sub>s e]\<rangle>" *)

lemma fbox_assign: "|x ::= e] Q = (Q\<lbrakk>e/x\<rbrakk>)\<^sub>e"
  by (simp add: assigns_def expr_defs fbox_def)

lemma hoare_assign: "\<^bold>{Q\<lbrakk>e/x\<rbrakk>\<^bold>} (x ::= e) \<^bold>{Q\<^bold>}"
  by (auto simp: fbox_assign)

lemma fbox_assigns [wp]: "|\<langle>\<sigma>\<rangle>] Q = \<sigma> \<dagger> (Q)\<^sub>e"
  by (simp add: assigns_def expr_defs fbox_def)

lemma fdia_assign: "|x ::= e\<rangle> P = (P\<lbrakk>e/x\<rbrakk>)\<^sub>e"
  by (simp add: assigns_def expr_defs fdia_def)

\<comment> \<open> Nondeterministic assignments \<close>

definition nondet_assign :: "('a \<Longrightarrow> 's) \<Rightarrow> 's prog" ("(2_ ::= ?)" [64] 65)
  where [prog_defs]: "(x ::= ?) = (\<lambda>s. {(put\<^bsub>x\<^esub> s k)|k. True})"

lemma fbox_nondet_assign [wp]: "|x ::= ?] P = (\<forall>k. P\<lbrakk>k/x\<rbrakk>)\<^sub>e"
  unfolding fbox_def nondet_assign_def vec_upd_eq by (auto simp add: fun_eq_iff expr_defs)

lemma hoare_nondet_assign: "\<^bold>{\<forall>k. Q\<lbrakk>k/x\<rbrakk>\<^bold>} (x ::= ?) \<^bold>{Q\<^bold>}"
  by (simp add: fbox_nondet_assign)

lemma fdia_nondet_assign: "|x ::= ?\<rangle> P = (\<exists>k. P\<lbrakk>k/x\<rbrakk>)\<^sub>e"
  unfolding fdia_def nondet_assign_def vec_upd_eq 
  by (auto simp add: fun_eq_iff expr_defs)

\<comment> \<open> Nondeterministic choice \<close>

definition nondet_choice :: "'s prog \<Rightarrow> 's prog \<Rightarrow> 's prog" (infixr "\<sqinter>" 60) where
[prog_defs]: "nondet_choice F G = (\<lambda> s. F s \<union> G s)"

lemma fbox_choice [wp]: "|F \<sqinter> G] P = ( |F] P \<and> |G] P)\<^sub>e"
  unfolding fbox_def nondet_choice_def by auto

lemma le_fbox_choice_iff: "P \<le> |F \<sqinter> G] Q \<longleftrightarrow> P \<le> |F] Q \<and> P \<le> |G] Q"
  unfolding fbox_def nondet_choice_def by auto

lemma hoare_choice: 
  "\<^bold>{P\<^bold>} F \<^bold>{Q\<^bold>} \<Longrightarrow> \<^bold>{P\<^bold>} G \<^bold>{Q\<^bold>} \<Longrightarrow> \<^bold>{P\<^bold>} (F \<sqinter> G) \<^bold>{Q\<^bold>}"
  by (subst le_fbox_choice_iff, simp)

lemma fdia_choice: "|F \<sqinter> G\<rangle> P = (\<lambda>s. ( |F\<rangle> P) s \<or> ( |G\<rangle> P ) s)"
  unfolding fdia_def nondet_choice_def by auto

\<comment> \<open> Sequential composition \<close>

definition kcomp :: "('a \<Rightarrow> 'b set) \<Rightarrow> ('b \<Rightarrow> 'c set) \<Rightarrow> ('a  \<Rightarrow> 'c set)" (infixl ";" 62) where
  [prog_defs]: "F ; G = \<mu> \<circ> \<P> G \<circ> F"

lemma kcomp_eq: "(f ; g) x = \<Union> {g y |y. y \<in> f x}"
  unfolding kcomp_def image_def by auto

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

\<comment> \<open> Conditional statement \<close>

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

\<comment> \<open> Finite iteration \<close>

definition kpower :: "('a \<Rightarrow> 'a set) \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> 'a set)" 
  where [prog_defs]: "kpower f n = (\<lambda>s. ((;) f ^^ n) skip s)"

lemma kpower_base:
  shows "kpower f 0 s = {s}" and "kpower f (Suc 0) s = f s"
  unfolding kpower_def by (auto simp: kcomp_eq skip_def)

lemma kpower_simp: "kpower f (Suc n) s = (f ; kpower f n) s"
  unfolding kcomp_eq 
  apply(induct n)
  unfolding kpower_base 
   apply(force simp: subset_antisym)
  unfolding kpower_def kcomp_eq by simp

definition kleene_star :: "('a \<Rightarrow> 'a set) \<Rightarrow> ('a \<Rightarrow> 'a set)" ("(_\<^sup>*)" [1000] 999)
  where [prog_defs]: "(f\<^sup>*) s = \<Union> {kpower f n s |n. n \<in> UNIV}"

lemma kpower_inv: 
  fixes F :: "'a \<Rightarrow> 'a set"
  assumes "\<forall>s. I s \<longrightarrow> (\<forall>s'. s' \<in> F s \<longrightarrow> I s')" 
  shows "\<forall>s. I s \<longrightarrow> (\<forall>s'. s' \<in> (kpower F n s) \<longrightarrow> I s')"
  apply(clarsimp, induct n)
  unfolding kpower_base kpower_simp 
   apply(simp_all add: kcomp_eq, clarsimp) 
  apply(subgoal_tac "I y", simp)
  using assms by blast

lemma kstar_inv: "I \<le> |F] I \<Longrightarrow> I \<le> |F\<^sup>*] I"
  unfolding kleene_star_def fbox_def 
  apply clarsimp
  apply(unfold le_fun_def, subgoal_tac "\<forall>x. I x \<longrightarrow> (\<forall>s'. s' \<in> F x \<longrightarrow> I s')")
  using kpower_inv[of I F] by blast simp

lemma fdia_kstar_inv: "I \<le> |F\<rangle> I \<Longrightarrow> I \<le> |F\<^sup>*\<rangle> I"
  unfolding kleene_star_def fdia_def apply(clarsimp simp: le_fun_def)
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

lemma fdia_kstarI:
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

lemma hoare_kstarI: "`P \<longrightarrow> I` \<Longrightarrow> `I \<longrightarrow> Q` \<Longrightarrow> \<^bold>{I\<^bold>} F \<^bold>{I\<^bold>} \<Longrightarrow> \<^bold>{P\<^bold>} F\<^sup>* \<^bold>{Q\<^bold>}"
  by (rule fbox_kstarI) (auto simp: SEXP_def taut_def)

\<comment> \<open> Loops with annotated invariants \<close>

definition loopi :: "('a \<Rightarrow> 'a set) \<Rightarrow> 'a pred \<Rightarrow> ('a \<Rightarrow> 'a set)" 
  where [prog_defs]: "loopi F I \<equiv> (F\<^sup>*)"

syntax "_loopi" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("LOOP _ INV _ " [0, 63] 64)
translations "_loopi F I" == "CONST loopi F (I)\<^sub>e"

lemma change_loopI: "LOOP X INV G = LOOP X INV I"
  unfolding loopi_def by simp

lemma fbox_loopI: "P \<le> I \<Longrightarrow> I \<le> Q \<Longrightarrow> I \<le> |F] I \<Longrightarrow> P \<le> |LOOP F INV I] Q"
  unfolding loopi_def using fbox_kstarI[of "P"] by (auto simp: SEXP_def)

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

\<comment> \<open> Framing \<close>

definition frame :: "'s scene \<Rightarrow> 's prog \<Rightarrow> 's prog" where
[prog_defs]: "frame a P = (\<lambda> s. {s'. s = cp\<^bsub>a\<^esub> s s' \<and> s' \<in> P s})"

syntax "_frame" :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("_:[_]" [65] 65)
translations "_frame a P" == "CONST frame a P"

lemma frame_UNIV: "\<Sigma>:[P] = P"
  by (simp add: frame_def lens_defs)

lemma frame_skip: "idem_scene a \<Longrightarrow> a:[skip] = skip"
  by (auto simp add: skip_def frame_def fun_eq_iff)
  
lemma frame_assign_in:
  assumes "vwb_lens x" "idem_scene a" "x \<in>\<^sub>S a"
  shows "a:[x ::= v] = x ::= v"
  using assms
  by (auto simp add: prog_defs expr_defs fun_eq_iff lens_member_put)
  
definition not_modifies :: "'s prog \<Rightarrow> 's scene \<Rightarrow> bool" where
  "not_modifies P a = (\<forall> s s'. s' \<in> P s \<longrightarrow> s' \<approx>\<^sub>S s on a)" 

syntax "_not_modifies" :: "logic \<Rightarrow> salpha \<Rightarrow> logic" (infix "nmods" 30)
translations "_not_modifies P a" == "CONST not_modifies P a"

named_theorems closure

(* FIXME: The following rule is an inefficient way to calculate modification; 
  replace with scene membership laws. *)

lemma nmods_union [closure]:
  assumes "P nmods A" "P nmods B"
  shows "P nmods (A ; B)"
  using assms
  by (auto simp add: not_modifies_def prog_defs)
     (metis scene_equiv_def scene_override_union scene_union_incompat scene_union_unit)

lemma nmods_skip [closure]: "idem_scene a \<Longrightarrow> skip nmods a"
  by (simp add: not_modifies_def prog_defs scene_equiv_def)

lemma nmods_seq [closure]:
  assumes "P nmods a" "Q nmods a"
  shows "(P ; Q) nmods a"
  using assms 
  by (auto simp add: not_modifies_def prog_defs scene_equiv_def, metis scene_override_overshadow_right)

lemma nmods_if [closure]:
  assumes "P nmods a" "Q nmods a"
  shows "IF b THEN P ELSE Q nmods a"
  using assms by (auto simp add: not_modifies_def prog_defs)

lemma nmods_choice [closure]:
  assumes "P nmods a" "Q nmods a"
  shows "P \<sqinter> Q nmods a"  
  using assms by (auto simp add: not_modifies_def prog_defs)

lemma nmods_test [closure]:
  "idem_scene a \<Longrightarrow> \<questiondown>b? nmods a"
  by (auto simp add: not_modifies_def prog_defs scene_equiv_def)

lemma lens_not_member_put:
  assumes "vwb_lens x" "idem_scene a" "x \<notin>\<^sub>S a"
  shows "put\<^bsub>x\<^esub> s v \<oplus>\<^sub>S s on a = put\<^bsub>x\<^esub> s v"
  by (metis assms(1) assms(2) assms(3) idem_scene_uminus lens_member_put scene_override_commute scene_override_overshadow_right)
  
lemma nmods_assign [closure]:
  assumes "vwb_lens x" "idem_scene a" "x \<notin>\<^sub>S a"
  shows "x ::= e nmods a"
  by (expr_simp add: not_modifies_def assigns_def, simp add: lens_not_member_put assms)

lemma nmods_g_orbital_on_discrete [closure]:
  assumes "vwb_lens x" "idem_scene a" "x \<notin>\<^sub>S a"
  shows "(g_orbital_on x f G U S t\<^sub>0) nmods a"
  using assms
  by (auto simp add: g_orbital_on_def not_modifies_def lens_not_member_put scene_equiv_def)

lemma nmods_g_orbital_on_discrete' [closure]:
  assumes "vwb_lens x" 
  shows "(g_orbital_on x f G U S t\<^sub>0) nmods (- $x)"
  by (rule nmods_g_orbital_on_discrete, simp_all add: assms lens_member_def lens_override_def)

lemma nmods_g_orbital_on_discrete_lens [closure]:
  assumes "vwb_lens A" "vwb_lens x" "x \<bowtie> A"
  shows "(g_orbital_on A f G U S t\<^sub>0) nmods $x"
  by (rule nmods_g_orbital_on_discrete, simp_all add: assms lens_indep_sym) 

lemma nmods_via_fbox:
  "\<lbrakk> vwb_lens x; \<And> v. |P] ($x = \<guillemotleft>v\<guillemotright>) = ($x = \<guillemotleft>v\<guillemotright>)\<^sub>e \<rbrakk> \<Longrightarrow> P nmods $x"
  by (expr_simp add: fbox_def not_modifies_def, auto)
     (metis UNIV_I lens_override_def lens_scene_override mwb_lens.weak_get_put vwb_lens_iff_mwb_UNIV_src)

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

subsection \<open> Verification of hybrid programs \<close>

text \<open> Verification by providing evolution \<close>

definition g_evol :: "(('a::ord) \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b pred \<Rightarrow> ('b \<Rightarrow> 'a set) \<Rightarrow> ('b \<Rightarrow> 'b set)" ("EVOL")
  where "g_evol \<phi> G U = (\<lambda>s. g_orbit (\<lambda>t. \<phi> t s) G (U s))"

definition g_evol_on :: "('c::real_normed_vector \<Longrightarrow> 'a) \<Rightarrow> (real \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> real set) \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "g_evol_on a \<phi> G U \<equiv> (\<lambda> s. put\<^bsub>a\<^esub> s ` (g_evol (loc_subst a \<phi> s) (\<lambda> v. G (put\<^bsub>a\<^esub> s v)) U (get\<^bsub>a\<^esub> s)))"

lemma g_evol_on_alt_def:
  "vwb_lens a \<Longrightarrow> g_evol_on a \<phi> G U s = {s \<oplus>\<^sub>L \<phi> t s on a |t. t \<in> U (get\<^bsub>a\<^esub> s) \<and> (\<forall>\<tau>. \<tau> \<in> down (U (get\<^bsub>a\<^esub> s)) t \<longrightarrow> G (s \<oplus>\<^sub>L \<phi> \<tau> s on a))}"
  by (auto simp add: g_evol_on_def g_evol_def g_orbit_eq lens_defs)

abbreviation g_evol_eq :: "('c::real_normed_vector \<Longrightarrow> 'b) \<Rightarrow> (real \<Rightarrow> ('c, 'b) expr) \<Rightarrow> 'b pred \<Rightarrow> ('c \<Rightarrow> real set) \<Rightarrow> ('b \<Rightarrow> 'b set)" where
"g_evol_eq a f G U \<equiv> g_evol_on a (\<lambda> \<tau>. subst_upd [\<leadsto>] a (f \<tau>)) G U"

no_notation disj  (infixr "|" 30)

syntax
  "_time_var" :: id
  "_EVOL" :: "svid \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("{EVOL _ = _ | _ on _}")
  "_EVOL_ge" :: "svid \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("{EVOL _ = _ | _}")
  "_EVOL_simp" :: "svid \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("{EVOL _ = _}")

parse_translation 
  \<open>[(@{syntax_const "_time_var"}, fn ctx => fn term => Syntax.free "\<tau>")]\<close>

translations
  "_EVOL a f G U" => "CONST g_evol_eq a (\<lambda> _time_var. (f)\<^sub>e) (G)\<^sub>e (U)\<^sub>e"
  "_EVOL a f G U" <= "CONST g_evol_eq a (\<lambda> b. (f)\<^sub>e) (G)\<^sub>e (U)\<^sub>e"
  "_EVOL_ge a f G" == "_EVOL a f G {0..}"
  "_EVOL_simp a f" == "_EVOL_ge a f (CONST True)"

term "{EVOL x = \<guillemotleft>\<tau>\<guillemotright> * 5 + $x}"

term "{EVOL (x, y) = ($x * cos \<guillemotleft>\<tau>\<guillemotright> + $y * sin \<guillemotleft>\<tau>\<guillemotright>, - $x * sin \<guillemotleft>\<tau>\<guillemotright> + $y * cos \<guillemotleft>\<tau>\<guillemotright>) | true on UNIV}"

lemma fbox_g_evol: 
  fixes \<phi> :: "('a::preorder) \<Rightarrow> 'b \<Rightarrow> 'b"
  shows "|EVOL \<phi> G U] Q = (\<lambda>s. \<forall>t\<in>U s. (\<forall>\<tau>\<in>down (U s) t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s))"
  unfolding g_evol_def g_orbit_eq fbox_def by auto

lemma fdia_g_evol: 
  fixes \<phi> :: "('a::preorder) \<Rightarrow> 'b \<Rightarrow> 'b"
  shows "|EVOL \<phi> G U\<rangle> Q = (\<lambda>s. \<exists>t\<in>U s. (\<forall>\<tau>\<in>down (U s) t. G (\<phi> \<tau> s)) \<and> Q (\<phi> t s))"
  unfolding g_evol_def g_orbit_eq fdia_def by auto

lemma fbox_g_evol': 
  fixes \<phi> :: "('a::preorder) \<Rightarrow> 'b \<Rightarrow> 'b"
  shows "|EVOL \<phi> G U] Q = (\<forall>t\<in>U. ((\<forall>\<tau>\<in>down U \<guillemotleft>t\<guillemotright>. \<phi> \<tau> \<dagger> G) \<longrightarrow> \<phi> t \<dagger> Q))\<^sub>e"
  by (simp add: fbox_g_evol, simp add: expr_defs)

lemma fbox_g_evol_on:
  "vwb_lens a \<Longrightarrow> 
   fbox (g_evol_on a \<phi> G U) Q = (\<lambda>s. \<forall>t\<in>U (get\<^bsub>a\<^esub> s). (\<forall>\<tau>\<in>down (U (get\<^bsub>a\<^esub> s)) t. G (s \<oplus>\<^sub>L \<phi> \<tau> s on a)) \<longrightarrow> Q (s \<oplus>\<^sub>L \<phi> t s on a))"
  by (auto simp add: g_evol_on_alt_def fbox_def fun_eq_iff)

lemma fbox_g_evol_on'' [wp]:
  assumes "vwb_lens a"
  shows "fbox (g_evol_on a \<phi> G U) Q = (\<forall>t\<in>\<guillemotleft>U\<guillemotright> ($a). (\<forall> \<tau>\<in>down (\<guillemotleft>U\<guillemotright> ($a)) \<guillemotleft>t\<guillemotright> . G\<lbrakk>\<langle>\<phi> \<tau>\<rangle>\<^sub>s a/a\<rbrakk>) \<longrightarrow> Q\<lbrakk>\<langle>\<phi> t\<rangle>\<^sub>s a/a\<rbrakk>)\<^sub>e"
  by (simp add: fbox_g_evol_on assms, expr_auto)

text \<open> Verification by providing solutions \<close>

abbreviation g_ode_frame :: "('c::banach \<Longrightarrow> 'a) \<Rightarrow> 'a subst \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> real set) \<Rightarrow> 'c set \<Rightarrow> real \<Rightarrow> 'a \<Rightarrow> 'a set" 
  where "g_ode_frame a \<sigma> G U S t\<^sub>0 \<equiv> g_orbital_on a (\<lambda> t. \<sigma>) G U S t\<^sub>0"

abbreviation g_ode_on :: "('c::banach \<Longrightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> real set) \<Rightarrow> 'c set \<Rightarrow> real \<Rightarrow> 'a \<Rightarrow> 'a set"
  where "g_ode_on a f G U S t\<^sub>0 \<equiv> g_ode_frame a (subst_upd [\<leadsto>] a f) G U S t\<^sub>0"

abbreviation g_dl_ode_frame :: "('c::banach \<Longrightarrow> 'a) \<Rightarrow> 'a subst \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a set"
  where "g_dl_ode_frame a \<sigma> G \<equiv> g_ode_frame a \<sigma> G ({t. 0 \<le> t})\<^sub>e UNIV 0"

abbreviation g_dl_ode_on :: "('c::banach \<Longrightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a set"
  where "g_dl_ode_on a f G \<equiv> g_ode_on a f G ({t. 0 \<le> t})\<^sub>e UNIV 0"

no_notation (ASCII)
  disj  (infixr "|" 30)

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

term "{x` = 1, y` = $x | True}"

term "{(x, y)` = (1, 2*$x)}"
term "(x, y):{x` = 1, y` = 2*$x}"
term "(x,y):{(x, y)` = (1, 2*$x), z` = $y}"

lemma fbox_g_ode_on: "|{x` = f | G on U S @ t\<^sub>0}] Q = 
  (\<lambda>s. \<forall>X \<in> Sols (\<lambda>t c. get\<^bsub>x\<^esub> ([x \<leadsto> f] (put\<^bsub>x\<^esub> s c))) (U)\<^sub>e S t\<^sub>0 (get\<^bsub>x\<^esub> s). 
  \<forall>t\<in>U (get\<^bsub>x\<^esub> s). (\<forall>\<tau>\<in>down (U (get\<^bsub>x\<^esub> s)) t. G (put\<^bsub>x\<^esub> s (X \<tau>))) \<longrightarrow> Q (put\<^bsub>x\<^esub> s (X t)))"
  unfolding fbox_def g_orbital_on_eq by (auto simp: fun_eq_iff SEXP_def)

notation g_orbital ("(1x\<acute>=_ & _ on _ _ @ _)")

lemma fbox_g_orbital: "|x\<acute>=f & G on U S @ t\<^sub>0] Q = 
  (\<lambda>s. \<forall>X\<in>Sols f U S t\<^sub>0 s. \<forall>t\<in>U s. (\<forall>\<tau>\<in>down (U s) t. G (X \<tau>)) \<longrightarrow> Q (X t))"
  unfolding fbox_def g_orbital_eq by (auto simp: fun_eq_iff)

lemma fbox_g_orbital_on: "|g_orbital_on a f G U S t\<^sub>0] Q =
  (\<lambda>s. \<forall>X\<in>Sols (loc_subst a f s) U S t\<^sub>0 (get\<^bsub>a\<^esub> s).
        \<forall>t\<in>U (get\<^bsub>a\<^esub> s). (\<forall>x. x \<in> U (get\<^bsub>a\<^esub> s) \<and> x \<le> t \<longrightarrow> G (put\<^bsub>a\<^esub> s (X x))) \<longrightarrow> Q (put\<^bsub>a\<^esub> s (X t)))"
  by (auto simp add: g_orbital_on_def fbox_def g_orbital_eq fun_eq_iff)

lemma fbox_g_ode_on_subset:
  assumes "\<And> s. local_flow (\<lambda>c. get\<^bsub>a\<^esub> (\<sigma> (put\<^bsub>a\<^esub> s c))) T UNIV (loc_subst a \<phi> s)" "vwb_lens a"
    "{t. 0 \<le> t} \<subseteq> T"
  shows "|g_dl_ode_frame a \<sigma> G] Q = (\<lambda> s. (\<forall>t\<ge>0. (\<forall>\<tau>\<in>{0..t}. G (s \<oplus>\<^sub>L \<phi> \<tau> s on a)) \<longrightarrow> Q (s \<oplus>\<^sub>L \<phi> t s on a)))"
proof (unfold fbox_g_orbital_on fun_eq_iff, simp add: expr_defs, clarify)
  fix s
  let ?sol = "(\<lambda>t. get\<^bsub>a\<^esub> (\<phi> t s))"
  interpret local_flow "(\<lambda>c. get\<^bsub>a\<^esub> (\<sigma> (put\<^bsub>a\<^esub> s c)))" T "UNIV" _ "(loc_subst a \<phi> s)"
    by (simp add: assms)
  have sol: "?sol \<in> Sols (\<lambda>t c. get\<^bsub>a\<^esub> (\<sigma> (put\<^bsub>a\<^esub> s c))) (\<lambda>\<s>. Collect ((\<le>) 0)) UNIV 0 (get\<^bsub>a\<^esub> s)"
    using in_ivp_sols[of "(get\<^bsub>a\<^esub> s)" "(\<lambda>\<s>. Collect ((\<le>) 0))"] assms(2,3)
    by auto
  show "(\<forall>X\<in>Sols (\<lambda>t c. get\<^bsub>a\<^esub> (\<sigma> (put\<^bsub>a\<^esub> s c))) (\<lambda>\<s>. Collect ((\<le>) 0)) UNIV 0 (get\<^bsub>a\<^esub> s).
             \<forall>t\<ge>0. (\<forall>xa. 0 \<le> xa \<and> xa \<le> t \<longrightarrow> G (put\<^bsub>a\<^esub> s (X xa))) \<longrightarrow> Q (put\<^bsub>a\<^esub> s (X t))) =
         (\<forall>t\<ge>0. (\<forall>\<tau>\<in>{0..t}. G (s \<oplus>\<^sub>L \<phi> \<tau> s on a)) \<longrightarrow> Q (s \<oplus>\<^sub>L \<phi> t s on a))" (is "?lhs = ?rhs")
  proof 
    show "?lhs \<Longrightarrow> ?rhs"
      by (drule_tac x="?sol" in bspec, simp_all add: sol lens_override_def)
    show "?rhs \<Longrightarrow> ?lhs"
    proof clarify
      fix X and t :: real
      assume 
        a: "\<forall>t\<ge>0. (\<forall>\<tau>\<in>{0..t}. G (s \<oplus>\<^sub>L \<phi> \<tau> s on a)) \<longrightarrow> Q (s \<oplus>\<^sub>L \<phi> t s on a)"
        "X \<in> Sols (\<lambda>t c. get\<^bsub>a\<^esub> (\<sigma> (put\<^bsub>a\<^esub> s c))) (\<lambda>\<s>. Collect ((\<le>) 0)) UNIV 0 (get\<^bsub>a\<^esub> s)" "0 \<le> t"
      hence "\<forall>\<tau>\<in>{0..t}. X \<tau> = (loc_subst a \<phi> s) \<tau> (get\<^bsub>a\<^esub> s)"
      proof (safe)
        fix \<tau>
        assume \<tau>: "\<tau> \<in> {0..t}"
        thus "X \<tau> = (loc_subst a \<phi> s) \<tau> (get\<^bsub>a\<^esub> s)"
        using a assms(2, 3) ivp_unique_solution[of "(get\<^bsub>a\<^esub> s)" "\<lambda> _. Collect ((\<le>) 0)" \<tau> X "?sol"]
        by (auto simp add: sol)
      qed
  
      thus "\<forall>xa. 0 \<le> xa \<and> xa \<le> t \<longrightarrow> G (put\<^bsub>a\<^esub> s (X xa)) \<Longrightarrow> Q (put\<^bsub>a\<^esub> s (X t))"
        by (metis a(1) a(3) assms(2) atLeastAtMost_iff lens_override_def order_refl vwb_lens.put_eq)
    qed
  qed
qed

lemma fbox_g_ode_on_subset':
  assumes "\<And> s. local_flow (\<lambda>c. get\<^bsub>a\<^esub> (\<sigma> (put\<^bsub>a\<^esub> s c))) T UNIV (loc_subst a \<phi> s)" "vwb_lens a" "{t. 0 \<le> t} \<subseteq> T"
  shows "|g_dl_ode_frame a \<sigma> G] Q = |g_evol_on a \<phi> G ({0..})\<^sub>e] Q"
  using assms
  apply (simp add: g_evol_on_def fbox_g_evol)
  apply (subst fbox_g_ode_on_subset[OF assms(1)], simp_all add:assms expr_defs fun_eq_iff)
  apply (auto simp add: fbox_def g_evol_def g_orbit_eq assms image_Collect lens_defs)
  apply (metis atLeastAtMost_iff)
  done

text \<open> A postcondition of a localised ODE is a postcondition of its unique localised solution. \<close>

definition local_flow_on :: "('s \<Rightarrow> 's) \<Rightarrow> ('c::{heine_borel, banach} \<Longrightarrow> 's) \<Rightarrow> real set \<Rightarrow> 'c set \<Rightarrow> (real \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> bool" where
"local_flow_on f A T S \<phi> = (\<forall> s. local_flow (\<lambda>c. get\<^bsub>A\<^esub> (f (put\<^bsub>A\<^esub> s c))) T S (loc_subst A \<phi> s))"

definition local_lipschitz_on :: "('c::metric_space \<Longrightarrow> 's) \<Rightarrow> 'a::metric_space set \<Rightarrow> 'c set \<Rightarrow> ('s \<Rightarrow> 's) \<Rightarrow> bool" where
"local_lipschitz_on A T S \<phi> = (\<forall> s. local_lipschitz T S (\<lambda>t c. get\<^bsub>A\<^esub> (\<phi> (put\<^bsub>A\<^esub> s c))))"

lemma fbox_g_ode_on_subset'':
  assumes "local_flow_on \<sigma> a UNIV UNIV \<phi>" "vwb_lens a"
  shows "|g_dl_ode_frame a \<sigma> G] Q = |g_evol_on a \<phi> G ({0..})\<^sub>e] Q"
  using assms unfolding local_flow_on_def
  by (rule_tac fbox_g_ode_on_subset', auto)

context local_flow
begin

lemma fbox_g_ode_subset:
  assumes "\<And>s. s \<in> S \<Longrightarrow> 0 \<in> U s \<and> is_interval (U s) \<and> U s \<subseteq> T"
  shows "|x\<acute>= (\<lambda>t. f) & G on U S @ 0] Q = 
  (\<lambda> s. s \<in> S \<longrightarrow> (\<forall>t\<in>(U s). (\<forall>\<tau>\<in>down (U s) t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s)))"
  apply(unfold fbox_g_orbital fun_eq_iff)
  apply(clarify, rule iffI; clarify)
   apply(force simp: in_ivp_sols assms)
  apply(frule ivp_solsD(2), frule ivp_solsD(3), frule ivp_solsD(4))
  apply(subgoal_tac "\<forall>\<tau>\<in>down (U x) t. X \<tau> = \<phi> \<tau> x")
   apply(clarsimp, fastforce, rule ballI)
  apply(rule ivp_unique_solution[OF _ _ _ _ _ in_ivp_sols])
  using assms by auto

lemma 
  assumes "s \<in> S" and "0 \<in> U (get\<^bsub>x\<^esub> s)" and "U (get\<^bsub>x\<^esub> s) \<subseteq> T"
  shows "(\<lambda>t. put\<^bsub>x\<^esub> s (\<phi> \<tau> s)) \<in> Sols (\<lambda>t c. get\<^bsub>x\<^esub> ([x \<leadsto> f] (put\<^bsub>x\<^esub> s c))) (\<lambda>s. U (get\<^bsub>x\<^esub> s)) S 0 s"
  apply (rule in_ivp_sols_subset[OF _ _ ivp_solsI, of _ _ _ "\<lambda>s. T"])
  using  ivp(2)[OF \<open>s \<in> S\<close>] has_vderiv_on_domain[OF \<open>s \<in> S\<close>] 
    in_domain[OF \<open>s \<in> S\<close>] 
  oops

lemma fbox_g_ode_on_subset:
  assumes "\<And>s. s \<in> S \<Longrightarrow> 0 \<in> U (get\<^bsub>x\<^esub> s) \<and> is_interval (U (get\<^bsub>x\<^esub> s)) \<and> U (get\<^bsub>x\<^esub> s) \<subseteq> T"
  shows "|g_ode_on x f G U S 0] Q = (\<lambda>s. s \<in> S \<longrightarrow> (\<forall>t\<in>(U (get\<^bsub>x\<^esub> s)). 
  (\<forall>\<tau>\<in>down (U (get\<^bsub>x\<^esub> s)) t. G (put\<^bsub>x\<^esub> s (\<phi> \<tau> s)))) \<longrightarrow> Q (put\<^bsub>x\<^esub> s (\<phi> \<tau> s)))"
  apply(unfold fbox_g_ode_on fun_eq_iff)
  apply(clarify, rule iffI)
   apply(clarsimp simp: in_ivp_sols assms)
  oops
                         
lemma fbox_g_ode: "|x\<acute>=(\<lambda>t. f) & G on (\<lambda>s. T) S @ 0] Q = 
  (\<lambda>s. s \<in> S \<longrightarrow> (\<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s)))"
  by (subst fbox_g_ode_subset, simp_all add: init_time interval_time)

lemma fbox_g_ode_ivl: "t \<ge> 0 \<Longrightarrow> t \<in> T \<Longrightarrow> |x\<acute>=(\<lambda>t. f) & G on (\<lambda>s. {0..t}) S @ 0] Q = 
  (\<lambda>s. s \<in> S \<longrightarrow> (\<forall>t\<in>{0..t}. (\<forall>\<tau>\<in>{0..t}. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s)))"
  apply(subst fbox_g_ode_subset, simp_all add: subintervalI init_time real_Icc_closed_segment)
  by (auto simp: closed_segment_eq_real_ivl)

lemma fbox_orbit: "|\<gamma>\<^sup>\<phi>] Q = (\<lambda>s. s \<in> S \<longrightarrow> (\<forall> t \<in> T. Q (\<phi> t s)))"
  unfolding orbit_def fbox_g_ode by simp

end

text \<open> Verification with differential invariants \<close>

definition g_ode_inv :: "(real \<Rightarrow> ('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> ('a \<Rightarrow> real set) \<Rightarrow> 'a set \<Rightarrow> 
  real \<Rightarrow> 'a pred \<Rightarrow> ('a \<Rightarrow> 'a set)" ("(1x\<acute>=_ & _ on _ _ @ _ DINV _ )") 
  where "(x\<acute>= f & G on U S @ t\<^sub>0 DINV I) = (x\<acute>= f & G on U S @ t\<^sub>0)"

lemma fbox_g_orbital_guard: 
  assumes "H = (\<lambda>s. G s \<and> Q s)"
  shows "|x\<acute>=f & G on U S @ t\<^sub>0] Q = |x\<acute>=f & G on U S @ t\<^sub>0] H "
  unfolding fbox_g_orbital using assms by auto

lemma fbox_g_orbital_inv:
  assumes "P \<le> I" and "I \<le> |x\<acute>=f & G on U S @ t\<^sub>0] I" and "I \<le> Q"
  shows "P \<le> |x\<acute>=f & G on U S @ t\<^sub>0] Q"
  using assms(1) 
  apply(rule order.trans)
  using assms(2) 
  apply(rule order.trans)
  by (rule fbox_iso[OF assms(3)])

lemma fbox_diff_inv: 
  "(I \<le> |x\<acute>=f & G on U S @ t\<^sub>0] I) = diff_invariant I f U S t\<^sub>0 G"
  by (auto simp: diff_invariant_def ivp_sols_def fbox_def g_orbital_eq)

lemma hoare_diff_inv[simp]:
  "\<^bold>{I\<^bold>} (x\<acute>=f & G on U S @ t\<^sub>0) \<^bold>{I\<^bold>} = diff_invariant (I)\<^sub>e f (U)\<^sub>e S t\<^sub>0 (G)\<^sub>e"
  using fbox_diff_inv[of I f G U S t\<^sub>0] by (simp add: SEXP_def)

lemma fbox_diff_inv_on: 
  "(I \<le> |{a` = f | G on U S @ t\<^sub>0}] I) = diff_invariant_on I a (\<lambda> _. [a \<leadsto> f]) (U)\<^sub>e S t\<^sub>0 (G)\<^sub>e"
  by (auto simp: diff_invariant_on_def ivp_sols_def fbox_def g_orbital_on_eq SEXP_def)

lemma hoare_diff_inv_on:
  "\<^bold>{I\<^bold>} {a` = f | G on U S @ t\<^sub>0} \<^bold>{I\<^bold>} = diff_invariant_on (I)\<^sub>e a (\<lambda>_. [a \<leadsto> f]) (U)\<^sub>e S t\<^sub>0 (G)\<^sub>e"
  using fbox_diff_inv_on[of I a f G U S t\<^sub>0] by (simp add: SEXP_def)

lemma fbox_diff_inv_on2:
  "I \<le> fbox (g_orbital_on a f G U S t\<^sub>0) I = diff_invariant_on I a f U S t\<^sub>0 G"
  by (auto simp: diff_invariant_on_def ivp_sols_def fbox_def g_orbital_on_eq)

lemma diff_inv_guard_ignore:
  assumes "I \<le> |x\<acute>= f & (\<lambda>s. True) on U S @ t\<^sub>0] I"
  shows "I \<le> |x\<acute>= f & G on U S @ t\<^sub>0] I"
  using assms unfolding fbox_diff_inv diff_invariant_eq image_le_pred by auto

context local_flow
begin

lemma fbox_diff_inv_eq: 
  assumes "\<And>s. s \<in> S \<Longrightarrow> 0 \<in> U s \<and> is_interval (U s) \<and> U s \<subseteq> T"
  shows "diff_invariant I (\<lambda>t. f) U S 0 (\<lambda>s. True) = 
  ((\<lambda>s. s \<in> S \<longrightarrow> I s) = |x\<acute>= (\<lambda>t. f) & (\<lambda>s. True) on U S @ 0] (\<guillemotleft>\<s>\<guillemotright> \<in> \<guillemotleft>S\<guillemotright> \<longrightarrow> I))"
  unfolding fbox_diff_inv[symmetric] 
  apply(subst fbox_g_ode_subset[OF assms], simp)+
  apply(clarsimp simp: le_fun_def fun_eq_iff, safe, force)
   apply(erule_tac x=0 in ballE)
  using init_time in_domain ivp(2) assms apply(force, force)
  apply(erule_tac x=x in allE, clarsimp, erule_tac x=t in ballE)
  using in_domain ivp(2) assms by force+

lemma diff_inv_eq_inv_set: 
  "diff_invariant I (\<lambda>t. f) (\<lambda>s. T) S 0 (\<lambda>s. True) = (\<forall>s. I s \<longrightarrow> \<gamma>\<^sup>\<phi> s \<subseteq> {s. I s})"
  unfolding diff_inv_eq_inv_set orbit_def by simp

end

lemma fbox_g_odei: "P \<le> I \<Longrightarrow> I \<le> |x\<acute>= f & G on U S @ t\<^sub>0] I \<Longrightarrow> (\<lambda>s. I s \<and> G s) \<le> Q \<Longrightarrow> 
  P \<le> |x\<acute>= f & G on U S @ t\<^sub>0 DINV I] Q"
  unfolding g_ode_inv_def 
  apply(rule_tac b="|x\<acute>= f & G on U S @ t\<^sub>0] I" in order.trans)
   apply(rule_tac I="I" in fbox_g_orbital_inv, simp_all)
  apply(subst fbox_g_orbital_guard, simp)
  by (rule fbox_iso, force)

lemma hoare_g_odei: " \<^bold>{I\<^bold>} (x\<acute>= f & G on U S @ t\<^sub>0) \<^bold>{I\<^bold>}  \<Longrightarrow> `P \<longrightarrow> I` \<Longrightarrow> `I \<and> G \<longrightarrow> Q` \<Longrightarrow> 
 \<^bold>{P\<^bold>} (x\<acute>= f & G on U S @ t\<^sub>0 DINV I) \<^bold>{Q\<^bold>}"
  by (rule fbox_g_odei, simp_all add: SEXP_def taut_def le_fun_def)


subsection \<open> Derivation of the rules of dL \<close>

text \<open> We derive domain specific rules of differential dynamic logic (dL). First we present a 
generalised version, then we show the rules as instances of the general ones.\<close>

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
      and  x_ivp: "X \<in> Sols (\<lambda>t c. get\<^bsub>x\<^esub> ([x \<leadsto> f] (put\<^bsub>x\<^esub> s c))) (U)\<^sub>e S t\<^sub>0 (get\<^bsub>x\<^esub> s)"  
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
    and x_ivp:"X \<in> Sols (\<lambda>t c. get\<^bsub>a\<^esub> (f t (put\<^bsub>a\<^esub> s c))) (U)\<^sub>e S t\<^sub>0 (get\<^bsub>a\<^esub> s)" 
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
  assumes "\<^bold>{P\<^bold>} g_orbital_on a f (B)\<^sub>e (U)\<^sub>e S t\<^sub>0 \<^bold>{P\<^bold>}" "\<^bold>{Q\<^bold>} g_orbital_on a f (B \<and> P)\<^sub>e (U)\<^sub>e S t\<^sub>0\<^bold>{Q\<^bold>}"
  shows "\<^bold>{P \<and> Q\<^bold>} g_orbital_on a f (B)\<^sub>e (U)\<^sub>e S t\<^sub>0 \<^bold>{P \<and> Q\<^bold>}"
  apply (rule diff_cut_on_rule[where C="P"])
  using assms(1) hoare_weaken_pre(1) apply blast
  apply (rule hoare_conj)
   apply (rule hoare_weaken_pre)
   apply (rule diff_weak_on_rule)
  apply (simp)
  using assms(2) hoare_weaken_pre(2) by blast

lemma diff_cut_on_split':
  assumes "\<^bold>{P\<^bold>} g_orbital_on a f (B)\<^sub>e (U)\<^sub>e S t\<^sub>0 \<^bold>{P\<^bold>}" "\<^bold>{Q\<^bold>} g_orbital_on a f (B \<and> P)\<^sub>e (U)\<^sub>e S t\<^sub>0 \<^bold>{Q\<^bold>}"
  shows "\<^bold>{P \<and> Q\<^bold>} g_orbital_on a f (B)\<^sub>e (U)\<^sub>e S t\<^sub>0 \<^bold>{Q\<^bold>}"
  by (metis (mono_tags) SEXP_def assms(1) assms(2) diff_cut_on_rule hoare_weaken_pre(1) hoare_weaken_pre(2))

lemma diff_inv_axiom1:
  assumes "G s \<longrightarrow> I s" and "diff_invariant I (\<lambda>t. f) (\<lambda>s. {t. t \<ge> 0}) UNIV 0 G"
  shows "( |x\<acute>= f & G] I) s"
  using assms unfolding fbox_g_orbital diff_invariant_eq apply clarsimp
  by (erule_tac x=s in allE, frule ivp_solsD(2), clarsimp)

lemma diff_inv_axiom2:
  assumes "picard_lindeloef (\<lambda>t. f) UNIV UNIV 0"
    and "\<And>s. {t::real. t \<ge> 0} \<subseteq> picard_lindeloef.ex_ivl (\<lambda>t. f) UNIV UNIV 0 s"
    and "diff_invariant I (\<lambda>t. f) (\<lambda>s. {t::real. t \<ge> 0}) UNIV 0 G"
  shows "|x\<acute>= f & G] I = |(\<lambda>s. {x. s = x \<and> G s})] I"
proof(unfold fbox_g_orbital, subst fbox_def, clarsimp simp: fun_eq_iff)
  fix s
  let "?ex_ivl s" = "picard_lindeloef.ex_ivl (\<lambda>t. f) UNIV UNIV 0 s"
  let "?lhs s" = 
    "\<forall>X\<in>Sols (\<lambda>t. f) (\<lambda>s. {t. t \<ge> 0}) UNIV 0 s. \<forall>t\<ge>0. (\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> G (X \<tau>)) \<longrightarrow> I (X t)"
  obtain X where xivp1: "X \<in> Sols (\<lambda>t. f) (\<lambda>s. ?ex_ivl s) UNIV 0 s"
    using picard_lindeloef.flow_in_ivp_sols_ex_ivl[OF assms(1)] by auto
  have xivp2: "X \<in> Sols (\<lambda>t. f) (\<lambda>s. Collect ((\<le>) 0)) UNIV 0 s"
    by (rule in_ivp_sols_subset[OF _ _ xivp1], simp_all add: assms(2))
  hence shyp: "X 0 = s"
    using ivp_solsD by auto
  have dinv: "\<forall>s. I s \<longrightarrow> ?lhs s"
    using assms(3) unfolding diff_invariant_eq by auto
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
  assumes "P \<le> I" and "diff_invariant I f U S t\<^sub>0 G" and "I \<le> Q"
  shows "P \<le> |x\<acute>= f & G on U S @ t\<^sub>0] Q"
  apply(rule fbox_g_orbital_inv[OF assms(1) _ assms(3)])
  unfolding fbox_diff_inv using assms(2) .

lemma diff_inv_on_rule:
  assumes "`P \<longrightarrow> I`" and "diff_invariant_on (I)\<^sub>e a (\<lambda> _. [a \<leadsto> f]) (U)\<^sub>e S t\<^sub>0 (G)\<^sub>e" and "`I \<longrightarrow> Q`"
  shows "\<^bold>{P\<^bold>} {a` = f | G on U S @ t\<^sub>0} \<^bold>{Q\<^bold>}"
  using assms unfolding fbox_diff_inv_on[THEN sym] refine_iff_implies[THEN sym]
  by (metis (mono_tags, lifting) SEXP_def fbox_iso order.trans)

lemma diff_ghost_rule:
  assumes "vwb_lens y" "y \<bowtie> a" "y \<sharp>\<^sub>s \<sigma>" "$y \<sharp> B" 
    "\<^bold>{G\<^bold>} g_dl_ode_frame (a +\<^sub>L y) (\<sigma>(y \<leadsto> \<eta>)) B \<^bold>{G\<^bold>}"
  shows "\<^bold>{G \\ $y\<^bold>} g_dl_ode_frame a \<sigma> B \<^bold>{G \\ $y\<^bold>}"
  oops

lemma diff_ghost_rule_very_simple:
  fixes y :: "real \<Longrightarrow> _"
  assumes "vwb_lens y" "y \<bowtie> a" "y \<sharp>\<^sub>s \<sigma>" "$y \<sharp> B" "(F)\<^sub>e = G \\ $y"
    "\<^bold>{G\<^bold>} g_dl_ode_frame (a +\<^sub>L y) (\<sigma>(y \<leadsto> \<guillemotleft>k\<guillemotright> *\<^sub>R $y)) B \<^bold>{G\<^bold>}"
  shows "\<^bold>{F\<^bold>} g_dl_ode_frame a \<sigma> B \<^bold>{F\<^bold>}"
  using assms
  by (metis SEXP_def diff_ghost_very_simple fbox_diff_inv_on2) 

no_notation Union ("\<mu>")

subsection \<open> Proof Methods \<close>

text \<open> A simple tactic for Hoare logic that uses weakest liberal precondition calculations \<close>

method hoare_wp_simp uses local_flow = ((rule_tac hoare_loopI)?; simp add: unrest_ssubst var_alpha_combine wp usubst usubst_eval refine_iff_implies fbox_g_ode_on_subset''[OF local_flow])
method hoare_wp_auto uses local_flow = (hoare_wp_simp local_flow: local_flow; expr_auto)

method vderiv = ((expr_simp)?; force intro!: poly_derivatives simp: vec_eq_iff field_simps)

method lipschitz for L :: real = 
  (unfold local_lipschitz_on_def local_lipschitz_def lipschitz_on_def dist_norm, clarify, rule exI[where x="L"], expr_auto, (rule exI[where x="L"], auto)?)

method local_flow for L :: real =
  ((auto simp add: local_flow_on_def)?, (unfold_locales, auto), (lipschitz L, vderiv, expr_auto))

method local_flow_auto =
  (local_flow "1/4" | local_flow "1/2" | local_flow "1" | local_flow "2")

method dDiscr = (rule_tac nmods_invariant[OF nmods_g_orbital_on_discrete']; unrest)

method dGhost for y :: "real \<Longrightarrow> 's" and G :: "'s \<Rightarrow> bool" and k :: real 
  = (rule diff_ghost_rule_very_simple[where y="y" and G="G" and k="k"]
    ,simp_all add: unrest usubst usubst_eval unrest_ssubst liberate_as_subst)

end