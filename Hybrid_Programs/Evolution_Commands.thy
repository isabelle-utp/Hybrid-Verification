(*  Title: HS verification with lenses *)

section \<open> HS verification with lenses \<close>

text \<open> We use shallow expressions to rephrase hybrid systems properties. Each operator below 
includes lemmas for verification condition generation. \<close>

theory Evolution_Commands
  imports 
    Correctness_Specs
    "Framed_ODEs.Framed_ODEs"
begin


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
  put\<^bsub>a\<^esub> s ` (g_evol (\<phi>\<down>\<^sub>V\<^sub>e\<^sub>c\<^bsub>a\<^esub> s) (\<lambda> v. G (put\<^bsub>a\<^esub> s v)) U (get\<^bsub>a\<^esub> s))"

lemma g_evol_on_eq:
  "vwb_lens a \<Longrightarrow> g_evol_on a \<phi> G U s 
    = {(s \<triangleleft>\<^bsub>a\<^esub> \<phi> t s) |t. t \<in> U (get\<^bsub>a\<^esub> s) \<and> (\<forall>\<tau>. \<tau> \<in> down (U (get\<^bsub>a\<^esub> s)) t \<longrightarrow> G (s \<triangleleft>\<^bsub>a\<^esub> \<phi> \<tau> s))}"
  by (auto simp add: g_evol_on_def g_evol_def g_orbit_eq lens_defs tsubst2vecf_eq)

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

lemma fbox_g_evol_on [wlp]:
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

lemma fbox_g_orbital_on: "|g_orbital_on x f G U S t\<^sub>0] Q =
  (\<lambda>s. \<forall>X\<in>Sols U S (f\<down>\<^sub>V\<^sub>e\<^sub>c\<^bsub>x\<^esub> s) t\<^sub>0 (get\<^bsub>x\<^esub> s).
        \<forall>t\<in>U (get\<^bsub>x\<^esub> s). (\<forall>\<tau>. \<tau> \<in> U (get\<^bsub>x\<^esub> s) \<and> \<tau> \<le> t \<longrightarrow> G (put\<^bsub>x\<^esub> s (X \<tau>))) \<longrightarrow> Q (put\<^bsub>x\<^esub> s (X t)))"
  by (auto simp add: g_orbital_on_eq fbox_def g_orbital_eq fun_eq_iff)

lemma fdia_g_orbital_on: "|g_orbital_on x f G U S t\<^sub>0\<rangle> Q =
  (\<lambda>s. \<exists>X\<in>Sols U S (f\<down>\<^sub>V\<^sub>e\<^sub>c\<^bsub>x\<^esub> s) t\<^sub>0 (get\<^bsub>x\<^esub> s).
        \<exists>t\<in>U (get\<^bsub>x\<^esub> s). (\<forall>\<tau>. \<tau> \<in> U (get\<^bsub>x\<^esub> s) \<and> \<tau> \<le> t \<longrightarrow> G (put\<^bsub>x\<^esub> s (X \<tau>))) \<and> Q (put\<^bsub>x\<^esub> s (X t)))"
  by (auto simp: fdia_def g_orbital_on_eq g_orbital_eq fun_eq_iff)

lemma fbox_orbitals_prelim: "|g_orbital_on x f G U S t\<^sub>0] Q =
  (\<lambda>s. (fbox (g_orbital (f\<down>\<^sub>V\<^sub>e\<^sub>c\<^bsub>x\<^esub> s) (G\<down>\<^sub>F\<^bsub>x\<^esub> s) U S t\<^sub>0) (Q\<down>\<^sub>F\<^bsub>x\<^esub> s)) (get\<^bsub>x\<^esub> s))"
  unfolding fbox_g_orbital[unfolded clarify_fbox] fbox_g_orbital_on fun_eq_iff
  by (clarsimp simp: expr_defs)

lemma fdia_orbitals_prelim: "|g_orbital_on x f G U S t\<^sub>0\<rangle> Q =
  (\<lambda>s. (fdia (g_orbital (f\<down>\<^sub>V\<^sub>e\<^sub>c\<^bsub>x\<^esub> s) (G\<down>\<^sub>F\<^bsub>x\<^esub> s) U S t\<^sub>0) (Q\<down>\<^sub>F\<^bsub>x\<^esub> s)) (get\<^bsub>x\<^esub> s))"
  by (expr_auto add: fdia_def g_orbital_on_eq g_orbital_eq)

lemmas fbox_g_orbital_on_orbital = fbox_orbitals_prelim[
    unfolded clarify_fbox[of 
      "g_orbital (tsubst2vecf _ _ _) (_ \<down>\<^sub>F\<^bsub>_\<^esub> _) _ _ _"
      "(_ \<down>\<^sub>F\<^bsub>_\<^esub> _)", 
      symmetric
      ]
    ]

lemmas fdia_g_orbital_on_orbital = fdia_orbitals_prelim[
    unfolded clarify_fdia[of 
      "g_orbital (tsubst2vecf _ _ _) (_ \<down>\<^sub>F\<^bsub>_\<^esub> _) _ _ _"
      "(_ \<down>\<^sub>F\<^bsub>_\<^esub> _)", 
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
  = g_ode_frame (x +\<^sub>L y) [x \<leadsto> \<guillemotleft>f\<guillemotright> ($x), y \<leadsto> g] (G)\<^sub>e (U)\<^sub>e S t\<^sub>0 "
    and "g_ode_frame (x +\<^sub>L y) [x \<leadsto> \<guillemotleft>f\<guillemotright> ($x), y \<leadsto> g] (G)\<^sub>e (U)\<^sub>e S t\<^sub>0 
  = g_orbital_on (x +\<^sub>L y) (\<lambda>t s. put\<^bsub>y\<^esub> (put\<^bsub>x\<^esub> s (f (get\<^bsub>x\<^esub> s))) (g s)) G U S t\<^sub>0"
    and "((x,y):{x` = f(y \<leadsto> h) | G on U S @ t\<^sub>0})
  = g_ode_frame (x +\<^sub>L y) [x \<leadsto> f(y \<leadsto> h)] (G)\<^sub>e (U)\<^sub>e S t\<^sub>0"
    and "g_ode_frame (x +\<^sub>L y) [x \<leadsto> f(y \<leadsto> h)] (G)\<^sub>e (U)\<^sub>e S t\<^sub>0 
  = g_orbital_on (x +\<^sub>L y) (\<lambda>t s. put\<^bsub>x\<^esub> s (put\<^bsub>y\<^esub> (f s) (h s))) G U S t\<^sub>0"
   apply (rule_tac f="\<lambda>s. g_ode_frame (x +\<^sub>L y) s (G)\<^sub>e (U)\<^sub>e S t\<^sub>0" in arg_cong)
  prefer 3 apply (rule_tac f="\<lambda>s. g_ode_frame (x +\<^sub>L y) s (G)\<^sub>e (U)\<^sub>e S t\<^sub>0" in arg_cong)
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
  where "local_flow_on f x T S \<phi> = (\<forall>s. local_flow (lframe_subst x f s) T S (\<lambda>t. (\<phi>\<down>\<^sub>V\<^sub>e\<^sub>c\<^bsub>x\<^esub> s) t))"

lemma fbox_g_ode_frame_flow:
  fixes a::"'c::{heine_borel,banach} \<Longrightarrow> 's"
    and f::"'s \<Rightarrow> 's"
  assumes "local_flow_on f x T S \<phi>" and "vwb_lens x"
    and "\<And>s. s \<in> S \<Longrightarrow> 0 \<in> U s \<and> is_interval (U s) \<and> U s \<subseteq> T"
  shows "|g_ode_frame x f G U S 0] Q = (\<lambda>s. get\<^bsub>x\<^esub> s \<in> S 
    \<longrightarrow> (\<forall>t\<in>U (get\<^bsub>x\<^esub> s). (\<forall>\<tau>\<in>down (U (get\<^bsub>x\<^esub> s)) t. G (s \<triangleleft>\<^bsub>x\<^esub> \<phi> \<tau> s)) \<longrightarrow> Q (s \<triangleleft>\<^bsub>x\<^esub> \<phi> t s)))"
  apply (subst fbox_g_orbital_on_orbital)
  apply (subst local_flow.fbox_g_ode_subset[OF assms(1)[unfolded local_flow_on_def, rule_format]])
  using assms by expr_auto+

lemmas fbox_solve = fbox_g_ode_frame_flow[where T=UNIV, simplified]

lemma fdia_g_ode_frame_flow:
  fixes a::"'c::{heine_borel,banach} \<Longrightarrow> 's"
    and f::"'s \<Rightarrow> 's"
  assumes "local_flow_on f x T UNIV \<phi>" and "vwb_lens x"
    and "\<And>s. 0 \<in> U s \<and> is_interval (U s) \<and> U s \<subseteq> T"
  shows "|g_ode_frame x f G U UNIV 0\<rangle> Q = 
  (\<lambda>s. (\<exists>t\<in>U (get\<^bsub>x\<^esub> s). (\<forall>\<tau>\<in>down (U (get\<^bsub>x\<^esub> s)) t. G (s \<triangleleft>\<^bsub>x\<^esub> \<phi> \<tau> s)) \<and> Q (s \<triangleleft>\<^bsub>x\<^esub> \<phi> t s)))"
  apply (subst fdia_g_orbital_on_orbital, rule ext)
  apply (subst local_flow.fdia_g_ode_subset[OF assms(1)[unfolded local_flow_on_def, rule_format]])
  using assms by expr_auto+

lemma fbox_g_ode_on_flow: (* delete *)
  assumes "local_flow_on (subst_upd [\<leadsto>] A f) A T S \<phi>" 
    and "vwb_lens A"
    and "\<And>s. 0 \<in> U s \<and> is_interval (U s) \<and> U s \<subseteq> T"
  shows "|g_ode_on A f G U S 0] Q = (\<lambda>s. get\<^bsub>A\<^esub> s \<in> S 
    \<longrightarrow> (\<forall>t\<in>U (get\<^bsub>A\<^esub> s). (\<forall>\<tau>\<in>down (U (get\<^bsub>A\<^esub> s)) t. G (s \<triangleleft>\<^bsub>A\<^esub> \<phi> \<tau> s)) \<longrightarrow> Q (s \<triangleleft>\<^bsub>A\<^esub> \<phi> t s)))"
  by (subst fbox_g_ode_frame_flow[OF assms], simp)

lemma fbox_g_dl_ode_frame_flow: (* delete *)
  assumes "local_flow_on f A T UNIV \<phi>"
    and "vwb_lens A" and "{t. 0 \<le> t} \<subseteq> T"
  shows "|g_dl_ode_frame A f G] Q = (\<lambda>s. 
  (\<forall>t\<ge>0. (\<forall>\<tau>\<in>{0..t}. G (s \<oplus>\<^sub>L \<phi> \<tau> s on A)) \<longrightarrow> Q (s \<oplus>\<^sub>L \<phi> t s on A)))"
  apply (subst fbox_g_ode_frame_flow[OF assms(1,2)])
  using assms(2,3) by auto

lemma fbox_g_dl_ode_on_flow: (* delete *)
  assumes "local_flow_on (subst_upd [\<leadsto>] A f) A T UNIV \<phi>"
    and "vwb_lens A" and "{t. 0 \<le> t} \<subseteq> T"
  shows "|g_dl_ode_on A f G] Q = (\<lambda>s. 
  (\<forall>t\<ge>0. (\<forall>\<tau>\<in>{0..t}. G (s \<oplus>\<^sub>L \<phi> \<tau> s on A)) \<longrightarrow> Q (s \<oplus>\<^sub>L \<phi> t s on A)))"
  by (subst fbox_g_dl_ode_frame_flow[OF assms], simp)

lemma fbox_g_ode_frame_g_evol:
  assumes "local_flow_on f A T S \<phi>"
    and "vwb_lens A" 
    and "\<And>s. s \<in> S \<Longrightarrow> 0 \<in> U s \<and> is_interval (U s) \<and> U s \<subseteq> T"
  shows "|g_ode_frame A f G U S 0] Q = (\<lambda>s. get\<^bsub>A\<^esub> s \<in> S \<longrightarrow> ( |g_evol_on A \<phi> G U] Q) s)"
  by (subst fbox_g_ode_frame_flow[OF assms(1,2,3)], force)
    (subst fbox_g_evol_on[OF assms(2)], expr_auto)

lemma fbox_g_ode_on_g_evol: (* delete *)
  assumes "local_flow_on (subst_upd [\<leadsto>] A f) A T UNIV \<phi>" and "vwb_lens A"
    and "\<And>s. 0 \<in> U s \<and> is_interval (U s) \<and> U s \<subseteq> T"
  shows "|g_ode_on A f G U UNIV 0] Q = |g_evol_on A \<phi> G U] Q"
  using fbox_g_ode_frame_g_evol[OF assms(1,2,3), simplified]
  by force

lemma fbox_g_dl_ode_frame_g_evol: (* delete *)
  assumes "local_flow_on f A T UNIV \<phi>"
    and "vwb_lens A" and "{t. 0 \<le> t} \<subseteq> T"
  shows "|g_dl_ode_frame A f G] Q = |g_evol_on A \<phi> G ({0..})\<^sub>e] Q"
  using assms(3)
  by (subst fbox_g_ode_frame_g_evol[OF assms(1,2)])
    (auto simp: fbox_g_evol_on[OF assms(2)])

lemmas fbox_g_dL_easiest = fbox_g_dl_ode_frame_g_evol[of _ _ UNIV, simplified]


subsection \<open> Differential invariants \<close>


definition g_ode_inv :: "(real \<Rightarrow> 'a::real_normed_vector \<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> ('a \<Rightarrow> real set) \<Rightarrow> 'a set \<Rightarrow> 
  real \<Rightarrow> 'a pred \<Rightarrow> ('a \<Rightarrow> 'a set)" ("(1x\<acute>=_ & _ on _ _ @ _ DINV _ )") 
  where "(x\<acute>= f & G on U S @ t\<^sub>0 DINV I) = g_orbital f G U S t\<^sub>0"

lemma fbox_g_orbital_guard: 
  assumes "H = (\<lambda>s. G s \<and> Q s)"
  shows "|g_orbital f G U S t\<^sub>0] Q = |g_orbital f G U S t\<^sub>0] H "
  unfolding fbox_g_orbital using assms by auto

lemma fbox_g_orbital_on_guard: 
  assumes "H = (G \<and> Q)\<^sub>e"
  shows "|g_orbital_on a f G U S t\<^sub>0] Q = |g_orbital_on a f G U S t\<^sub>0] H "
  unfolding fbox_g_orbital_on
  using assms by auto

lemma fbox_diff_inv: 
  "(I \<le> |g_orbital f G U S t\<^sub>0] I) = diff_inv U S G f t\<^sub>0 I"
  by (auto simp: diff_inv_def ivp_sols_def fbox_def g_orbital_eq)

lemma hoare_diff_inv:
  "\<^bold>{I\<^bold>} (g_orbital f G U S t\<^sub>0) \<^bold>{I\<^bold>} = diff_inv (U)\<^sub>e S (G)\<^sub>e f t\<^sub>0 (I)\<^sub>e"
  using fbox_diff_inv[of I f G U S t\<^sub>0] by (simp add: SEXP_def)

lemma fbox_diff_inv_on:
  "I \<le> fbox (g_orbital_on a f G U S t\<^sub>0) I = diff_inv_on a f G U S t\<^sub>0 I"
  by (auto simp: diff_inv_on_def ivp_sols_def fbox_def g_orbital_on_eq SEXP_def)

lemma fbox_diff_inv_on':
  "(I \<le> |g_orbital_on a f G U S t\<^sub>0] I) = diff_inv_on a f G U S t\<^sub>0 I"
  by (simp add: fbox_diff_inv_on expr_defs)

lemma hoare_diff_inv_on:
  "\<^bold>{I\<^bold>} (g_orbital_on a f G U S t\<^sub>0) \<^bold>{I\<^bold>} = diff_inv_on a f G U S t\<^sub>0 I"
  using fbox_diff_inv_on[of I a f G U S]
  by (simp add: SEXP_def)

lemma hoare_diff_inv_on':
  "\<^bold>{I\<^bold>} (g_orbital_on a f G U S t\<^sub>0) \<^bold>{I\<^bold>} = diff_inv_on a f (G)\<^sub>e (U)\<^sub>e S t\<^sub>0 (I)\<^sub>e"
  using fbox_diff_inv_on[of I a f G U S]
  by (simp add: SEXP_def)

lemma diff_inv_guard_ignore:
  assumes "I \<le> |g_orbital f (True)\<^sub>e U S t\<^sub>0] I"
  shows "I \<le> |g_orbital f G U S t\<^sub>0] I"
  using assms 
  by (auto simp: fbox_diff_inv diff_inv_eq)

lemma diff_inv_on_guard_ignore:
  assumes "I \<le> |g_orbital_on a f (True)\<^sub>e U S t\<^sub>0] I"
  shows "I \<le> |g_orbital_on a f G U S t\<^sub>0] I"
  using assms 
  by (auto simp: fbox_diff_inv_on diff_inv_on_eq expr_defs)

context local_flow
begin

lemma fbox_diff_inv_eq: 
  assumes "\<And>s. s \<in> S \<Longrightarrow> 0 \<in> U s \<and> is_interval (U s) \<and> U s \<subseteq> T"
  shows "diff_inv U S (\<lambda>s. True) (\<lambda>t. f) 0 I = 
  ((\<lambda>s. s \<in> S \<longrightarrow> I s) = |g_orbital (\<lambda>t. f) (True)\<^sub>e U S 0] (\<guillemotleft>\<s>\<guillemotright> \<in> \<guillemotleft>S\<guillemotright> \<longrightarrow> I))"
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

lemma fbox_g_odei: "P \<le> I \<Longrightarrow> I \<le> |g_orbital f G U S t\<^sub>0] I \<Longrightarrow> (\<lambda>s. I s \<and> G s) \<le> Q \<Longrightarrow> 
  P \<le> |x\<acute>= f & G on U S @ t\<^sub>0 DINV I] Q"
  unfolding g_ode_inv_def 
  apply(rule_tac b="|g_orbital f G U S t\<^sub>0] I" in order.trans)
   apply(rule_tac I="I" in fbox_inv, simp_all)
  apply(subst fbox_g_orbital_guard, simp)
  by (rule fbox_iso, force)

lemma hoare_g_odei: " \<^bold>{I\<^bold>} (g_orbital f G U S t\<^sub>0) \<^bold>{I\<^bold>}  \<Longrightarrow> `P \<longrightarrow> I` \<Longrightarrow> `I \<and> G \<longrightarrow> Q` \<Longrightarrow> 
 \<^bold>{P\<^bold>} (x\<acute>= f & G on U S @ t\<^sub>0 DINV I) \<^bold>{Q\<^bold>}"
  by (rule fbox_g_odei, simp_all add: SEXP_def taut_def le_fun_def)

lemma fbox_diff_invI: "(I)\<^sub>e \<le> |g_orbital_on a f G U S t\<^sub>0] I \<Longrightarrow> P \<le> (I)\<^sub>e \<Longrightarrow> (I \<and> G)\<^sub>e \<le> Q
  \<Longrightarrow> P \<le> |g_orbital_on a f G U S t\<^sub>0] Q"
  apply(rule_tac b="|g_orbital_on a f G U S t\<^sub>0] I" in order.trans)
   apply (rule_tac I=I in fbox_inv; expr_simp)
  by (subst fbox_g_orbital_on_guard, force)
    (rule fbox_iso, force)

lemmas fbox_diff_inv_rawI = fbox_diff_invI[unfolded clarify_fbox expr_defs]

lemma hoare_diff_inv_on_post_inv: (* generalise and wrap in tactic *)
  assumes "`P \<longrightarrow> Q`" "\<^bold>{Q\<^bold>} {a` = f | G on U S @ t\<^sub>0} \<^bold>{Q\<^bold>}"
  shows "\<^bold>{P\<^bold>} {a` = f | G on U S @ t\<^sub>0} \<^bold>{Q\<^bold>}"
  using assms(2) by (rule hoare_conseq; simp add: assms)


end