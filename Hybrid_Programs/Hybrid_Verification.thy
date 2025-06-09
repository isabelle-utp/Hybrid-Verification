theory Hybrid_Verification
  imports
    Diff_Dyn_Logic
    Proof_Automation
    HS_CAS_Integration
begin

(* Extra lens laws -- move to Optics *)

lemma lens_plus_left_sublens [simp, lens]: 
  assumes "vwb_lens Y" "Y \<bowtie> Z" "X \<subseteq>\<^sub>L Z" 
  shows "X \<subseteq>\<^sub>L Z +\<^sub>L Y"
  using lens_plus_ub sublens_trans vwb_lens_def assms by blast

lemma lens_quotient_plus_den3 [simp, lens]: 
  assumes "weak_lens x" "weak_lens z" "x \<bowtie> z" "y \<subseteq>\<^sub>L z"
  shows "y /\<^sub>L (z +\<^sub>L x) = (y /\<^sub>L z) ;\<^sub>L fst\<^sub>L "
  using assms
  by (auto simp add: lens_defs prod.case_eq_if fun_eq_iff lens_indep.lens_put_irr1 lens_indep.lens_put_irr2)

declare lens_indep_impl_scene_indep_var [lens]

(* Turn off notation from HOL that clashes with ours *)

bundle Hybrid_Program_Syntax
begin

no_notation Transitive_Closure.rtrancl (\<open>(\<open>notation=\<open>postfix *\<close>\<close>_\<^sup>*)\<close> [1000] 999)
no_notation (ASCII) disj (infixr "|" 30)
no_notation (ASCII)
  Set.member  ("'(:')") and
  Set.member  ("(_/ : _)" [51, 51] 50)

end

syntax
  "_preserves"       :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infix "preserves" 40)
  "_preserves_under" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_ preserves _ under _" [40, 0, 40] 40)

translations
  "_preserves S P" => "H{P} S {P}"
  "_preserves_under S P Q" => "H{P \<and> Q} S {P}"

unbundle Hybrid_Program_Syntax

(* People will mainly be using this theory for doing verification, so we turn on literal variables,
   and enable pretty printing of expressions  *)

declare [[literal_variables, pretty_print_exprs, mark_state_variables=false]]

no_notation (ASCII) disj (infixr "|" 30)

(* Should lens gets appear in VCs, it's better they are concise and pretty *)

syntax
  "_lens_get_pretty" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("_<_>" [999,0] 999)

translations
  "_lens_get_pretty x s" == "CONST lens_get x s"

(* Print translation tweaks for syntax *)

translations
  (* Display sequents using the semantic bracket notation *)
  "_bigimpl (_asm P) Q" <= "CONST Pure.imp P Q"
  "_bigimpl (_asms (_asm P) Q) R" <= "_bigimpl (_asm P) (_bigimpl Q R)"

(* Optional: Pretty printing of Hoare triples *)

(* 
syntax
  "_hoare" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("Precondition: _//Program: _//Postcondition: _")
*)

end