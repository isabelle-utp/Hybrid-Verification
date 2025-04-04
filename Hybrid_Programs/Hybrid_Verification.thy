theory Hybrid_Verification
  imports
    Diff_Dyn_Logic
    Proof_Automation
    HS_CAS_Integration
begin

(* Turn off notation from HOL that clashes with ours *)

bundle Hybrid_Program_Syntax
begin

no_notation Transitive_Closure.rtrancl ("(_\<^sup>*)" [1000] 999)
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

lit_vars
pretty_exprs
expr_no_mark_vars
no_notation (ASCII) disj (infixr "|" 30)

(* Should lens gets appear in VCs, it's better they are concise and pretty *)

syntax
  "_lens_get_pretty" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("_<_>" [999,0] 999)

translations
  "_lens_get_pretty x s" == "CONST lens_get x s"

(* Optional: Pretty printing of Hoare triples *)

(* 
syntax
  "_hoare" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("Precondition: _//Program: _//Postcondition: _")
*)

end