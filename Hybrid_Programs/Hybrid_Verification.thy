theory Hybrid_Verification
  imports
    Diff_Dyn_Logic
    Proof_Automation
    HS_CAS_Integration
begin

(* People will mainly be using this theory for doing verification, so we turn on literal variables *)

lit_vars
no_notation (ASCII) disj (infixr "|" 30)

end