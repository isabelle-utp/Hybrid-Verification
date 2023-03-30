theory HS_CAS_Integration
  imports Proof_Automation "CAS_Integration.Subst_ODE"
  keywords "find_local_flow" :: diag
begin

ML \<open>
fun match_term (top, _) = case top of
     Const ("Framed_Dyn_Sys.g_orbital_on", _) => true
   | _ => false

fun find_ode term =
let
open Zipper
val matches = Seq.filter match_term (EqSubst.search_lr_all (mktop term))
val get_ode = (move_up_right #> move_up_right #> move_down_right #> move_down_abs #> trm)
in
  get_ode (Seq.hd matches)
end

(* Legacy function - reconstructs original ODE *)
fun solve_subst_ode_cmd ctx term =
    let
      open Syntax
      val sode = find_ode term
      val tm = Solve_Subst_ODE.solve_subst_ode ctx sode
      val {odes = odes, ...} = Subst_ODE.subst_ode "t" sode
      val frame = foldl1 (fn (x, y) => const @{const_name lens_plus} $ x $ y) (map (Expr_Util.const_or_free ctx) (Symtab.keys odes))
      val lflow = @{term "local_flow_on"} $ sode $ frame $ const @{const_abbrev UNIV} $ const @{const_abbrev UNIV} $ tm
    in
    "Found ODE solution: " ^ Active.sendback_markup_command ("lemma \"" ^ Syntax.string_of_term ctx lflow ^ "\" by local_flow_auto") |> writeln
    end;

fun find_local_flow_cmd state =
    let
      val ctx = Proof.context_of state
      val {goal = g, ...} = Proof.goal state
      val term = Thm.concl_of g
      val sode = find_ode term
      val tm = Solve_Subst_ODE.solve_subst_ode ctx sode
    in 
    "try this: " ^ Active.sendback_markup_command
     ("apply (wlp_solve \"" ^ Syntax.string_of_term ctx tm ^ "\")") |> writeln
   end
;


val _ =
  Outer_Syntax.command \<^command_keyword>\<open>find_local_flow\<close>
    "search for solutions to ODEs using a CAS"
    (Scan.option Parse.string >>
      (fn (_) =>
        Toplevel.keep_proof
          (find_local_flow_cmd o Toplevel.proof_of)))
\<close>
end
