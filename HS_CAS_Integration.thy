theory HS_CAS_Integration
  imports "HS_Lens_Spartan" "CAS_Integration.Subst_ODE"
  keywords "solve_ode" :: thy_decl
begin

ML \<open>
fun find_ode term =
let
open Zipper
val match_term = fn (top, _) => case top of Const ("HS_Lens_ODEs.g_orbital_on", _) => true
                                          | _ => false
val matches = EqSubst.search_lr_valid match_term (mktop term)
val get_ode = (move_up_right #> move_up_right #> move_down_right #> move_down_abs #> trm)
in
  get_ode (Seq.hd matches)
end

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

  Outer_Syntax.local_theory \<^command_keyword>\<open>solve_ode\<close> "Use a CAS to provide an ODE solution"
    (Parse.term >> (fn tm =>
        (fn ctx => solve_subst_ode_cmd ctx (Syntax.read_term ctx tm) |> (fn _ => ctx))))
\<close>

solve_ode "{y` = 2}"

end
