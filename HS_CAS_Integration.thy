theory HS_CAS_Integration
  imports "HS_Lens_Spartan" "CAS_Integration.Subst_ODE"
  keywords "solve_ode" :: thy_decl
begin

ML \<open>
let
  fun solve_subst_ode_cmd ctx sode =
    let
      open Syntax
      val tm = Solve_Subst_ODE.solve_subst_ode ctx sode
      val {odes = odes, ...} = Subst_ODE.subst_ode "t" sode
      val frame = foldl1 (fn (x, y) => const @{const_name lens_plus} $ x $ y) (map (Expr_Util.const_or_free ctx) (Symtab.keys odes))
      val lflow = @{term "local_flow_on"} $ sode $ frame $ const @{const_abbrev UNIV} $ const @{const_abbrev UNIV} $ tm
    in 
    "Found ODE solution: " ^ Active.sendback_markup_command ("lemma \"" ^ Syntax.string_of_term ctx lflow ^ "\" by local_flow_auto") |> writeln
    end
  in
  Outer_Syntax.local_theory \<^command_keyword>\<open>solve_ode\<close> "Use a CAS to provide an ODE solution"
    (Parse.term >> (fn tm =>
        (fn ctx => solve_subst_ode_cmd ctx (Syntax.read_term ctx tm) |> (fn _ => ctx))))
end

\<close>

end