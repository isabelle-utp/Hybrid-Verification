signature SPEC_UTILS =
sig
    val is_hoare_triple: term -> bool
    val dest_hoare_triple: term -> term * term * term
    val inst_hoare_rule_tac: thm -> string -> Proof.context -> term -> term -> tactic
end

structure Spec_Utils : SPEC_UTILS =
struct

(* Check whether a term is a Hoare triple *)
fun is_hoare_triple
  (Const (@{const_name "Trueprop"}, _) 
     $ (Const (@{const_name less_eq}, _) $ _ $ (Const (@{const_name fbox}, _) $ _ $ _))) = true |
is_hoare_triple _ = false;

(* Destruct a Hoare triple *)
fun dest_hoare_triple
      (Const (@{const_name "Trueprop"}, _) 
        $ (Const (@{const_name less_eq}, _) $ P $ (Const (@{const_name fbox}, _) $ C $ Q))) = (P, C, Q) |
dest_hoare_triple _ = error "Goal is not a Hoare triple"

(* Instantiate a Hoare logic law with an assertion (e.g. an invariant) *)
fun inst_hoare_rule_tac thm var ctx rt goal =
  let fun strip_alls (Const ("Pure.all", _) $ (u as Abs _)) = strip_alls (snd (Term.dest_abs_global u)) |
          strip_alls t = t;
      val concl = Logic.strip_imp_concl (strip_alls goal) 
  in
    if is_hoare_triple concl
    then let val (P, _, _) = dest_hoare_triple concl; 
             val stT = fst (dest_funT (fastype_of P)) 
             val t = Syntax.check_term ctx (Lift_Expr.mk_lift_expr ctx stT rt)
             val ct = Thm.cterm_of ctx t
             val cstT = Thm.ctyp_of ctx stT
             val ithm = Thm.instantiate (TVars.make1 ((("'a", 0), @{sort type}), cstT)
                                        ,Vars.make1 (((var, 0), stT --> @{typ bool}), ct)) thm
         in resolve_tac ctx [ithm] 1 end 
    else error "Goal is not a Hoare triple"
  end


end