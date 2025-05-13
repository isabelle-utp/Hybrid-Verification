signature SPEC_UTILS =
sig
    val is_hoare_triple: term -> bool
    val dest_hoare_triple: term -> term * term * term
end

structure Spec_Utils : SPEC_UTILS =
struct

fun is_hoare_triple
  (Const (@{const_name "Trueprop"}, _) 
     $ (Const (@{const_name less_eq}, _) $ _ $ (Const (@{const_name fbox}, _) $ _ $ _))) = true |
is_hoare_triple _ = false;

fun dest_hoare_triple
      (Const (@{const_name "Trueprop"}, _) 
        $ (Const (@{const_name less_eq}, _) $ P $ (Const (@{const_name fbox}, _) $ C $ Q))) = (P, C, Q) |
dest_hoare_triple _ = error "Goal is not a Hoare triple"

end