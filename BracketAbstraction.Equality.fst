module BracketAbstraction.Equality

open SKI
open BracketAbstraction


let subst_bracket (n i : nat) (t v : nclosed_lam n)
: Lemma (requires i <= n) 
        (ensures bracket_abstraction (subst_lam t v i) = subst (bracket_abstraction t) (bracket_abstraction v) i)
= admit ()

let rec step_preserves_eq (#n : nat) (#t #u : nclosed_lam n) (st : step t u)
: ski_eq #n (nclosed_bracket_abstraction n t) (nclosed_bracket_abstraction n u) =
  match st with
  | AppL st_t u -> 
    nclosed_step_impl n st ;
    App_eq (step_preserves_eq st_t) (Refl (nclosed_bracket_abstraction n u))
  | Beta a t u ->
    nclosed_step_impl n st ;
    match t with
    | Var 0 -> Red_I (nclosed_bracket_abstraction n u)
    | Abs _ t -> admit ()
    | App t1 t2 -> admit ()
    | _ -> admit ()