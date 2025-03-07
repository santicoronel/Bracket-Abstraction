module Lam.Equality

open SKI
open Subst

type step : lam -> lam -> Type =
  | AppL : #t : lam -> #t' : lam -> step t t' -> u : lam -> step (App t u) (App t' u)
  | AppR : t : lam -> #u : lam -> #u' : lam -> step u u' -> step (App t u) (App t u')
  | Beta : a : ty -> t : lam -> u : lam -> step (App (Abs a t) u) (subst0 t u)
  | Down : a : ty -> #t : lam -> #t' : lam -> step t t' -> step (Abs a t) (Abs a t') 

let rec nclosed_step_sub (n : nat) (#t #u : lam) (st : step t u)
: Tot bool (decreases st) =
  match st with
  | AppL #t #t' st' u -> nclosed n t && nclosed n t' && nclosed_step_sub n st' && nclosed n u
  | AppR t #u #u' st' -> nclosed n t && nclosed n u && nclosed n u' && nclosed_step_sub n st'
  | Beta _ t u -> nclosed (n + 1) t && nclosed n u
  | Down _ #t #t' st' -> nclosed (n + 1) t && nclosed (n + 1) t && nclosed_step_sub (n + 1) st'

// Se puede probar algo mas fuerte: basta con que `t` o `u` sean n-cerrados.
let rec nclosed_step_impl (n : nat) (#t #u : nclosed_lam n) (st : step t u)
: Lemma (ensures nclosed_step_sub n st) (decreases st) =
  match st with
  | AppL st' u -> nclosed_step_impl n st'
  | AppR t st' -> nclosed_step_impl n st'
  | Beta _ t u -> ()
  | Down _ st' -> nclosed_step_impl (n + 1) st'