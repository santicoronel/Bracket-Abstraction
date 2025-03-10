module SKI.Equality

open SKI
open Subst


type ski_step : ski -> ski -> Type =
  | Red_S : f : ski -> g : ski -> x : ski ->
            ski_step (App (App (App S f) g) x) (App (App f x) (App g x))
  | Red_K : a : ski -> b : ski ->
            ski_step (App (App K a) b) a
  | Red_I : x : ski -> ski_step (App I x) x

let fnl (t : ski) : bool = match t with
  | App (App S _) _ -> true
  | App S _ -> true
  | App K _ -> true
  | S -> true
  | K -> true
  | I -> true
  | _ -> false

noeq
type ski_eq : ski -> ski -> Type =
  | SRefl : t : ski -> ski_eq t t
  | SSymm : #t : ski -> #u : ski -> ski_eq t u -> ski_eq u t
  | STran : #t : ski -> #u : ski -> #v : ski ->
            ski_eq t u -> ski_eq u v -> ski_eq t v
  // voy a tener q cambiar esto y tener AppL y AppR
  | SAppL : #t : ski -> #t' : ski ->
            ski_eq t t' -> u : ski ->
            ski_eq (App t u) (App t' u)
  | SAppR : t : ski -> #u : ski -> #u' : ski ->
            ski_eq u u' -> ski_eq (App t u) (App t u')
  | Zeta : #t : ski {fnl t} -> #u : ski {fnl u} ->
           (i : nat {not_free i t && not_free i u} ->
           ski_eq (App t (Var i)) (App u (Var i))) ->
           ski_eq t u
  | SStep : #t : ski -> #u : ski -> ski_step t u -> ski_eq t u

let ski_app_eq (#t #t' #u #u' : ski)
               (eq_t : ski_eq t t') (eq_u : ski_eq u u')
: ski_eq (App t u) (App t' u')
= STran (SAppL eq_t u) (SAppR t' eq_u)