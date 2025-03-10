module SKI.Equality

open SKI
open Subst


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
  | Refl : t : ski -> ski_eq t t
  | Symm : #t : ski -> #u : ski -> ski_eq t u -> ski_eq u t
  | Tran : #t : ski -> #u : ski -> #v : ski ->
            ski_eq t u -> ski_eq u v -> ski_eq t v
  // voy a tener q cambiar esto y tener AppL y AppR
  | App_eq : #t1 : ski -> #t2 : ski ->
             #u1 : ski -> #u2 : ski ->
              ski_eq t1 t2 -> ski_eq u1 u2 ->
              ski_eq (App t1 u1) (App t2 u2)
  | Zeta : #t : ski {fnl t} -> #u : ski {fnl u} ->
           (i : nat {not_free i t && not_free i u} ->
           ski_eq (App t (Var i)) (App u (Var i))) ->
           ski_eq t u
  | Red_S : f : ski -> g : ski -> x : ski ->
            ski_eq (App (App (App S f) g) x) (App (App f x) (App g x))
  | Red_K : a : ski -> b : ski ->
            ski_eq (App (App K a) b) a
  | Red_I : x : ski -> ski_eq (App I x) x