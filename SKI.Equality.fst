module SKI.Equality

open SKI
open Subst


let fnl (t : term) : bool = match t with
  | App (App S _) _ -> true
  | App S _ -> true
  | App K _ -> true
  | S -> true
  | K -> true
  | I -> true
  | _ -> false


let rel (a b : Type) = a -> b -> Type

noeq
type eq (#a : Type) (app : a -> a -> a) (r : rel a a)
: a -> a -> Type =
  | Refl : t : a -> eq app r t t
  | Symm : #t : a -> #u : a -> r t u -> eq app r u t
  | Tran : #t : a -> #u : a -> #v : a ->
            r t u -> r u v -> eq app r t v
  | AppL : #t : a -> #t' : a ->
            r t t' -> u : a ->
            eq app r (app t u) (app t' u)
  | AppR : t : a -> #u : a -> #u' : a ->
            r u u' -> eq app r (app t u) (app t u')


let lapp (x y : lam) : z : lam {z = App x y} = App x y

noeq
type lam_eq : lam -> lam -> Type =
  | Beta : t : lam -> u : lam -> lam_eq (App (Abs t) u) (subst0 t u)
  | Down : #t : lam -> #t' : lam -> lam_eq t t' -> lam_eq (Abs t) (Abs t') 
  | Eq_L : #t : lam -> #u : lam -> eq lapp lam_eq t u -> lam_eq t u 


let sapp (x y : ski) : z : ski {z = App x y} = App x y

noeq
type ski_eq : ski -> ski -> Type =
  | RedS : f : ski -> g : ski -> x : ski ->
            ski_eq (App (App (App S f) g) x) (App (App f x) (App g x))
  | RedK : a : ski -> b : ski ->
            ski_eq (App (App K a) b) a
  | RedI : x : ski -> ski_eq (App I x) x
  | Zeta : #t : ski {fnl t} -> #u : ski {fnl u} ->
           (i : nat {not_free i t && not_free i u} ->
           ski_eq (App t (Var i)) (App u (Var i))) ->
           ski_eq t u
  | Eq_S : #t : ski -> #u : ski -> eq sapp ski_eq t u -> ski_eq t u



let app_eq_ski (#t #t' #u #u' : ski)
           (eq_t : ski_eq t t') (eq_u : ski_eq u u')
: (if true then ski_eq else ski_eq) (App t u) (App t' u')
= Eq_S (Tran (Eq_S (AppL eq_t u)) (Eq_S (AppR t' #u #u' eq_u)))