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


let expand (#n k : nat) (t : nclosed_ski n) : nclosed_ski (n + k) =
  App (extend_ski #n #1 t) (Var n)


// MAYBE sacar lo de nclosed
type ski_eq : (#n : nat) -> nclosed_ski n -> nclosed_ski n -> Type =
  | Refl : #n : nat -> t : nclosed_ski n -> ski_eq t t
  | Symm : #n : nat -> #t : nclosed_ski n -> #u : nclosed_ski n ->
            ski_eq t u -> ski_eq u t
  | Tran : #n : nat ->
           #t : nclosed_ski n -> #u : nclosed_ski n -> #v : nclosed_ski n ->
            ski_eq t u -> ski_eq u v -> ski_eq t v
  // voy a tener q cambiar esto y tener AppL y AppR
  | App_eq : #n : nat ->
             #t1 : nclosed_ski n -> #t2 : nclosed_ski n ->
             #u1 : nclosed_ski n -> #u2 : nclosed_ski n ->
              ski_eq t1 t2 -> ski_eq u1 u2 ->
              ski_eq #n (App t1 u1) (App t2 u2)
  | Zeta : #n : nat ->
           #t : nclosed_ski n {fnl t} -> #u : nclosed_ski n {fnl u} ->
           ski_eq #(n + 1) (expand #n t) (expand #n u) ->
           ski_eq #n t u
  | Red_S : #n : nat ->
            f : nclosed_ski n -> g : nclosed_ski n -> x : nclosed_ski n ->
            ski_eq #n (App (App (App S f) g) x) (App (App f x) (App g x))
  | Red_K : #n : nat ->
            a : nclosed_ski n -> b : nclosed_ski n ->
            ski_eq (App (App K a) b) a
  | Red_I : #n : nat -> x : nclosed_ski n -> ski_eq (App I x) x


let rec ext_Zeta (n k : nat) (#t #u : nclosed_ski n)
                 (eq : ski _eq (App t (Var (n + k))))


let rec extend_ski_eq (n k : nat) (#t #u : nclosed_ski n) (eq : ski_eq t u)
: Tot (ski_eq #(n + k) (extend #n #k t) (extend #n #k u)) (decreases eq)
= assert (extend #n #k t = t) ; 
  assert (extend #n #k u = u) ;
  match eq with
  | Refl _ -> Refl _
  | Symm eq -> Symm (extend_ski_eq n k eq)
  | Tran eq1 eq2 -> Tran (extend_ski_eq n k eq1) (extend_ski_eq n k eq2)
  | App_eq eq1 eq2 -> App_eq (extend_ski_eq n k eq1) (extend_ski_eq n k eq2)
  | Red_S f g x -> Red_S (extend #n #k f) (extend #n #k g) (extend #n #k x)
  | Red_K x y -> Red_K (extend #n #k x) (extend #n #k y)
  | Red_I x -> Red_I (extend #n #k x)
  | Zeta eq -> admit ()