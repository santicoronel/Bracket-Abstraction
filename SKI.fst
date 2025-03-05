module SKI

open FStar.List.Tot

type ty : Type =
  | Fun : ty -> ty -> ty
  | T : ty

type term : Type =
  | Unit : term 
  | Var : nat -> term
  | S : term
  | K : term
  | I : term
  | Abs : ty -> term -> term
  | App : term -> term -> term


let rec nclosed (n : nat) (t : term) : Tot bool (decreases t) =
  match t with
  | Var i -> i < n
  | Abs _ t -> nclosed (n + 1) t
  | App t u -> nclosed n t && nclosed n u
  | _ -> true

let closed : term -> bool = nclosed 0

let nclosed_term (n : nat) = t : term {nclosed n t}

let closed_term = nclosed_term 0

let rec is_Lam (t : term) : bool = match t with
  | Unit -> true
  | Var _ -> true
  | Abs _ t -> is_Lam t
  | App t u -> is_Lam t && is_Lam u
  | _ -> false

let lam = t : term {is_Lam t}

let nclosed_lam (n : nat) = t : lam {nclosed n t}

let closed_lam = nclosed_lam 0

let rec is_SKI (t : term) : bool = match t with
  | Unit -> true
  | Var _ -> true
  | S -> true
  | K -> true
  | I -> true
  | App t u -> is_SKI t && is_SKI u
  | _ -> false

let ski = t : term {is_SKI t}

let nclosed_ski (n : nat) = t : ski {nclosed n t}

let closed_ski = nclosed_ski 0


// ------------------------------------------------------------------------




// ------------------------------------------------------------------------


let rec shiftn (n : nat) (t : term) : Tot term (decreases t) =
  match t with
  | Var i -> if i < n then Var i else Var (i + 1)
  | Abs a t -> Abs a (shiftn (n + 1) t)
  | App t u -> App (shiftn n t) (shiftn n u)
  | _ -> t

let rec shift_lam (n : nat) (t : lam)
: Lemma (ensures is_Lam (shiftn n t)) (decreases t)
= match t with
  | Abs _ t -> shift_lam (n + 1) t
  | App t u -> shift_lam n t ; shift_lam n u
  | _ -> ()

let shift = shiftn 0

let rec subst (t : term) (v : term) (n : nat) : term =
  match t with
  | Var i -> if i = n then v else Var i
  | Abs a t -> Abs a (subst t (shift v) (n + 1))
  | App t u -> App (subst t v n) (subst u v n)
  | _ -> t

let rec subst_lam_lem (t : lam) (v : lam) (n : nat)
: Lemma (is_Lam (subst t v n))
= match t with
  | Abs a t -> shift_lam 0 v ; subst_lam_lem t (shift v) (n + 1)
  | App t u -> subst_lam_lem t v n ; subst_lam_lem u v n 
  | _ -> ()

let subst_lam (t v : lam) (n : nat) : lam = subst_lam_lem t v n ; subst t v n

let subst0 (t : lam) (v : lam) : lam = subst_lam t v 0

type step : lam -> lam -> Type =
  | AppL : #t : lam -> #t' : lam -> step t t' -> u : lam -> step (App t u) (App t' u)
  | Beta : a : ty -> t : lam -> u : lam -> step (App (Abs a t) u) (subst0 t u)

let rec nclosed_step_sub (n : nat) (#t #u : lam) (st : step t u) : bool =
  match st with
  | AppL #t #t' st' u -> nclosed n t && nclosed n t' && nclosed_step_sub n st' && nclosed n u
  | Beta _ t u -> nclosed (n + 1) t && nclosed n u

// Se puede probar algo mas fuerte: basta con que `t` o `u` sean n-cerrados.
let rec nclosed_step_impl (n : nat) (#t #u : nclosed_lam n) (st : step t u)
: Lemma (nclosed_step_sub n st) =
  match st with
  | AppL st' u -> nclosed_step_impl n st'
  | Beta _ t u -> ()



let fnl (t : ski) : bool = match t with
  | App (App S _) _ -> true
  | App S _ -> true
  | App K _ -> true
  | S -> true
  | K -> true
  | I -> true
  | _ -> false

let rec extend (#n #k : nat) (t : nclosed_term n)
: Tot (nclosed_term (n + k)) (decreases t) =
  match t with
  | App t u -> App (extend #n #k t) (extend #n #k u)
  | Abs a t -> Abs a (extend #(n + 1) #k t)
  | _ -> t

let rec extend_ski (#n #k : nat) (t : nclosed_ski n)
: Tot (nclosed_ski (n + k)) (decreases t) =
  match t with
  | App t u -> App (extend_ski #n #k t) (extend_ski #n #k u)
  | _ -> t

let expand (#n : nat) (t : nclosed_ski n) : nclosed_ski (n + 1) =
  App (extend_ski #n #1 t) (Var n)


// MAYBE sacar lo de nclosed
type ski_eq : (#n : nat) -> nclosed_ski n -> nclosed_ski n -> Type =
  | Refl : #n : nat -> t : nclosed_ski n -> ski_eq t t
  | Symm : #n : nat -> #t : nclosed_ski n -> #u : nclosed_ski n ->
            ski_eq t u -> ski_eq u t
  | Tran : #n : nat ->
           #t : nclosed_ski n -> #u : nclosed_ski n -> #v : nclosed_ski n ->
            ski_eq t u -> ski_eq u v -> ski_eq t v
  | App_eq : #n : nat ->
             #t1 : nclosed_ski n -> #t2 : nclosed_ski n ->
             #u1 : nclosed_ski n -> #u2 : nclosed_ski n ->
              ski_eq t1 t2 -> ski_eq u1 u2 ->
              ski_eq #n (App t1 u1) (App t2 u2)
  | Zeta : #n : nat ->
           #t : nclosed_ski n {fnl t} -> #u : nclosed_ski n {fnl u} ->
           ski_eq #(n + 1) (expand #n t) (expand #n u)
  | Red_S : #n : nat ->
            f : nclosed_ski n -> g : nclosed_ski n -> x : nclosed_ski n ->
            ski_eq #n (App (App (App S f) g) x) (App (App f x) (App g x))
  | Red_K : #n : nat ->
            a : nclosed_ski n -> b : nclosed_ski n ->
            ski_eq (App (App K a) b) a
  | Red_I : #n : nat -> x : nclosed_ski n -> ski_eq (App I x) x
