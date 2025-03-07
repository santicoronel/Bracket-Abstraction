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

let nclosed_App (n : nat) (t u : nclosed_term n)
: Lemma (nclosed n (App t u)) = ()

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

let rec extend_lem (#n #k : nat) (t : nclosed_term n)
: Lemma (ensures nclosed (n + k) t) (decreases t) =
  match t with
  | App t u -> extend_lem #n #k t ; extend_lem #n #k u
  | Abs _ t -> extend_lem #(n + 1) #k t
  | _ -> ()

let extend (#n #k : nat) (t : term)
: Pure term
       (requires nclosed n t) 
       (ensures fun r -> nclosed (n + k) r /\ r = t)
       (decreases t) =
  extend_lem #n #k t ; t

let rec extend_ski (#n #k : nat) (t : ski)
: Pure ski
      (requires nclosed n t)
      (ensures fun r -> nclosed (n + k) r /\ r = t)
      (decreases t) =
  match t with
  | App t u -> App (extend_ski #n #k t) (extend_ski #n #k u)
  | _ -> t
