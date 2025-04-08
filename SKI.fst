module SKI

open FStar.List.Tot


type term : Type =
  | Var : nat -> term
  | S : term
  | K : term
  | I : term
  | Abs : term -> term
  | App : term -> term -> term


let rec nclosed (n : nat) (t : term) : Tot bool (decreases t) =
  match t with
  | Var i -> i < n
  | Abs t -> nclosed (n + 1) t
  | App t u -> nclosed n t && nclosed n u
  | _ -> true


let nclosed_term (n : nat) = t : term {nclosed n t}

let nclosed_App (n : nat) (t u : nclosed_term n)
: Lemma (nclosed n (App t u)) = ()

let rec is_Lam (t : term) : bool = match t with
  | Var _ -> true
  | Abs t -> is_Lam t
  | App t u -> is_Lam t && is_Lam u
  | _ -> false

let lam = t : term {is_Lam t}

let nclosed_lam (n : nat) = t : lam {nclosed n t}

let closed_lam = nclosed_lam 0

let rec is_SKI (t : term) : bool = match t with
  | Var _ -> true
  | S -> true
  | K -> true
  | I -> true
  | App t u -> is_SKI t && is_SKI u
  | _ -> false

let ski = t : term {is_SKI t}

let nclosed_ski (n : nat) = t : ski {nclosed n t}

let closed_ski = nclosed_ski 0

let max (x y : int)
: Pure int true (fun z -> (z = x \/ z = y) /\ x <= z /\ y <= z)
= if x < y then y else x

let rec free (i : nat) (t : term) : Tot bool (decreases t)
= match t with
  | Var j -> j = i
  | Abs t -> free (i + 1) t
  | App t u -> free i t || free i u
  | _ -> false

let not_free (i : nat) (t : term) = not (free i t)

let rec _freshn (n : nat) (t : term)
: Tot nat (decreases t)
= match t with
  | Var i -> if i < n then 0 else i - n + 1
  | Abs t' -> _freshn (n + 1) t'
  | App t u -> max (_freshn n t) (_freshn n u)
  | _ -> 0

let rec lem_freshn (n : nat) (t : term) (j : nat)
: Lemma (requires free (j + n) t) (ensures _freshn n t > j) (decreases t)
= match t with
  | Abs t' -> lem_freshn (n + 1) t' j
  | App t u -> 
    if free (j + n) t
    then lem_freshn n t j
    else lem_freshn n u j
  | _ -> ()

let freshn (n : nat) (t : term)
: Pure nat true (fun i -> forall (j : nat). free (j + n) t ==> i > j)
= let i = _freshn n t in
  introduce forall (j : nat). free (j + n) t ==> i > j with
  introduce free (j + n) t ==> i > j with
  _. lem_freshn n t j;
  i

let fresh (t : term) : i : nat {not_free i t} = freshn 0 t

let rec fresh_for_all (l : list term)
: Pure nat true 
      (fun i -> for_all (not_free i) l /\ 
                (forall (j : nat). j > i ==> for_all (not_free j) l))
= match l with
  | [] -> 0
  | t :: ts ->
  max (fresh t) (fresh_for_all ts)