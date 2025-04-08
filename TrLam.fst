module TrLam

open SKI
open Subst

let rec trlam (t : ski) : lam =
  match t with
  | Var i -> Var i
  | S -> 
    let f = Var 2 in
    let g = Var 1 in
    let x = Var 0 in
    Abs (Abs (Abs (App (App f x) (App g x))))
  | K -> 
    let x = Var 1 in
    Abs (Abs x)
  | I -> 
    let x = Var 0 in
    Abs x
  | App t u -> App (trlam t) (trlam u)

let rec not_free_trlam (i : nat) (t : ski)
: Lemma (requires not_free i t) (ensures not_free i (trlam t))
= match t with
  | App t u -> not_free_trlam i t ; not_free_trlam i u
  | _ -> ()