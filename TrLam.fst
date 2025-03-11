module TrLam

open SKI

let rec trlam (t : ski) : lam =
  match t with
  | Unit -> Unit
  | Var i -> Var i
  | S -> 
    let f = Var 2 in
    let g = Var 1 in
    let x = Var 0 in
    Abs (Abs (Abs (App (App f x) (App g x))))
  | K -> Abs (Abs (Var 1))
  | I -> Abs (Var 0)
  | App t u -> App (trlam t) (trlam u)
