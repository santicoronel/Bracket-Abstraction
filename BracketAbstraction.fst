module BracketAbstraction

open SKI

let rec abstract (t : ski) : Tot ski (decreases t) =
  match t with
  | Var 0 -> I
  | Var i -> App K (Var (i - 1))
  | App t u -> App (App S (abstract t)) (abstract u)
  | _ -> App K t

let rec bracket_abstraction (t : term) : Tot ski =
  match t with
  | App t u -> App (bracket_abstraction t) (bracket_abstraction u)
  | Abs t -> abstract (bracket_abstraction t)
  | _ -> t

let rec closed_abstraction (n : pos) (t : nclosed_ski n)
: Lemma (ensures nclosed (n - 1) (abstract t)) =
  match t with
  | App t u -> closed_abstraction n t ; closed_abstraction n u
  | _ -> ()

let rec closed_bracket (n : nat) (t : nclosed_term n)
: Lemma (ensures nclosed n (bracket_abstraction t))
        (decreases t) =
  match t with
  | App t u -> closed_bracket n t ; closed_bracket n u
  | Abs t ->
    closed_bracket (n + 1) t ;
    closed_abstraction (n + 1) (bracket_abstraction t)
  | _ -> ()

let nclosed_bracket_abstraction (n : nat) (t : nclosed_lam n) : nclosed_ski n =
  closed_bracket n t ;
  bracket_abstraction t

// Mapeamos lambdas cerrados a terminos SKI cerrados
let closed_bracket_abstraction (t : closed_lam) : closed_ski =
  closed_bracket 0 t ;
  bracket_abstraction t
