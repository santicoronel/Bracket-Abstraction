module BracketAbstraction

open SKI

let rec abstract (t : term) : Tot term (decreases t) =
  match t with
  | Var 0 -> I
  | Var i -> App K (Var (i - 1))
  | App t u -> App (App S (abstract t)) (abstract u)
  | _ -> App K t

let rec bracket_abstraction0 (t : term) : Tot term =
  match t with
  | App t u -> App (bracket_abstraction0 t) (bracket_abstraction0 u)
  | Abs _ t -> abstract (bracket_abstraction0 t)
  | _ -> t


let rec abstraction_ski (t : ski) : Lemma (is_SKI (abstract t)) =
  match t with
  | App t u -> abstraction_ski t ; abstraction_ski u
  | _ -> _

let rec bracket_ski (t : term) : Lemma (is_SKI (bracket_abstraction0 t)) =
  match t with
  | App t u -> bracket_ski t ; bracket_ski u
  | Abs _ t -> bracket_ski t ; abstraction_ski (bracket_abstraction0 t)
  | _ -> ()


let rec closed_abstraction (n : pos) (t : nclosed_ski n)
: Lemma (ensures nclosed (n - 1) (abstract t) && is_SKI (abstract t)) =
  match t with
  | App t u -> closed_abstraction n t ; closed_abstraction n u
  | _ -> ()

let rec closed_bracket (n : nat) (t : nclosed_term n)
: Lemma (ensures nclosed n (bracket_abstraction0 t) && is_SKI (bracket_abstraction0 t))
        (decreases t) =
  match t with
  | App t u -> closed_bracket n t ; closed_bracket n u
  | Abs _ t ->
    closed_bracket (n + 1) t ;
    closed_abstraction (n + 1) (bracket_abstraction0 t)
  | _ -> ()


let bracket_abstraction (t : lam) : ski =
  bracket_ski t ;
  bracket_abstraction0 t

let nclosed_abstraction (n : pos) (t : nclosed_ski n) : nclosed_ski (n -1) =
  closed_abstraction n t ;
  abstract t

let nclosed_bracket_abstraction (n : nat) (t : nclosed_lam n) : nclosed_ski n =
  closed_bracket n t ;
  bracket_abstraction0 t

let closed_bracket_abstraction (t : closed_lam) : closed_ski =
  closed_bracket 0 t ;
  bracket_abstraction0 t
