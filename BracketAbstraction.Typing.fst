module BracketAbstraction.Typing

open SKI
open SKI.Typing
open BracketAbstraction

let rec abstract_typing (#n : pos) (#ctx : context (n - 1)) (#t : nclosed_ski n)
                        (#tx : ty) (#tt : ty)
                        (typ : typing (Cons tx ctx) t tt)
                       : Tot (typing ctx (nclosed_abstraction n t) (Fun tx tt)) =
  match typ with
  | TVar 0 -> TI tx
  | TVar i ->
  let tvar_i = tvar (i - 1) ctx in
  let typ_k = TK tvar_i tx in
  let typ_v = TVar #_ #ctx (i - 1) in
  TApp typ_k typ_v
  | TApp #_ #_ #_ #_ #a # b typ_t typ_u ->
    let typ_t = abstract_typing typ_t in
    let typ_u = abstract_typing typ_u in
    let typ_S = TS tx a b in
    TApp (TApp typ_S typ_t) typ_u
  | TUnit -> TApp (TK tt tx) TUnit
  | TS a b c -> TApp (TK tt tx) (TS a b c)
  | TK a b -> TApp (TK tt tx) (TK a b)
  | TI a -> TApp (TK tt tx) (TI a)


let rec bracket_typing (#n : nat) (#ctx : context n) (#t : nclosed_lam n)
                       (#tt : ty)
                       (typ : typing ctx t tt)
                       : Tot (typing ctx (nclosed_bracket_abstraction n t) tt)
                             (decreases typ) =
  match t with
  | App t u -> let TApp typ_t typ_u = typ in 
    TApp (bracket_typing typ_t) (bracket_typing typ_u)
  | Abs _ t -> let TAbs a typ_t = typ in
    let typ_t' = bracket_typing #(n + 1) #(Cons a ctx) #t #_ typ_t in
    abstract_typing typ_t'
  | _ -> typ
