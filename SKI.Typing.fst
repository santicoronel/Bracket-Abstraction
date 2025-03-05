module SKI.Typing

open SKI

type context : nat -> Type =
  | Nil : context 0
  | Cons : (#n : nat) -> ty -> context n -> context (n + 1)  

let rec tvar (#n : nat) (i : nat {i < n}) (ctx : context n)
: Tot ty (decreases i) =
  match ctx with
  | Cons ty ctx -> if i = 0 then ty else tvar (i - 1) ctx 


let s_type (a b c : ty) = Fun (Fun a (Fun b c)) (Fun (Fun a b) (Fun a c))
let k_type (a b : ty) = Fun a (Fun b a)
let i_type (a : ty) = Fun a a

type typing : #n : nat -> context n -> t : nclosed_term n -> ty -> Type =
  | TUnit : #n : nat -> #ctx : context n -> typing ctx Unit T
  | TVar : #n : nat -> #ctx : context n -> 
            i : nat {i < n} -> typing ctx (Var i) (tvar i ctx)
  | TS : #n : nat -> #ctx : context n ->
          a : ty -> b : ty -> c : ty -> typing ctx S (s_type a b c)
  | TK : #n : nat -> #ctx : context n ->
          a : ty -> b : ty -> typing ctx K (k_type a b)
  | TI : #n : nat -> #ctx : context n ->
          a : ty -> typing ctx I (i_type a)
  | TAbs : #n : nat -> #ctx : context n ->
           #t : nclosed_term (n + 1) -> #b : ty ->
            a : ty -> typing (Cons a ctx) t b ->
            typing ctx (Abs a t) (Fun a b)
  | TApp : #n : nat -> #ctx : context n ->
           #t : nclosed_term n -> #u : nclosed_term n ->
           #a : ty -> #b : ty ->
           typing ctx t (Fun a b) -> typing ctx u a ->
           typing ctx (App t u) b

let rec infer_lam (#n:nat) (ctx : context n) (t : nclosed_lam n)
  : Tot (option ((tt : ty) & typing ctx t tt)) (decreases t) =
  match t with
  | Unit -> Some (|T, TUnit|)
  | Var i -> Some (|tvar i ctx, TVar i|)
  | Abs a t -> (
    match infer_lam (Cons a ctx) t with
      | Some (|tt, pf_tt|) -> Some (|Fun a tt, TAbs a pf_tt|)
      | None -> None
    )
  | App t u ->
    let infer_t = infer_lam ctx t in
    let infer_u = infer_lam ctx u in (
    match infer_t, infer_u with
      | Some (|Fun a b, pf_tt|), Some (|tu, pf_tu|) ->
        if a = tu
        then Some (|b, TApp pf_tt pf_tu|)
        else None
      | _ -> None
    )

// -----------------------------------------------------------------------------------

let rec ski_to_lam (#n : nat) (#ctx : context n) (#t : nclosed_ski n) (#tt : ty)
               (typ : typing ctx t tt) : nclosed_lam n =
  match typ with
  | TUnit -> Unit
  | TVar i -> Var i
  | TS a b c -> 
    let tf = Fun a (Fun b c) in
    let tg = Fun a b in
    let tx = a in
    let f = Var 2 in
    let g = Var 1 in
    let x = Var 0 in
    Abs tf (Abs tg (Abs tx (App (App f x) (App g x))))
  | TK a b -> Abs a (Abs b (Var 1))
  | TI a -> Abs a (Var 0)
  | TApp typ_t typ_u -> App (ski_to_lam typ_t) (ski_to_lam typ_u)