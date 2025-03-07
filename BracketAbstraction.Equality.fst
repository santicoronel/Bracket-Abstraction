module BracketAbstraction.Equality

open SKI
open SKI.Equality 
open BracketAbstraction
open Subst
open Lam.Equality



let abs_fnl (t : ski) : Lemma (fnl t ==> fnl (abstract_ski t))
= ()


let rec abstract_App (#n : nat) (t : nclosed_ski (n + 1)) (v : nclosed_ski n)
: ski_eq #n (App (nclosed_abstraction (n + 1) t) v) (subst_nclosed_ski #n t v 0)
= match t with
  | App t u ->
    let abs_t = nclosed_abstraction (n + 1) t  in
    let abs_u = nclosed_abstraction (n + 1) u  in
    let red_s = Red_S abs_t abs_u v in
    let hi_t = abstract_App t v in
    let hi_u = abstract_App u v in
    let app_eq = App_eq hi_t hi_u in
    Tran red_s app_eq
  | Var 0 -> Red_I v
  | Var j -> Red_K (Var (j - 1)) v
  | S -> Red_K S v
  | K -> Red_K K v
  | I -> Red_K I v
  | Unit -> Red_K Unit v


let rec expand_subst (n : nat) (t : nclosed_ski (n + 1)) (v : nclosed_ski n)
: Lemma (expand #n (subst_nclosed_ski t v 0) = subst_nclosed_ski (expand #(n + 1) t) (extend_ski #n #1 v) 0)
= match t with
  | App t u -> expand_subst n t v ; expand_subst n u v
  | _ -> ()

let rec subst_ski_eq (#n : nat) (#t #u: nclosed_ski (n + 1)) (eq : ski_eq t u)
                     (v : nclosed_ski n)
                     
: Tot (ski_eq #n (subst_nclosed_ski t v 0) (subst_nclosed_ski u v 0))
      (decreases eq)
= let sub t = subst_nclosed_ski t v 0 in
  match eq with
  | Refl _ -> Refl _
  | Symm eq -> Symm (subst_ski_eq eq v)
  | Tran eq1 eq2 -> Tran (subst_ski_eq eq1 v) (subst_ski_eq eq2 v)
  | App_eq eq1 eq2 -> App_eq (subst_ski_eq eq1 v) (subst_ski_eq eq2 v)
  | Red_S f g x -> Red_S (sub f) (sub g) (sub x)
  | Red_K x y -> Red_K (sub x) (sub y)
  | Red_I x -> Red_I (sub x)
  | Zeta eq ->
    expand_subst n t v ;
    expand_subst n u v ;
    Zeta (subst_ski_eq #(n + 1) eq (extend_ski #n #1 v))



let ( @ ) (#n : nat) (t u : nclosed_ski n) : nclosed_ski n = App t u


let rec abstract_ski_eq (n : pos) (#t #u : nclosed_ski n) (t_eq_u : ski_eq t u)
: Tot (ski_eq (nclosed_abstraction n t) (nclosed_abstraction n u))
      (decreases t_eq_u)
= match t_eq_u with
| Red_S f g x -> admit ()
// let f' : nclosed_ski n = extend_ski #(n - 1) #1 (nclosed_abstraction n f) in
// let g' : nclosed_ski n = extend_ski #(n - 1) #1 (nclosed_abstraction n g) in
// let x' : nclosed_ski n = extend_ski #(n - 1) #1 (nclosed_abstraction n x) in
// let y : nclosed_ski n = Var (n - 1) in
// let k  : nclosed_ski n = ((S @ ((S @ (K @ S)) @ f')) @ g') in 
// let red_1 = Red_S k x' y in
// let red_2 = Red_S (App (App S (App K S)) f') g' y in
// let red_3 = Red_S (App K S) f' y in
// let red_4 = Red_K S y in
// let app_2 = App_eq red_2 (Refl (App x' y)) in
// let app_3_1 = App_eq red_3 (Refl (App g' y)) in
// let app_3_2 = App_eq app_3_1 (Refl (App x' y)) in
// let app_4_1 = App_eq red_4 (Refl (App f' y)) in
// let app_4_2 = App_eq app_4_1 (Refl (App g' y)) in 
// let app_4_3 = App_eq app_4_2 (Refl (App x' y)) in
// let red_5 = Red_S #n (App f' y) (App g' y) (App x' y) in
// let lhs = Tran (Tran (Tran (Tran red_1 app_2) app_3_2) app_4_3) red_5 in
// let red_1 = Red_S ((S @ f') @ x') ((S @ g') @ x') y in
// let redl = Red_S f' x' y in
// let redr = Red_S g' x' y in
// let rhs = Tran red_1 (App_eq redl redr) in
// assert (t = ((S @ f) @ g) @ x) ;
// assert (abstract g = g') ;
// Zeta (Tran lhs (Symm rhs))
| Red_K x y ->
let x' : nclosed_ski n = extend_ski #(n - 1) #1 (nclosed_abstraction n x) in
let y' : nclosed_ski n = extend_ski #(n - 1) #1 (nclosed_abstraction n y) in
let z : nclosed_ski n = Var (n - 1) in
admit ()
| Red_I x ->
let x' : nclosed_ski n = extend_ski #(n - 1) #1 (nclosed_abstraction n x) in
let y : nclosed_ski n = Var (n - 1) in
let red_S = Red_S (K @ I) x' y in
let red_K = Red_K I y in
let app = App_eq (red_K) (Refl (x' @ y)) in
let red_I = Red_I (x' @ y) in
Zeta (Tran (Tran red_S app) red_I)
| App_eq eq1 eq2 -> App_eq (App_eq (Refl S) (abstract_ski_eq n eq1)) (abstract_ski_eq n eq2)
| Refl t -> Refl _
| Symm eq -> Symm (abstract_ski_eq n eq)
| Tran eq1 eq2 -> Tran (abstract_ski_eq n eq1) (abstract_ski_eq n eq2)
| Zeta eq -> admit ()




let rec shift_abs (n : nat) (t : ski)
: Lemma (shiftn n (abstract t) = abstract (shiftn (n + 1) t))
= match t with
  | App t u -> shift_abs n t ; shift_abs n u 
  | _ -> ()

let rec shift_bracket (i : nat) (t : lam)
: Lemma (ensures shiftn i (bracket_abstraction t) = bracket_abstraction (shiftn_lam i t))
        (decreases t)
= match t with
  | Abs a t ->
    shift_abs i (bracket_abstraction t) ;
    shift_bracket (i + 1) t
  | App t u -> shift_bracket i t ; shift_bracket i u
  | _ -> ()

let ski_eq_S_K (#n : nat) (t u : nclosed_ski n)
: ski_eq #n (App (App S (App K t)) (App K u)) (App K (App t u))
= let red_S = Red_S (extend_ski (App K t)) (extend_ski (App K u)) (Var n) in
  let red_K_l = Red_K #(n + 1) (extend_ski t) (Var n) in
  let red_K_r = Red_K #(n + 1) (extend_ski u) (Var n) in
  let red_K_app = App_eq red_K_l red_K_r in
  let lhs = Tran red_S red_K_app in
  let red_K = Red_K #(n + 1) (extend_ski (App t u)) (Var n) in
  let rhs = Symm red_K in
  Zeta (Tran lhs rhs)

let rec ski_eq_abstract (#n : nat) (t : nclosed_ski n)
: ski_eq #n (nclosed_abstraction (n + 1) (shift_nclosed_ski t)) (App K t)
= match t with
  | App t u ->
    let hi_t = ski_eq_abstract #n t in
    let hi_u = ski_eq_abstract #n u in
    let hi_appl = App_eq (Refl S) (hi_t) in
    let hi_app = App_eq (hi_appl) (hi_u) in
    let eq_SK = ski_eq_S_K #n t u in
    Tran hi_app eq_SK
  | _ -> Refl _

let rec subst_abstract (#n : nat) (t : nclosed_ski (n + 2)) (v : nclosed_ski n) (i : nat {i <= n})
: ski_eq #n (nclosed_abstraction (n + 1) (subst_nclosed_ski t (shift_nclosed_ski #n v) (i + 1)))
            (subst_nclosed_ski (nclosed_abstraction (n + 2) t) v i)
= match t with
  | App t u ->
    App_eq (App_eq (Refl S) (subst_abstract t v i)) (subst_abstract u v i)  
  | Var j ->
    if j = i + 1
    then ski_eq_abstract #n v
    else Refl _
  | _ -> Refl _


let rec subst_bracket (#n : nat) (t : nclosed_lam (n + 1)) (v : nclosed_lam n) (i : nat {i <= n})
: Tot
    (ski_eq #n
      (nclosed_bracket_abstraction n (subst_nclosed_lam t v i))
      (subst_nclosed_ski (nclosed_bracket_abstraction (n + 1) t) (nclosed_bracket_abstraction n v) i))
    (decreases t)
= match t with
  | Abs _ t ->
    // TODO comentar esto
    shift_bracket 0 v ;
    let hi = subst_bracket #(n + 1) t (shift_nclosed_lam v) (i + 1) in
    let hi = abstract_ski_eq (n + 1) _ _ hi in 
    let bracket_t = nclosed_bracket_abstraction (n + 2) t in
    let bracket_v = nclosed_bracket_abstraction n v in
    let subst_abstract_eq = subst_abstract bracket_t bracket_v i in
    Tran hi subst_abstract_eq
  | App t u -> App_eq (subst_bracket t v i) (subst_bracket u v i)
  | _ -> Refl _


let rec step_preserves_eq (#n : nat) (#t #u : nclosed_lam n) (st : step t u)
: ski_eq #n (nclosed_bracket_abstraction n t) (nclosed_bracket_abstraction n u) =
  match st with
  | AppL st_t u -> 
    nclosed_step_impl n st ;
    App_eq (step_preserves_eq st_t) (Refl (nclosed_bracket_abstraction n u))
  | AppR t st_u -> admit ()
  | Beta _ t u ->
    nclosed_step_impl n st ;
    let bracket_t = nclosed_bracket_abstraction (n + 1) t in
    let bracket_u = nclosed_bracket_abstraction n u in
    Tran (abstract_App #n bracket_t bracket_u) (Symm (subst_bracket #n t u 0))
  | Down _ st -> admit ()
  