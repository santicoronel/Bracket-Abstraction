module BracketAbstraction.Equality

open SKI
open SKI.Equality 
open BracketAbstraction
open Subst
open Lam.Equality


let rec abstract_App (t v : ski)
: ski_eq (App (abstract t) v) (subst_ski t v 0)
= match t with
  | App t u ->
    let abs_t = abstract t  in
    let abs_u = abstract u  in
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



let rec subst_ski_eq (#t #u: ski) (eq : ski_eq t u)
                     (v : ski)
: Tot (ski_eq (subst_ski t v 0) (subst_ski u v 0))
      (decreases eq)
= let sub t = subst_ski t v 0 in
  match eq with
  | Refl _ -> Refl _
  | Symm eq -> Symm (subst_ski_eq eq v)
  | Tran eq1 eq2 -> Tran (subst_ski_eq eq1 v) (subst_ski_eq eq2 v)
  | App_eq eq1 eq2 -> App_eq (subst_ski_eq eq1 v) (subst_ski_eq eq2 v)
  | Red_S f g x -> Red_S (sub f) (sub g) (sub x)
  | Red_K x y -> Red_K (sub x) (sub y)
  | Red_I x -> Red_I (sub x)
  | Zeta ext ->
    let t' = subst_ski t v 0 in
    let u' = subst_ski u v 0 in
    let ext' (i : nat {not_free i t' /\ not_free i u'})
    : ski_eq (App t' (Var i)) (App u' (Var i))
    = not_free_subst_ski t v i ;
      not_free_subst_ski u v i ;
      subst_ski_eq (ext (i + 1)) v in
    Zeta ext' 

let app2 (t u v : ski) : ski = App (App t u) v
let app3 (t u v w : ski) : ski = App (app2 t u v) w

let ( @ ) (t u : ski) : ski = App t u

let abstract_S_ski_eq (f g x y : ski)
: ski_eq (((S @ ((S @ ((S @ (K @ S)) @ f)) @ g)) @ x) @ y)
         (((S @ ((S @ f) @ x)) @ ((S @ g) @ x)) @ y)
= let red_1 = Red_S ((S  @ ((S @ (K @ S)) @ f)) @ g) x y in
  let red_2 = Red_S (App (App S (App K S)) f) g y in
  let red_2 = Red_S ((S @ (K @ S)) @ f) g y in
  let red_3 = Red_S (K @ S) f y in
  let red_4 = Red_K S y in
  let app_2 = App_eq red_2 (Refl (x @ y)) in
  let app_3_1 = App_eq red_3 (Refl (g @ y)) in
  let app_3_2 = App_eq app_3_1 (Refl (x @ y)) in
  let app_4_1 = App_eq red_4 (Refl (f @ y)) in
  let app_4_2 = App_eq app_4_1 (Refl (g @ y)) in 
  let app_4_3 = App_eq app_4_2 (Refl (x @ y)) in
  let red_5 = Red_S (f @ y) (g @ y) (x @ y) in
  let lhs = Tran (Tran (Tran (Tran red_1 app_2) app_3_2) app_4_3) red_5 in
  let red_1 = Red_S ((S @ f) @ x) ((S @ g) @ x) y in
  let redl = Red_S f x y in
  let redr = Red_S g x y in
  let rhs = Tran red_1 (App_eq redl redr) in
  Tran lhs (Symm rhs)

let abstract_K_ski_eq (x y z : ski)
: ski_eq (((S @ ((S @ (K @ K)) @ x)) @ y) @ z)
         (x @ z)
= let red_S_1 = Red_S ((S @ (K @ K)) @ x) y z in
  let red_S_2 = Red_S (K @ K) x z in
  let red_K_1 = Red_K K z in
  let red_K_2 = Red_K (x @ z) (y @ z) in
  let app_1 = App_eq red_S_2 (Refl (y @ z)) in
  let app_2 = App_eq (App_eq red_K_1 (Refl _)) (Refl _) in
  let lhs_1 = Tran red_S_1 app_1 in
  let lhs_2 = Tran lhs_1 app_2 in
  Tran lhs_2 red_K_2

let abstract_I_ski_eq (x y : ski)
: ski_eq (((S @ (K @ I)) @ x) @ y)
         (x @ y)
= let red_S = Red_S (K @ I) x y in
  let red_K = Red_K I y in
  let red_I = Red_I (x @ y) in
  let app = App_eq red_K (Refl _) in
  Tran (Tran red_S app) red_I

let rec abstract_ski_eq (#t #u : ski) (t_eq_u : ski_eq t u)
: Tot (ski_eq (abstract t) (abstract u))
      (decreases t_eq_u)
= match t_eq_u with
| Refl t -> Refl _
| Symm eq -> Symm (abstract_ski_eq eq)
| Tran eq1 eq2 -> Tran (abstract_ski_eq eq1) (abstract_ski_eq eq2)
| App_eq eq1 eq2 -> App_eq (App_eq (Refl S) (abstract_ski_eq eq1)) (abstract_ski_eq eq2)
| Zeta ext ->
  let t' = abstract t in
  let u' = abstract u in
  let ext' (i : nat)
  : ski_eq (App t' (Var i)) (App u' (Var i))
  = let t'' = subst_ski t (Var i) 0 in
    let u'' = subst_ski u (Var i) 0 in
    let abs_app_t = abstract_App t (Var i) in
    let abs_app_u = abstract_App u (Var i) in
    let ext'' (j : nat {not_free j t'' && not_free j u''})
    = not_free_subst_ski t (Var i) j ; 
      not_free_subst_ski u (Var i) j ;
      subst_ski_eq (ext (j + 1)) (Var i)
    in Tran (Tran abs_app_t (Zeta ext'')) (Symm abs_app_u)
  in Zeta ext'
| Red_S f g x ->
  let f' : ski= abstract f in
  let g' : ski= abstract g in
  let x' : ski= abstract x in
  let ext (i : nat {not_free i f' && not_free i g' && not_free i x'})
  = abstract_S_ski_eq f' g' x' (Var i)
  in Zeta ext
| Red_K x y ->
  let x' : ski = abstract x in
  let y' : ski = abstract y in
  let ext (i : nat {not_free i x' && not_free i y'})
  = abstract_K_ski_eq x' y' (Var i)
  in Zeta ext
| Red_I x ->
let x' : ski = abstract x in
let ext (i : nat {not_free i x'})
= abstract_I_ski_eq x' (Var i)
in Zeta ext




let rec shift_abs (n : nat) (t : ski)
: Lemma (shiftn n (abstract t) = abstract (shiftn_ski (n + 1) t))
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

let ski_eq_S_K (t u : ski)
: ski_eq (App (App S (App K t)) (App K u)) (App K (App t u))
= let ext (i : nat {not_free i t && not_free i u})
  = let red_S = Red_S (App K t) (App K u) (Var i) in
    let red_K_l = Red_K t (Var i) in
    let red_K_r = Red_K u (Var i) in
    let red_K_app = App_eq red_K_l red_K_r in
    let lhs = Tran red_S red_K_app in
    let red_K = Red_K (App t u) (Var i) in
    let rhs = Symm red_K in
    Tran lhs rhs
  in Zeta ext

let rec ski_eq_abstract (t : ski)
: ski_eq (abstract (shift_ski t)) (App K t)
= match t with
  | App t u ->
    let hi_t = ski_eq_abstract t in
    let hi_u = ski_eq_abstract u in
    let hi_appl = App_eq (Refl S) (hi_t) in
    let hi_app = App_eq (hi_appl) (hi_u) in
    let eq_SK = ski_eq_S_K t u in
    Tran hi_app eq_SK
  | _ -> Refl _

let rec subst_abstract (t : ski) (v : ski) (i : nat)
: ski_eq (abstract (subst_ski t (shift_ski v) (i + 1)))
         (subst_ski (abstract t) v i)
= match t with
  | App t u ->
    App_eq (App_eq (Refl S) (subst_abstract t v i)) (subst_abstract u v i)  
  | Var j ->
    if j = i + 1
    then ski_eq_abstract v
    else Refl _
  | _ -> Refl _


let rec subst_bracket (t : lam) (v : lam) (i : nat)
: Tot (ski_eq (bracket_abstraction (subst_lam t v i))
              (subst_ski (bracket_abstraction t) (bracket_abstraction v) i))
      (decreases t)
= match t with
  | Abs _ t ->
    shift_bracket 0 v ;
    let hi = subst_bracket t (shift_lam v) (i + 1) in
    let hi = abstract_ski_eq hi in 
    let bracket_t = bracket_abstraction t in
    let bracket_v = bracket_abstraction v in
    let subst_abstract_eq = subst_abstract bracket_t bracket_v i in
    Tran hi subst_abstract_eq
  | App t u -> App_eq (subst_bracket t v i) (subst_bracket u v i)
  | _ -> Refl _


let rec step_preserves_eq (#t #u : lam) (st : step t u)
: ski_eq (bracket_abstraction t) (bracket_abstraction u) =
  match st with
  | AppL st_t u -> 
    App_eq (step_preserves_eq st_t) (Refl (bracket_abstraction u))
  | AppR t st_u ->
    App_eq (Refl (bracket_abstraction t)) (step_preserves_eq st_u)
  | Beta _ t u ->
    let bracket_t = bracket_abstraction t in
    let bracket_u = bracket_abstraction u in
    Tran (abstract_App bracket_t bracket_u) (Symm (subst_bracket t u 0))
  | Down _ st -> abstract_ski_eq (step_preserves_eq st)
  