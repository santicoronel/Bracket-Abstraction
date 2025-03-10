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
    let red_s = SStep (Red_S abs_t abs_u v) in
    let hi_t = abstract_App t v in
    let hi_u = abstract_App u v in
    let app_eq = ski_app_eq hi_t hi_u in
    STran red_s app_eq
  | Var 0 -> SStep (Red_I v)
  | Var j -> SStep (Red_K (Var (j - 1)) v)
  | S -> SStep (Red_K S v)
  | K -> SStep (Red_K K v)
  | I -> SStep (Red_K I v)
  | Unit -> SStep (Red_K Unit v)


let subst_ski_step_eq (#t #u: ski) (st : ski_step t u)
                      (v : ski)
: Tot (ski_eq (subst_ski t v 0) (subst_ski u v 0))
      (decreases st)
= let sub t = subst_ski t v 0 in
  match st with
  | Red_S f g x -> SStep (Red_S (sub f) (sub g) (sub x))
  | Red_K x y -> SStep (Red_K (sub x) (sub y))
  | Red_I x -> SStep (Red_I (sub x))

let rec subst_ski_eq (#t #u: ski) (eq : ski_eq t u)
                     (v : ski)
: Tot (ski_eq (subst_ski t v 0) (subst_ski u v 0))
      (decreases eq)
= let sub t = subst_ski t v 0 in
  match eq with
  | SRefl _ -> SRefl _
  | SSymm eq -> SSymm (subst_ski_eq eq v)
  | STran eq1 eq2 -> STran (subst_ski_eq eq1 v) (subst_ski_eq eq2 v)
  // | ski_app_eq eq1 eq2 -> ski_app_eq (subst_ski_eq eq1 v) (subst_ski_eq eq2 v)
  | SAppL eq u -> SAppL (subst_ski_eq eq v) (subst_ski u v 0)
  | SAppR t eq -> SAppR (subst_ski t v 0) (subst_ski_eq eq v)
  | Zeta ext ->
    let t' = subst_ski t v 0 in
    let u' = subst_ski u v 0 in
    let ext' (i : nat {not_free i t' /\ not_free i u'})
    : ski_eq (App t' (Var i)) (App u' (Var i))
    = not_free_subst_ski t v i ;
      not_free_subst_ski u v i ;
      subst_ski_eq (ext (i + 1)) v in
    Zeta ext'
  | SStep st -> subst_ski_step_eq st v

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
  let app_2 = SAppL (SStep red_2) (x @ y) in
  let app_3_1 = SAppL (SStep red_3) (g @ y) in
  let app_3_2 = SAppL app_3_1 (x @ y) in
  let app_4_1 = SAppL (SStep red_4) (f @ y) in
  let app_4_2 = SAppL app_4_1 (g @ y) in 
  let app_4_3 = SAppL app_4_2 (x @ y) in
  let red_5 = Red_S (f @ y) (g @ y) (x @ y) in
  let lhs = STran (SStep red_1) app_2 in
  let lhs = STran lhs app_3_2 in
  let lhs = STran lhs app_4_3 in
  let lhs = STran lhs (SStep red_5) in
  let red_1 = Red_S ((S @ f) @ x) ((S @ g) @ x) y in
  let redl = Red_S f x y in
  let redr = Red_S g x y in
  let app = ski_app_eq (SStep redl) (SStep redr) in
  let rhs = STran (SStep red_1) app in
  STran lhs (SSymm rhs)

let abstract_K_ski_eq (x y z : ski)
: ski_eq (((S @ ((S @ (K @ K)) @ x)) @ y) @ z)
         (x @ z)
= let red_S_1 = Red_S ((S @ (K @ K)) @ x) y z in
  let red_S_2 = Red_S (K @ K) x z in
  let red_K_1 = Red_K K z in
  let red_K_2 = Red_K (x @ z) (y @ z) in
  let app_1 = SAppL (SStep red_S_2) (y @ z) in
  let app_2 = SAppL (SAppL (SStep red_K_1) _) _ in
  let lhs_1 = STran (SStep red_S_1) app_1 in
  let lhs_2 = STran lhs_1 app_2 in
  STran lhs_2 (SStep red_K_2)

let abstract_I_ski_eq (x y : ski)
: ski_eq (((S @ (K @ I)) @ x) @ y)
         (x @ y)
= let red_S = Red_S (K @ I) x y in
  let red_K = Red_K I y in
  let red_I = Red_I (x @ y) in
  let app = SAppL (SStep red_K) _ in
  STran (STran (SStep red_S) app) (SStep red_I)

let abstract_ski_step_eq (#t #u : ski) (st : ski_step t u)
: Tot (ski_eq (abstract t) (abstract u))
      (decreases st)
= match st with
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


let rec abstract_ski_eq (#t #u : ski) (t_eq_u : ski_eq t u)
: Tot (ski_eq (abstract t) (abstract u))
      (decreases t_eq_u)
= match t_eq_u with
| SRefl t -> SRefl _
| SSymm eq -> SSymm (abstract_ski_eq eq)
| STran eq1 eq2 -> STran (abstract_ski_eq eq1) (abstract_ski_eq eq2)
// | ski_app_eq eq1 eq2 -> ski_app_eq (ski_app_eq (SRefl S) (abstract_ski_eq eq1)) (abstract_ski_eq eq2)
| SAppL eq u -> SAppL (SAppR S (abstract_ski_eq eq)) (abstract u) 
| SAppR t eq -> SAppR (App S (abstract t)) (abstract_ski_eq eq)
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
    in STran (STran abs_app_t (Zeta ext'')) (SSymm abs_app_u)
  in Zeta ext'
| SStep st -> abstract_ski_step_eq st



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
    let red_K_app = ski_app_eq (SStep red_K_l) (SStep red_K_r) in
    let lhs = STran (SStep red_S) red_K_app in
    let red_K = Red_K (App t u) (Var i) in
    let rhs = SSymm (SStep red_K) in
    STran lhs rhs
  in Zeta ext

let rec ski_eq_abstract (t : ski)
: ski_eq (abstract (shift_ski t)) (App K t)
= match t with
  | App t u ->
    let hi_t = ski_eq_abstract t in
    let hi_u = ski_eq_abstract u in
    let hi_appl = SAppR S hi_t in
    let hi_app = ski_app_eq hi_appl hi_u in
    let eq_SK = ski_eq_S_K t u in
    STran hi_app eq_SK
  | _ -> SRefl _

let rec subst_abstract (t : ski) (v : ski) (i : nat)
: ski_eq (abstract (subst_ski t (shift_ski v) (i + 1)))
         (subst_ski (abstract t) v i)
= match t with
  | App t u ->
    ski_app_eq (SAppR S (subst_abstract t v i)) (subst_abstract u v i)  
  | Var j ->
    if j = i + 1
    then ski_eq_abstract v
    else SRefl _
  | _ -> SRefl _


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
    STran hi subst_abstract_eq
  | App t u -> ski_app_eq (subst_bracket t v i) (subst_bracket u v i)
  | _ -> SRefl _


let rec step_preserves_eq (#t #u : lam) (st : step t u)
: ski_eq (bracket_abstraction t) (bracket_abstraction u) =
  match st with
  | AppL st_t u -> 
    SAppL (step_preserves_eq st_t) (bracket_abstraction u)
  | AppR t st_u ->
    SAppR (bracket_abstraction t) (step_preserves_eq st_u)
  | Beta _ t u ->
    let bracket_t = bracket_abstraction t in
    let bracket_u = bracket_abstraction u in
    STran (abstract_App bracket_t bracket_u) (SSymm (subst_bracket t u 0))
  | Down _ st -> abstract_ski_eq (step_preserves_eq st)
  