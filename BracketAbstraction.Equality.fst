module BracketAbstraction.Equality

open SKI
open SKI.Equality 
open BracketAbstraction
open Subst

// abstraer y despues aplicar es equivalente a sustituir
// i.e. `abstract` se comporta como esperamos
let rec abstract_App (t v : ski)
: ski_eq (App (abstract t) v) (subst_ski t v 0)
= match t with
  | App t u ->
    let abs_t = abstract t  in
    let abs_u = abstract u  in
    let red_s = RedS abs_t abs_u v in
    let hi_t = abstract_App t v in
    let hi_u = abstract_App u v in
    let app_eq = app_eq_ski hi_t hi_u in
    Eq_S (Tran red_s app_eq)
  | Var 0 -> RedI v
  | Var j -> RedK (Var (j - 1)) v
  | S -> RedK S v
  | K -> RedK K v
  | I -> RedK I v

// sustitución preserva igualdad
let rec subst_ski_eq (#t #u: ski) (r : ski_eq t u)
                     (v : ski)
: Tot (ski_eq (subst_ski t v 0) (subst_ski u v 0))
      (decreases r)
= let sub t = subst_ski t v 0 in
  match r with
  | Eq_S (Refl _) -> Eq_S (Refl _)
  | Eq_S (Symm r) -> Eq_S (Symm (subst_ski_eq r v))
  | Eq_S (Tran eq1 eq2) -> Eq_S (Tran (subst_ski_eq eq1 v) (subst_ski_eq eq2 v))
  | Eq_S (AppL r u) -> Eq_S (AppL (subst_ski_eq r v) (subst_ski u v 0))
  | Eq_S (AppR t r) -> Eq_S (AppR (subst_ski t v 0) (subst_ski_eq r v))
  | RedS f g x -> RedS (sub f) (sub g) (sub x)
  | RedK x y -> RedK (sub x) (sub y)
  | RedI x -> RedI (sub x)
  | Zeta ext ->
    let t' = subst_ski t v 0 in
    let u' = subst_ski u v 0 in
    let ext' (i : nat {not_free i t' /\ not_free i u'})
    : ski_eq (App t' (Var i)) (App u' (Var i))
    = not_free_subst_ski t v i ;
      not_free_subst_ski u v i ;
      subst_ski_eq (ext (i + 1)) v in
    Zeta ext'


let ( @ ) (t u : ski) : ski = App t u

// casos particulares de `abstract_ski_eq`

let abstract_S_ski_eq (f g x y : ski)
: ski_eq (((S @ ((S @ ((S @ (K @ S)) @ f)) @ g)) @ x) @ y)
         (((S @ ((S @ f) @ x)) @ ((S @ g) @ x)) @ y)
= let k : ski = ((S @ ((S @ (K @ S)) @ f)) @ g) in
  let red_1 = RedS k x y in
  let red_2 = RedS (App (App S (App K S)) f) g y in
  let red_2 = RedS ((S @ (K @ S)) @ f) g y in
  let red_3 = RedS (K @ S) f y in
  let red_4 = RedK S y in
  let app_2 = Eq_S (AppL red_2 (x @ y)) in
  let app_3_1 = Eq_S (AppL red_3 (g @ y)) in
  let app_3_2 = Eq_S (AppL app_3_1 (x @ y)) in
  let app_4_1 = Eq_S (AppL red_4 (f @ y)) in
  let app_4_2 = Eq_S (AppL app_4_1 (g @ y)) in 
  let app_4_3 = Eq_S (AppL app_4_2 (x @ y)) in
  let red_5 = RedS (f @ y) (g @ y) (x @ y) in
  let lhs = Eq_S (Tran red_1 app_2) in
  let lhs = Eq_S (Tran lhs app_3_2) in
  let lhs = Eq_S (Tran lhs app_4_3) in
  let lhs = Eq_S (Tran lhs red_5) in
  let red_1 = RedS ((S @ f) @ x) ((S @ g) @ x) y in
  let redl = RedS f x y in
  let redr = RedS g x y in
  let app = app_eq_ski redl redr in
  let rhs = Eq_S (Tran red_1 app) in
  Eq_S (Tran lhs (Eq_S (Symm rhs)))

let abstract_K_ski_eq (x y z : ski)
: ski_eq (((S @ ((S @ (K @ K)) @ x)) @ y) @ z)
         (x @ z)
= let red_S_1 = RedS ((S @ (K @ K)) @ x) y z in
  let red_S_2 = RedS (K @ K) x z in
  let red_K_1 = RedK K z in
  let red_K_2 = RedK (x @ z) (y @ z) in
  let app_1 = Eq_S (AppL red_S_2 (y @ z)) in
  let app_2 = Eq_S (AppL (Eq_S (AppL red_K_1 _)) _) in
  let lhs_1 = Eq_S (Tran red_S_1 app_1) in
  let lhs_2 = Eq_S (Tran lhs_1 app_2) in
  Eq_S (Tran lhs_2 red_K_2)

let abstract_I_ski_eq (x y : ski)
: ski_eq (((S @ (K @ I)) @ x) @ y)
         (x @ y)
= let red_S = RedS (K @ I) x y in
  let red_K = RedK I y in
  let red_I = RedI (x @ y) in
  let app = Eq_S (AppL red_K _) in
  Eq_S (Tran (Eq_S (Tran red_S app)) red_I)


// t = u ==> abs(t) = abs(u)
let rec abstract_ski_eq (#t #u : ski) (t_eq_u : ski_eq t u)
: Tot (ski_eq (abstract t) (abstract u))
      (decreases t_eq_u)
= match t_eq_u with
| Eq_S (Refl t) -> Eq_S (Refl _)
| Eq_S (Symm r) -> Eq_S (Symm (abstract_ski_eq r))
| Eq_S (Tran eq1 eq2) -> Eq_S (Tran (abstract_ski_eq eq1) (abstract_ski_eq eq2))
| Eq_S (AppL r u) -> Eq_S (AppL (Eq_S (AppR S (abstract_ski_eq r))) (abstract u)) 
| Eq_S (AppR t r) -> Eq_S (AppR (App S (abstract t)) (abstract_ski_eq r))
| RedS f g x ->
  let f' : ski= abstract f in
  let g' : ski= abstract g in
  let x' : ski= abstract x in
  let ext (i : nat {not_free i f' && not_free i g' && not_free i x'})
  = abstract_S_ski_eq f' g' x' (Var i)
  in Zeta ext
| RedK x y ->
  let x' : ski = abstract x in
  let y' : ski = abstract y in
  let ext (i : nat {not_free i x' && not_free i y'})
  = abstract_K_ski_eq x' y' (Var i)
  in Zeta ext
| RedI x ->
  let x' : ski = abstract x in
  let ext (i : nat {not_free i x'})
  = abstract_I_ski_eq x' (Var i)
  in Zeta ext
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
    in Eq_S (Tran (Eq_S (Tran abs_app_t (Zeta ext''))) (Eq_S (Symm abs_app_u)))
  in Zeta ext'


// shift conmuta con abs()
let rec shift_abs (n : nat) (t : ski)
: Lemma (shiftn n (abstract t) = abstract (shiftn_ski (n + 1) t))
= match t with
  | App t u -> shift_abs n t ; shift_abs n u 
  | _ -> ()

// shift conmuta con [| - |]
let rec shift_bracket (i : nat) (t : lam)
: Lemma (ensures shiftn i (bracket_abstraction t) = bracket_abstraction (shiftn_lam i t))
        (decreases t)
= match t with
  | Abs t ->
    shift_abs i (bracket_abstraction t) ;
    shift_bracket (i + 1) t
  | App t u -> shift_bracket i t ; shift_bracket i u
  | _ -> ()

let ski_eq_S_K (t u : ski)
: ski_eq (App (App S (App K t)) (App K u)) (App K (App t u))
= let ext (i : nat {not_free i t && not_free i u})
  = let red_S = RedS (App K t) (App K u) (Var i) in
    let red_K_l = RedK t (Var i) in
    let red_K_r = RedK u (Var i) in
    let red_K_app = app_eq_ski red_K_l red_K_r in
    let lhs = Eq_S (Tran red_S red_K_app) in
    let red_K = RedK (App t u) (Var i) in
    let rhs = Eq_S (Symm red_K) in
    Eq_S (Tran lhs rhs)
  in Zeta ext

let rec ski_eq_abstract (t : ski)
: ski_eq (abstract (shift_ski t)) (App K t)
= match t with
  | App t u ->
    let hi_t = ski_eq_abstract t in
    let hi_u = ski_eq_abstract u in
    let hi_appl = Eq_S (AppR S hi_t) in
    let hi_app = app_eq_ski hi_appl hi_u in
    let eq_SK = ski_eq_S_K t u in
    Eq_S (Tran hi_app eq_SK)
  | _ -> Eq_S (Refl _)

// sustitucion conmuta con abs()
let rec subst_abstract (t : ski) (v : ski) (i : nat)
: ski_eq (abstract (subst_ski t (shift_ski v) (i + 1)))
         (subst_ski (abstract t) v i)
= match t with
  | App t u ->
    app_eq_ski (Eq_S (AppR S (subst_abstract t v i))) (subst_abstract u v i)  
  | Var j ->
    if j = i + 1
    then ski_eq_abstract v
    else Eq_S (Refl _)
  | _ -> Eq_S (Refl _)

// sustitucion conmuta con [| - |]
let rec subst_bracket (t : lam) (v : lam) (i : nat)
: Tot (ski_eq (bracket_abstraction (subst_lam t v i))
              (subst_ski (bracket_abstraction t) (bracket_abstraction v) i))
      (decreases t)
= match t with
  | Abs t ->
    shift_bracket 0 v ;
    let hi = subst_bracket t (shift_lam v) (i + 1) in
    let hi = abstract_ski_eq hi in 
    let bracket_t = bracket_abstraction t in
    let bracket_v = bracket_abstraction v in
    let subst_abstract_eq = subst_abstract bracket_t bracket_v i in
    Eq_S (Tran hi subst_abstract_eq)
  | App t u -> app_eq_ski (subst_bracket t v i) (subst_bracket u v i)
  | _ -> Eq_S (Refl _)

// t = u ==> [| t |] = [| u |]
let rec bracket_preserves_eq (#t #u : lam) (r : lam_eq t u)
: Tot (ski_eq (bracket_abstraction t) (bracket_abstraction u)) (decreases r) =
  match r with
  | Eq_L (Refl _) -> Eq_S (Refl _)
  | Eq_L (Symm r) -> Eq_S (Symm (bracket_preserves_eq r))
  | Eq_L (Tran r1 r2) -> Eq_S (Tran (bracket_preserves_eq r1) (bracket_preserves_eq r2))
  | Eq_L (AppL r u) -> 
    Eq_S (AppL (bracket_preserves_eq r) (bracket_abstraction u))
  | Eq_L (AppR t r) ->
    Eq_S (AppR (bracket_abstraction t) (bracket_preserves_eq r))
  | Beta t u ->
    let bracket_t = bracket_abstraction t in
    let bracket_u = bracket_abstraction u in
    Eq_S (Tran (abstract_App bracket_t bracket_u) (Eq_S (Symm (subst_bracket t u 0))))
  | Down r -> abstract_ski_eq (bracket_preserves_eq r)