module TrLam.Equality

open SKI
open TrLam
open SKI.Equality
open Subst


let rec _abstractxn (n : nat) (x : nat) (t : lam)
: Tot lam (decreases t)
= match t with
  | Var i ->
    if i < n
    then t
    else if i = x + n
    then Var n
    else Var (i + 1)
  | App t u -> App (_abstractxn n x t) (_abstractxn n x u)
  | Abs t -> Abs (_abstractxn (n + 1) x t)
  | _ -> t

let _abstractx = _abstractxn 0

let abstractxn (n : nat) (x : nat) (t : lam) : lam = Abs (_abstractxn n x t)

let abstractx (x : nat) (t : lam) = abstractxn 0 x t

let rec subst_abstractxn (n : nat) (t v : lam) (x : nat)
: Lemma (requires not_free (x + n) t) (ensures subst (_abstractxn n x t) v n = t)
        (decreases t)
= match t with
  | Var i -> ()
  | App t u -> subst_abstractxn n t v x ; subst_abstractxn n u v x
  | Abs t -> subst_abstractxn (n + 1) t (shift_lam v) x 
  | _ -> ()

let rec shiftn_abstractxn (n i x : nat) (t : lam)
: Lemma (ensures shiftn_lam i (_abstractxn (n + i) x t) =
                _abstractxn (n + i + 1) x (shiftn_lam i t))
        (decreases t)
= match t with
  | Var j -> ()
  | App t u -> shiftn_abstractxn n i x t ; shiftn_abstractxn n i x u
  | Abs t -> shiftn_abstractxn n (i + 1) x t 
  | _ -> ()

let rec abstractxn_subst (n k : nat) (x : nat) (t v : lam)
: Lemma (ensures _abstractxn (n + k) x (subst_lam t v k) =
                  subst_lam (_abstractxn (n + k + 1) x t) (_abstractxn (n + k) x v) k)
        (decreases t)
= match t with
  | Var i -> ()
  | App t u -> abstractxn_subst n k x t v ; abstractxn_subst n k x u v 
  | Abs t -> 
    shiftn_abstractxn (n + k) 0 x v ;
    abstractxn_subst n (k + 1) x t (shift_lam v)
  | _ -> ()

let rec eq__abstractxn (n : nat) (x : nat) (#t #u : lam) (r : lam_eq t u)
: Tot (lam_eq (_abstractxn n x t) (_abstractxn n x u)) (decreases r)
= match r with
  | Eq_L (Refl _) -> Eq_L (Refl _)
  | Eq_L (Symm r) -> Eq_L (Symm (eq__abstractxn n x r))
  | Eq_L (Tran r1 r2) -> Eq_L (Tran (eq__abstractxn n x r1) (eq__abstractxn n x r2))
  | Eq_L (AppL r u) -> Eq_L (AppL (eq__abstractxn n x r) (_abstractxn n x u))
  | Eq_L (AppR t r) -> Eq_L (AppR (_abstractxn n x t) (eq__abstractxn n x r))
  | Beta t u ->
    abstractxn_subst n 0 x t u ;
    Beta (_abstractxn (n + 1) x t) (_abstractxn n x u)
  | Down r -> Down (eq__abstractxn (n + 1) x r)

let eq_abstractx (x: nat) (#t #u: lam) (r: lam_eq t u) = Down (eq__abstractxn 0 x r)


let rec _abstractxn_not_free (n x : nat) (t : lam)
: Lemma (requires not_free (x + n) t) (ensures _abstractxn n x t = shiftn n t)
        (decreases t)
= match t with
  | App t u -> _abstractxn_not_free n x t ; _abstractxn_not_free n x u 
  | Abs t -> _abstractxn_not_free (n + 1) x t
  | _ -> ()


let abstractx_S_f_g (f g x : lam)
: lam_eq (App (App (App (trlam S) f) g) x) (App (App f x) (App g x))
= let beta_1 = Beta (Abs (Abs (App (App (Var 2) (Var 0)) (App (Var 1) (Var 0))))) f in
  let app_1_1 = Eq_L (AppL beta_1 g) in
  let app_1 = Eq_L (AppL app_1_1 x) in
  let sf = shift_lam f in
  let sg = shift_lam g in
  let ssf = shift_lam sf in
  subst_shiftn f sg 1 0 ;
  let beta_2 = Beta (Abs (App (App ssf (Var 0)) (App (Var 1) (Var 0)))) g in
  let app_2 = Eq_L (AppL beta_2 x) in
  subst_shiftn f x 0 0 ;
  subst_shiftn g x 0 0 ;
  let beta_3 = Beta (App (App sf (Var 0)) (App sg (Var 0))) x in
  let tran = Eq_L (Tran app_1 app_2) in
  Eq_L (Tran tran beta_3)


let abstractx_fnl (x : nat) (t : ski)
: Pure (lam_eq (abstractx x (App (trlam t) (Var x))) (trlam t))
       (fnl t /\ not_free x t)
       (fun _ -> true)
= match t with
  | S -> Down (Beta (Abs (Abs (App (App (Var 2) (Var 0)) (App (Var 1) (Var 0))))) (Var 0))
  | App S f ->
    let f' = trlam f in
    let sf = shift_lam f' in
    not_free_trlam x f ;
    _abstractxn_not_free 0 x f' ;
    let beta_1 = Beta (Abs (Abs (App (App (Var 2) (Var 0)) (App (Var 1) (Var 0))))) sf in
    let app_1 = Eq_L (AppL beta_1 (Var 0)) in
    let down_1 = Down app_1 in
    let s3f = shift_lam (shift_lam sf) in
    subst_shiftn sf (Var 1) 1 0 ;
    let beta_2 = Beta (Abs (App (App s3f (Var 0)) (App (Var 1) (Var 0)))) (Var 0) in
    let down_2 = Down beta_2 in
    let lhs = Eq_L (Tran down_1 down_2) in
    let beta = Beta (Abs (Abs (App (App (Var 2) (Var 0)) (App (Var 1) (Var 0))))) (trlam f) in
    let rhs = Eq_L (Symm beta) in
    Eq_L (Tran lhs rhs)
  | App (App S f) g ->
    let f' = trlam f in
    let g' = trlam g in
    not_free_trlam x f ;
    not_free_trlam x g ;
    _abstractxn_not_free 0 x f' ;
    _abstractxn_not_free 0 x g' ;
    let sf = shift_lam f' in
    let sg = shift_lam g' in
    let ssf = shift_lam sf in
    let lhs = Down (abstractx_S_f_g sf sg (Var 0)) in
    let beta_1 = Beta (Abs (Abs (App (App (Var 2) (Var 0)) (App (Var 1) (Var 0))))) f' in
    let app_1 = Eq_L (AppL beta_1 g') in
    subst_shiftn f' sg 1 0 ;
    let beta_2 = Beta (Abs (App (App ssf (Var 0)) (App (Var 1) (Var 0)))) g' in
    let tran = Eq_L (Tran app_1 beta_2) in
    let rhs = Eq_L (Symm tran) in
    assert (_abstractx x (trlam S) = trlam S) ;
    assert (_abstractx x (trlam f) = sf) ;
    assert (_abstractx x (trlam g) = sg) ;
    assert (_abstractx x (Var x) = Var 0) ;
    assert (_abstractx x (trlam t) = App (App (trlam S) sf) sg) ;
    assert (_abstractx x (App (trlam t) (Var x)) = App (App (App (trlam S) sf) sg) (Var 0)) ;
    assert (abstractx x (App (trlam t) (Var x)) = Abs (App (App (App (trlam S) sf) sg) (Var 0))) ;
    Eq_L (Tran lhs rhs)
| K -> Down (Beta (Abs (Var 1)) (Var 0))
| App K t ->
  let t' = trlam t in
  let st = shift_lam t' in
  not_free_trlam x t ;
  _abstractxn_not_free 0 x t' ; 
  let beta_1 = Beta (Abs (Var 1)) st in
  let app_1 = Eq_L (AppL beta_1 (Var 0)) in
  let down_1 = Down app_1 in
  let sst = shift_lam st in
  subst_shiftn st (Var 0) 0 0 ;
  let beta_2 = Beta sst (Var 0) in
  let down_2 = Down beta_2 in
  let lhs = Eq_L (Tran down_1 down_2) in
  let beta = Beta (Abs (Var 1)) t' in
  let rhs = Eq_L (Symm beta) in
  Eq_L (Tran lhs rhs)
| I -> Down (Beta (Var 0) (Var 0))

let rec trlam_preserves_eq (#t #u : ski) (r : ski_eq t u)
: Tot (lam_eq (trlam t) (trlam u)) (decreases r)
= match r with
  | Eq_S (Refl _) -> Eq_L (Refl _)
  | Eq_S (Symm r) -> Eq_L (Symm (trlam_preserves_eq r))
  | Eq_S (Tran r1 r2) ->
    Eq_L (Tran (trlam_preserves_eq r1) (trlam_preserves_eq r2))
  | Eq_S (AppL r u) -> Eq_L (AppL (trlam_preserves_eq r) (trlam u))
  | Eq_S (AppR t r) -> Eq_L (AppR (trlam t) (trlam_preserves_eq r))
  | RedS f g x ->
    let f' = trlam f in
    let g' = trlam g in
    let x' = trlam x in
    let beta_1 = Beta (Abs (Abs (App (App (Var 2) (Var 0)) (App (Var 1) (Var 0))))) f'
    in let sf = shift_lam f'
    in let ssf = shift_lam sf
    in let beta_2 =  Beta (Abs (App (App ssf (Var 0)) (App (Var 1) (Var 0)))) g'
    in let sg = shift_lam g'
    in let beta_3 = Beta (App (App sf (Var 0)) (App sg (Var 0))) x'
    in let app_1_1 = Eq_L (AppL beta_1 g')
    in let app_1 = Eq_L (AppL app_1_1 x')
    in let app_2 = Eq_L (AppL beta_2 x')
    in let tran = Eq_L (Tran app_1 app_2)
    in 
    subst_shiftn f' sg 1 0;
    subst_shiftn f' x' 0 0;
    subst_shiftn g' x' 0 0;
    Eq_L (Tran tran beta_3)
  | RedK x y ->
    let beta_1 = Beta (Abs (Var 1)) (trlam x) in
    let beta_2 = Beta (shift_lam (trlam x)) (trlam y) in
    let app = Eq_L (AppL beta_1 (trlam y)) in
    subst_shiftn (trlam x) (trlam y) 0 0 ;
    Eq_L (Tran app beta_2)
  | RedI x -> Beta (Var 0) (trlam x)
  | Zeta ext ->
    let x = fresh_for_all [ t ; u] in
    let hi = trlam_preserves_eq (ext x) in
    let abs_hi = eq_abstractx x hi in
    let abs_1 = abstractx_fnl x t in
    let abs_2 = abstractx_fnl x u in
    Eq_L (Tran (Eq_L (Symm abs_1)) (Eq_L (Tran abs_hi abs_2)))