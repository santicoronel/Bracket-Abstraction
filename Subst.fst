module Subst

open SKI

let rec shiftn_plus (n : nat) (t : term) (k : nat)
: Pure term true (fun t' -> k > 0 ==> not_free (n + k - 1) t') (decreases t)
= match t with
  | Var i -> if i < n then t else Var (i + k)
  | App t u -> App (shiftn_plus n t k) (shiftn_plus n u k)
  | Abs t -> Abs (shiftn_plus (n + 1) t k)
  | _ -> t

let shift_plus (t : term) (k : nat) = shiftn_plus 0 t k

let shiftn (n : nat) (t : term)
: Pure term true (fun t' -> not_free n t') (decreases t) =
  shiftn_plus n t 1

let rec shiftn_lam_lem (n : nat) (t : lam)
: Lemma (ensures is_Lam (shiftn n t)) (decreases t)
= match t with
  | Abs t -> shiftn_lam_lem (n + 1) t
  | App t u -> shiftn_lam_lem n t ; shiftn_lam_lem n u
  | _ -> ()

let rec shiftn_ski_lem (n : nat) (t : ski)
: Lemma (ensures is_SKI (shiftn n t)) (decreases t)
= match t with
  | App t u -> shiftn_ski_lem n t ; shiftn_ski_lem n u
  | _ -> ()


let shiftn_lam (n : nat) (t : lam) : lam = shiftn_lam_lem n t ; shiftn n t

let shiftn_ski (n : nat) (t : ski) : ski = shiftn_ski_lem n t ; shiftn n t

let shift = shiftn 0

let shift_lam (t : lam) : Pure lam true (fun t' -> not (free 0 t'))
= shiftn_lam 0 t

let shift_ski (t : ski) : Pure ski true (fun t' -> not (free 0 t'))
= shiftn_ski 0 t

// no estan en orden los args: sust t v n = [v / Var n] t
let rec subst (t v : term) (n : nat) : term =
  match t with
  | Var i ->
    if i < n
    then t
    else if i = n
    then v
    else Var (i - 1)
  | Abs t -> Abs (subst t (shift v) (n + 1))
  | App t u -> App (subst t v n) (subst u v n)
  | _ -> t


let rec subst_lam_lem (t : lam) (v : lam) (n : nat)
: Lemma (is_Lam (subst t v n))
= match t with
  | Abs t -> shiftn_lam_lem 0 v ; subst_lam_lem t (shift v) (n + 1)
  | App t u -> subst_lam_lem t v n ; subst_lam_lem u v n 
  | _ -> ()

let subst_lam (t v : lam) (n : nat) : lam = subst_lam_lem t v n ; subst t v n

let rec subst_ski_lem (t : ski) (v : ski) (n : nat)
: Lemma (is_SKI (subst t v n))
= match t with
  | Abs t -> shiftn_ski_lem 0 v; subst_ski_lem t (shift v) (n + 1)
  | App t u -> subst_ski_lem t v n ; subst_ski_lem u v n 
  | _ -> ()

let subst_ski (t v : ski) (n : nat) : ski = subst_ski_lem t v n ; subst t v n

let subst0 (t : lam) (v : lam) : lam = subst_lam t v 0


// esto se podria generalizar:
// requires (not_free i (subst t v n))
// ensures (not_free (i + n + 1) t /\ (free n t => not_free (i + n) v))
// o algo asi
let rec not_free_subst_ski (t v : ski ) (i : nat)
: Lemma (requires not_free i (subst_ski t v 0))
        (ensures not_free (i + 1) t /\
                 (free 0 t ==> not_free i v))
= match t with
  | App t u -> not_free_subst_ski t v i ; not_free_subst_ski u v i
  | _ -> ()


let rec nshiftn (n k : nat) (t : term)
: term
= if k = 0 then t else shiftn n (nshiftn n (k - 1) t)

let rec shift_plus_nshift (n : nat) (t : term) (k : nat)
: Lemma (ensures shiftn_plus n t k = nshiftn n k t) (decreases %[t ; k])
= match t with
  | Var j -> 
    if k = 0
    then ()
    else
      shift_plus_nshift n t (k - 1)
  | App t u ->
    if k = 0
    then (
      shift_plus_nshift n t 0 ;
      shift_plus_nshift n u 0 )
    else (
      shift_plus_nshift n (App t u) (k - 1) ;
      shift_plus_nshift n t (k - 1) ;
      shift_plus_nshift n u (k - 1) ;
      shift_plus_nshift n t k ;
      shift_plus_nshift n u k )
  | Abs t ->
    if k = 0
    then shift_plus_nshift (n + 1) t 0
    else (
      shift_plus_nshift n (Abs t) (k - 1) ;
      shift_plus_nshift (n + 1) t (k - 1) ;
      shift_plus_nshift (n + 1) t k
    )
  | _ ->
    if k = 0
    then ()
    else shift_plus_nshift n t (k - 1)

let rec subst_shiftn (t v : term) (n i : nat)
: Lemma (subst (nshiftn i (n + 1) t) v (n + i) = nshiftn i n t)
= match t with
  | Var j -> 
    shift_plus_nshift i t (n + 1) ;
    shift_plus_nshift i t n
  | App t u ->
    shift_plus_nshift i (App t u) (n + 1) ;
    shift_plus_nshift i t (n + 1) ;
    shift_plus_nshift i u (n + 1) ;
    subst_shiftn t v n i ;
    subst_shiftn u v n i ;
    shift_plus_nshift i t n ;
    shift_plus_nshift i u n ;
    shift_plus_nshift i (App t u) n
  | Abs t ->
    shift_plus_nshift i (Abs t) (n + 1) ;
    shift_plus_nshift (i + 1) t (n + 1) ;
    subst_shiftn t (shift v) n (i + 1) ;
    shift_plus_nshift (i + 1) t n ;
    shift_plus_nshift i (Abs t) n
  | _ -> shift_plus_nshift i t (n + 1) ; shift_plus_nshift i t n