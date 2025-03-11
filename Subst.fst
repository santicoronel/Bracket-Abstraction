module Subst

open SKI

let rec shiftn (n : nat) (t : term)
: Pure term true (fun t' -> not (free n t')) (decreases t) =
  match t with
  | Var i -> if i < n then Var i else Var (i + 1)
  | Abs t -> Abs (shiftn (n + 1) t)
  | App t u -> App (shiftn n t) (shiftn n u)
  | _ -> t

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

let rec shiftn_nclosed_lem (#n #i : nat) (t : nclosed_term n)
: Lemma (ensures nclosed (n + 1) (shiftn i t)) (decreases t) =
  match t with
  | Abs t -> shiftn_nclosed_lem #(n + 1) #(i + 1) t
  | App t u -> shiftn_nclosed_lem #n #i t ; shiftn_nclosed_lem #n #i u
  | _ -> ()

let shift_nclosed_lam (#n : nat) (t : nclosed_lam n) : nclosed_lam (n + 1) =
  shiftn_nclosed_lem #n #0 t ; shiftn_lam 0 t

let shift_nclosed_ski (#n : nat) (t : nclosed_ski n) : nclosed_ski (n + 1) =
  shiftn_ski_lem 0 t ; shiftn_nclosed_lem #n #0 t ; shift t

// estan al reves los args xdd
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

let rec nclosed_subst_lem (#n : nat)
                          (t : nclosed_term (n + 1)) (v : nclosed_term n)
                          (i : nat)
: Lemma (ensures nclosed (n + 1) (subst t v i) /\
                 (i <= n ==> nclosed n (subst t v i)))
        (decreases t)
= match t with
  | Abs t ->
    shiftn_nclosed_lem #n #0 v ;
    nclosed_subst_lem #(n + 1) t (shift v) (i + 1)
  | App t u ->
    nclosed_subst_lem t v i ;
    nclosed_subst_lem u v i
  | Var j -> if j = i then extend_lem #n #1 v else () 
  | _ -> ()

let rec subst_lam_lem (t : lam) (v : lam) (n : nat)
: Lemma (is_Lam (subst t v n))
= match t with
  | Abs t -> shiftn_lam_lem 0 v ; subst_lam_lem t (shift v) (n + 1)
  | App t u -> subst_lam_lem t v n ; subst_lam_lem u v n 
  | _ -> ()

let subst_lam (t v : lam) (n : nat) : lam = subst_lam_lem t v n ; subst t v n

let subst_nclosed_lam (#n : nat)
                      (t : nclosed_lam (n + 1)) (v : nclosed_lam n)
                      (i : nat)
: Pure lam (requires true) (ensures fun r -> nclosed (n + 1) r /\ (i <= n ==> nclosed n r))
= nclosed_subst_lem #n t v i ; subst_lam t v i 

let rec subst_ski_lem (t : ski) (v : ski) (n : nat)
: Lemma (is_SKI (subst t v n))
= match t with
  | Abs t -> shiftn_ski_lem 0 v; subst_ski_lem t (shift v) (n + 1)
  | App t u -> subst_ski_lem t v n ; subst_ski_lem u v n 
  | _ -> ()

let subst_ski (t v : ski) (n : nat) : ski = subst_ski_lem t v n ; subst t v n

let subst_nclosed_ski (#n : nat)
                      (t : nclosed_ski (n + 1)) (v : nclosed_ski n)
                      (i : nat)
: Pure ski (requires true) (ensures fun r -> nclosed (n + 1) r /\ (i <= n ==> nclosed n r))
= nclosed_subst_lem #n t v i ; subst_ski t v i 

let subst0 (t : lam) (v : lam) : lam = subst_lam t v 0

let rec subst_free (t v : term) (i : nat)
: Lemma (requires not_free i t) (ensures shiftn i (subst t v i) = t)
= match t with
  | Abs t -> subst_free t (shift v) (i + 1)
  | App t u -> subst_free t v i ; subst_free u v i
  | _ -> ()


let subst0_free (t v : term)
: Lemma (requires not_free 0 t) (ensures shift (subst t v 0) = t)
= subst_free t v 0

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