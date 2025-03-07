module Subst

open SKI

let rec shiftn (n : nat) (t : term) : Tot term (decreases t) =
  match t with
  | Var i -> if i < n then Var i else Var (i + 1)
  | Abs a t -> Abs a (shiftn (n + 1) t)
  | App t u -> App (shiftn n t) (shiftn n u)
  | _ -> t

let rec shiftn_lam_lem (n : nat) (t : lam)
: Lemma (ensures is_Lam (shiftn n t)) (decreases t)
= match t with
  | Abs _ t -> shiftn_lam_lem (n + 1) t
  | App t u -> shiftn_lam_lem n t ; shiftn_lam_lem n u
  | _ -> ()

let rec shiftn_ski (n : nat) (t : ski)
: Lemma (ensures is_SKI (shiftn n t)) (decreases t)
= match t with
  | App t u -> shiftn_ski n t ; shiftn_ski n u
  | _ -> ()


let shiftn_lam (n : nat) (t : lam) : lam = shiftn_lam_lem n t ; shiftn n t

let shift = shiftn 0

let shift_lam (t : lam) : lam = shiftn_lam 0 t

let shift_ski (t : ski) : ski = shiftn_ski 0 t ; shift t

let rec shiftn_nclosed_lem (#n #i : nat) (t : nclosed_term n)
: Lemma (ensures nclosed (n + 1) (shiftn i t)) (decreases t) =
  match t with
  | Abs a t -> shiftn_nclosed_lem #(n + 1) #(i + 1) t
  | App t u -> shiftn_nclosed_lem #n #i t ; shiftn_nclosed_lem #n #i u
  | _ -> ()

let shift_nclosed_lam (#n : nat) (t : nclosed_lam n) : nclosed_lam (n + 1) =
  shiftn_nclosed_lem #n #0 t ; shiftn_lam 0 t

let shift_nclosed_ski (#n : nat) (t : nclosed_ski n) : nclosed_ski (n + 1) =
  shiftn_ski 0 t ; shiftn_nclosed_lem #n #0 t ; shift t

let rec subst (t v : term) (n : nat) : term =
  match t with
  | Var i ->
    if i < n
    then t
    else if i = n
    then v
    else Var (i - 1)
  | Abs a t -> Abs a (subst t (shift v) (n + 1))
  | App t u -> App (subst t v n) (subst u v n)
  | _ -> t

let rec nclosed_subst_lem (#n : nat)
                          (t : nclosed_term (n + 1)) (v : nclosed_term n)
                          (i : nat)
: Lemma (ensures nclosed (n + 1) (subst t v i) /\
                 (i <= n ==> nclosed n (subst t v i)))
        (decreases t)
= match t with
  | Abs _ t ->
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
  | Abs a t -> shiftn_lam_lem 0 v ; subst_lam_lem t (shift v) (n + 1)
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
  | Abs a t -> shiftn_ski 0 v; subst_ski_lem t (shift v) (n + 1)
  | App t u -> subst_ski_lem t v n ; subst_ski_lem u v n 
  | _ -> ()

let subst_ski (t v : ski) (n : nat) : ski = subst_ski_lem t v n ; subst t v n

let subst_nclosed_ski (#n : nat)
                      (t : nclosed_ski (n + 1)) (v : nclosed_ski n)
                      (i : nat)
: Pure ski (requires true) (ensures fun r -> nclosed (n + 1) r /\ (i <= n ==> nclosed n r))
= nclosed_subst_lem #n t v i ; subst_ski t v i 

let subst0 (t : lam) (v : lam) : lam = subst_lam t v 0
