module TrLam.Equality

open SKI
open TrLam
open SKI.Equality



let rec trlam_preserves_eq (#t #u : ski) (r : ski_eq t u)
: Tot (lam_eq (trlam t) (trlam u)) (decreases r)
= match r with
  | Eq_S (Refl _) -> Eq_L (Refl _)
  | Eq_S (Symm r) -> Eq_L (Symm (trlam_preserves_eq r))
  | Eq_S (Tran r1 r2) ->
    Eq_L (Tran (trlam_preserves_eq r1)
               (trlam_preserves_eq r2))
  | RedI x -> admit ()
  | _ -> admit ()