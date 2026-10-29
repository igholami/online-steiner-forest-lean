import OnlineSteinerForest.UpperBound.ChargingReference

/-! Only each auxiliary middle spoke carries its unique auxiliary index. -/
namespace OnlineSteinerForest.UpperBound.Charging

variable {W J : Type*} [DecidableEq W]

theorem edgeLabel_some (right : J → W) (e : Sym2 (W ⊕ J)) (j : J)
    (h : edgeLabel right e = some j) : e = middle right j := by
  refine Sym2.ind (fun x y h => ?_) e h
  cases x with
  | inl u =>
    cases y with
    | inl v => cases h
    | inr k =>
      change (if u = right k then some k else none) = some j at h
      split_ifs at h with hu
      · have hk := Option.some.inj h
        subst k
        subst u
        exact Sym2.eq_swap
  | inr k =>
    cases y with
    | inl u =>
      change (if u = right k then some k else none) = some j at h
      split_ifs at h with hu
      · have hk := Option.some.inj h
        subst k
        subst u
        rfl
    | inr k => cases h

theorem edgeLabel_unique (right : J → W) (e f : Sym2 (W ⊕ J)) (j : J)
    (he : edgeLabel right e = some j) (hf : edgeLabel right f = some j) : e = f :=
  (edgeLabel_some right e j he).trans (edgeLabel_some right f j hf).symm

theorem timedLabel_unique (right : J → W) (time : J ↪ ℕ) (e f : Sym2 (W ⊕ J)) (i : ℕ)
    (he : (edgeLabel right e).map time = some i) (hf : (edgeLabel right f).map time = some i) : e = f := by
  cases he' : edgeLabel right e with
  | none => simp only [he', Option.map_none] at he; cases he
  | some j =>
    cases hf' : edgeLabel right f with
    | none => simp only [hf', Option.map_none] at hf; cases hf
    | some k =>
      have hj : time j = i := by simpa only [he', Option.map_some, Option.some.injEq] using he
      have hk : time k = i := by simpa only [hf', Option.map_some, Option.some.injEq] using hf
      have hjk := time.injective (hj.trans hk.symm)
      subst k
      exact edgeLabel_unique right e f j he' hf'

end OnlineSteinerForest.UpperBound.Charging
