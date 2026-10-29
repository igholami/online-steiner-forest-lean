import OnlineSteinerForest.UpperBound.GirthTrace

/-! Injectivity of the standard simple-graph encoding of labelled dart paths. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*} [Fintype I] [DecidableEq I] [DecidableEq V]

theorem subdividedWalk_support (left right : I → V) (n : ℕ) (p : Paths (Dart I) n)
    (hp : Nonbacktracking left right n p) :
    (subdividedWalk left right n p hp).support =
      .inl (tail left right (first n p)) :: nodeTrace left right n p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((subdividedWalk left right n p.1 hp.1).append
      ((dartWalk left right p.2).copy _ _)).support = _
    rw [SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_copy, ih, dartWalk_support]
    rfl

theorem subdividedWalk_support_injective (left right : I → V) (n : ℕ)
    (p q : Paths (Dart I) n) (hp : Nonbacktracking left right n p)
    (hq : Nonbacktracking left right n q)
    (heq : (subdividedWalk left right n p hp).support =
      (subdividedWalk left right n q hq).support) : p = q := by
  apply nodeTrace_injective left right n
  have hh := congrArg List.tail heq
  simpa only [subdividedWalk_support, List.tail_cons] using hh

end OnlineSteinerForest.UpperBound.Girth
