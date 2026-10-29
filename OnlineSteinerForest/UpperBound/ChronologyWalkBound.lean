import OnlineSteinerForest.UpperBound.GirthResidualDistance

/-! The metric argument behind charging-cycle chronology, including copied vertices. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

variable {W X : Type*} {H : SimpleGraph W}

/-- Stepwise distance certificates sum along any mathlib walk. -/
theorem distance_le_walk_sum (d : X → X → ENNReal) (f : W → X)
    (hrefl : ∀ x, d x x = 0) (htriangle : ∀ x y z, d x z ≤ d x y + d y z)
    (length : Sym2 W → ENNReal) {u v : W} (p : H.Walk u v)
    (hstep : ∀ {a b}, H.Adj a b → s(a, b) ∈ p.edges → d (f a) (f b) ≤ length s(a, b)) :
    d (f u) (f v) ≤ (p.edges.map length).sum := by
  induction p with
  | nil => simp [hrefl]
  | @cons u v w huv p ih =>
    have htail := ih (fun hab he => hstep hab (by simp [SimpleGraph.Walk.edges_cons, he]))
    calc
      _ ≤ d (f u) (f v) + d (f v) (f w) := htriangle _ _ _
      _ ≤ length s(u, v) + (p.edges.map length).sum :=
        add_le_add (hstep huv (by simp)) htail
      _ = _ := by simp

/-- Removing the latest zero-cost auxiliary edge leaves a walk whose distance
certificates pay for that edge's pre-purchase separation. -/
theorem latest_auxiliary_closed_walk_bound (d : X → X → ENNReal) (f : W → X)
    (hrefl : ∀ x, d x x = 0) (hsymm : ∀ x y, d x y = d y x)
    (htriangle : ∀ x y z, d x z ≤ d x y + d y z)
    (length : Sym2 W → ENNReal) (label : Sym2 W → Option ℕ)
    {u v : W} (huv : H.Adj u v) (p : H.Walk v u) (i : ℕ) (sep : ENNReal)
    (hselected : label s(u, v) = some i) (hsep : sep ≤ d (f u) (f v))
    (hzero : ∀ e j, label e = some j → length e = 0)
    (hmax : ∀ e ∈ p.edges, ∀ j, label e = some j → j < i)
    (href : ∀ {a b}, H.Adj a b → s(a, b) ∈ p.edges → label s(a, b) = none →
      d (f a) (f b) ≤ length s(a, b))
    (hearlier : ∀ {a b}, H.Adj a b → s(a, b) ∈ p.edges → ∀ j,
      label s(a, b) = some j → j < i → d (f a) (f b) = 0) :
    sep ≤ ((SimpleGraph.Walk.cons huv p).edges.map length).sum := by
  have hstep : ∀ {a b}, H.Adj a b → s(a, b) ∈ p.edges →
      d (f a) (f b) ≤ length s(a, b) := by
    intro a b hab he
    cases hl : label s(a, b) with
    | none => exact href hab he hl
    | some j =>
      rw [hearlier hab he j hl (hmax _ he j hl)]
      exact bot_le
  calc
    sep ≤ d (f u) (f v) := hsep
    _ = d (f v) (f u) := hsymm _ _
    _ ≤ (p.edges.map length).sum := distance_le_walk_sum d f hrefl htriangle length p hstep
    _ = _ := by simp [hzero _ _ hselected]

end OnlineSteinerForest.UpperBound
