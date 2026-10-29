import OnlineSteinerForest.UpperBound.ChronologyCyclePath
import OnlineSteinerForest.UpperBound.ChronologyMaximum
import OnlineSteinerForest.UpperBound.ChronologyWalkBound

/-! The latest auxiliary edge forces every charging cycle to have large reference cost. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

variable {W X : Type*} {H : SimpleGraph W}

theorem cycle_separation_le_cost (label : Sym2 W → Option ℕ)
    (hforest : (H.deleteEdges {e | label e ≠ none}).IsAcyclic)
    (hunique : ∀ e f i, label e = some i → label f = some i → e = f)
    (d : ℕ → X → X → ENNReal) (project : W → X)
    (hrefl : ∀ i x, d i x x = 0)
    (htriangle : ∀ i x y z, d i x z ≤ d i x y + d i y z)
    (length : Sym2 W → ENNReal) (sep : ENNReal)
    (hseparation : ∀ {a b}, H.Adj a b → ∀ i, label s(a, b) = some i → sep ≤ d i (project a) (project b))
    (hreference : ∀ i {a b}, H.Adj a b → label s(a, b) = none → d i (project a) (project b) ≤ length s(a, b))
    (hearlier : ∀ i j {a b}, H.Adj a b → label s(a, b) = some j → j < i → d i (project a) (project b) = 0)
    {z : W} (c : H.Walk z z) (hc : c.IsCycle) :
    sep ≤ (c.edges.map length).sum := by
  classical
  obtain ⟨u, v, i, huv, he, hi, hmax⟩ := exists_latest_cycle_edge c hc label hforest
  obtain ⟨p, hp, hsub⟩ := cycle_avoiding_edge_path c hc he
  have hstep : ∀ {a b}, H.Adj a b → s(a, b) ∈ p.edges →
      d i (project a) (project b) ≤ length s(a, b) := by
    intro a b hab hmem
    cases hl : label s(a, b) with
    | none => exact hreference i hab hl
    | some j =>
      have hji := hmax _ (hsub _ hmem).1 j hl
      have hne : j ≠ i := by
        intro h
        subst j
        exact (hsub _ hmem).2 (hunique _ _ i hl hi)
      rw [hearlier i j hab hl (by omega)]
      exact bot_le
  calc
    sep ≤ d i (project u) (project v) := hseparation huv i hi
    _ ≤ (p.edges.map length).sum := distance_le_walk_sum (d i) project (hrefl i) (htriangle i) length p hstep
    _ ≤ (c.edges.map length).sum := ennreal_nodup_sum_map_le_of_subset length hp.isTrail.edges_nodup
      (by intro e he; exact (hsub e he).1)

end OnlineSteinerForest.UpperBound
