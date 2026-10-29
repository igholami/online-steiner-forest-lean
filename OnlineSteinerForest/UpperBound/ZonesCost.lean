import OnlineSteinerForest.Graph.Cost

/-! Exact original-edge accounting for a finite edge-disjoint family of zones. -/
namespace OnlineSteinerForest.UpperBound

variable {V I : Type*} [DecidableEq V] [DecidableEq I]

/-- Edge-disjoint zones count each original edge exactly once. -/
theorem zone_cost_sum (c : Sym2 V → ℝ) (indices : Finset I)
    (zones : I → Finset (Sym2 V))
    (hdisjoint : (indices : Set I).PairwiseDisjoint zones) :
    (∑ i ∈ indices, edgeCost c (zones i)) = edgeCost c (indices.biUnion zones) := by
  classical
  exact (Finset.sum_biUnion hdisjoint).symm

/-- Each zone costs at least the scale, so their number is bounded by the
cost of their union divided by that scale. -/
theorem zone_count_le_cost_div (c : Sym2 V → ℝ) (indices : Finset I)
    (zones : I → Finset (Sym2 V)) (scale : ℝ) (hscale : 0 < scale)
    (hdisjoint : (indices : Set I).PairwiseDisjoint zones)
    (hlower : ∀ i ∈ indices, scale ≤ edgeCost c (zones i)) :
    (indices.card : ℝ) ≤ edgeCost c (indices.biUnion zones) / scale := by
  apply (le_div_iff₀ hscale).mpr
  calc
    (indices.card : ℝ) * scale = ∑ _i ∈ indices, scale := by simp
    _ ≤ ∑ i ∈ indices, edgeCost c (zones i) := Finset.sum_le_sum hlower
    _ = edgeCost c (indices.biUnion zones) := zone_cost_sum c indices zones hdisjoint

end OnlineSteinerForest.UpperBound
