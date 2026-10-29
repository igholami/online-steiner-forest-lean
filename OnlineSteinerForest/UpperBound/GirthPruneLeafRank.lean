import OnlineSteinerForest.UpperBound.GirthPruneLeafConnected
import OnlineSteinerForest.UpperBound.GirthConnectedRank

/-! Leaf deletion preserves cycle rank and decreases total edge cost. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*} [Fintype V] [Fintype I] [DecidableEq I] [DecidableEq V]

theorem leaf_cycleRank (left right : I → V) (v : V) (d : Dart I)
    (hd : outgoing left right v = {d}) (hc : (endpointGraph left right).Connected) :
    cycleRank (leafLeft left right v d hd) (leafRight left right v d hd) = cycleRank left right := by
  rw [connected_cycleRank_eq _ _ (leaf_endpoint_connected left right v d hd hc), connected_cycleRank_eq left right hc]
  have hv := suppressedVertex_card v
  have he := prunedLeafEdge_card d
  omega

theorem leaf_weight_sum (w : I → ℝ) (d : Dart I) :
    (∑ i : PrunedLeafEdge d, w i) + w d.1 = ∑ i, w i := by
  have hsub : (∑ i ∈ (Finset.univ : Finset I) \ {d.1}, w i) = ∑ i : PrunedLeafEdge d, w i :=
    Finset.sum_subtype _ (by intro i; simp [PrunedLeafEdge]) w
  rw [← hsub]
  have hh := Finset.sum_sdiff (f := w) (Finset.subset_univ ({d.1} : Finset I))
  simpa using hh

theorem leaf_weight_sum_le (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (d : Dart I) :
    (∑ i : PrunedLeafEdge d, w i) ≤ ∑ i, w i := by
  have hh := leaf_weight_sum w d
  linarith [hw d.1]

end OnlineSteinerForest.UpperBound.Girth
