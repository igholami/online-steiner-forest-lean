import OnlineSteinerForest.UpperBound.ChargingGraph
import OnlineSteinerForest.UpperBound.ThresholdLeafExtension

/-! Deleting auxiliary middle edges leaves precisely a forest with fresh leaves. -/
namespace OnlineSteinerForest.UpperBound.Charging

open scoped Classical
variable {W J : Type*} [DecidableEq W]

def referenceEmbedding (H : SimpleGraph W) (left : J → W) : H ↪g referenceSpokes H left where
  toFun := Sum.inl
  inj' := Sum.inl_injective
  map_rel_iff' := Iff.rfl

theorem referenceSpokes_acyclic (H : SimpleGraph W) (hH : H.IsAcyclic) (left : J → W) :
    (referenceSpokes H left).IsAcyclic := by
  apply isAcyclic_leaf_extension (referenceEmbedding H left) hH
  intro x hx u v hxu hxv
  cases x with
  | inl w => exact False.elim (hx ⟨w, rfl⟩)
  | inr j =>
    cases u with
    | inl u =>
      cases v with
      | inl v =>
        change u = left j at hxu
        change v = left j at hxv
        exact congrArg Sum.inl (hxu.trans hxv.symm)
      | inr v => exact hxv.elim
    | inr u => exact hxu.elim

theorem reference_delete_eq (H : SimpleGraph W) (left right : J → W) (hne : ∀ j, left j ≠ right j) :
    (graph H left right).deleteEdges {e | edgeLabel right e ≠ none} = referenceSpokes H left := by
  ext x y
  cases x <;> cases y <;> simp [SimpleGraph.deleteEdges_adj, graph, referenceSpokes, edgeLabel]
  all_goals grind

end OnlineSteinerForest.UpperBound.Charging
