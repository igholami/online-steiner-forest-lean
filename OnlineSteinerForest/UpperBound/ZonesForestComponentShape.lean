import OnlineSteinerForest.UpperBound.SmallComponentEdges
import OnlineSteinerForest.UpperBound.ZonesTreeRepresentation

/-! Present every ordinary forest component as a valid tree shape in the same original vertex type. -/
namespace OnlineSteinerForest.UpperBound

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_component_zoneTree (F : SimpleGraph V) (hF : F.IsAcyclic) (C : F.ConnectedComponent) :
    ∃ r : V, ∃ t : ZoneTree V r, t.Valid ∧ t.edges = componentEdges F C := by
  let root : C := Classical.choice C.connected_toSimpleGraph.nonempty
  obtain ⟨t, ht, he, hv⟩ := exists_zoneTree C.toSimpleGraph (hF.isTree_connectedComponent C) root
  refine ⟨root.val, t.map Subtype.val, t.valid_map ht _ Subtype.val_injective, ?_⟩
  rw [ZoneTree.edges_map, he]
  rw [componentEdges, Finset.map_eq_image]
  rfl

end OnlineSteinerForest.UpperBound
