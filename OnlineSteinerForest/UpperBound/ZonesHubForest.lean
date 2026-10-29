import OnlineSteinerForest.UpperBound.ZonesHubComponent
import OnlineSteinerForest.UpperBound.ZonesGraphUnion

/-! Choosing the required terminal trees in every component of a boundary-hub graph. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical BigOperators

/-- For an arbitrary finite graph, connect exactly the originally connected
required pairs while bounding all required-vertex incidences by twice their count. -/
theorem exists_terminal_spanning_subgraph {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (terminals : Finset V) :
    ∃ H : SimpleGraph V, H ≤ G ∧
      (∀ u ∈ terminals, ∀ v ∈ terminals, G.Reachable u v → H.Reachable u v) ∧
      (∑ v ∈ terminals, H.degree v) ≤ 2 * terminals.card := by
  let J := ↥(terminals.image G.connectedComponentMk)
  have hlocal : ∀ j : J, ∃ H : SimpleGraph V, H ≤ G ∧ H.support ⊆ j.val.supp ∧
      (∀ u ∈ terminals, ∀ v ∈ terminals,
        u ∈ j.val.supp → v ∈ j.val.supp → H.Reachable u v) ∧
      (∑ v ∈ terminals, H.degree v) ≤ 2 * (componentTerminals G terminals j.val).card := by
    intro j
    exact exists_component_terminal_subgraph G terminals j.val j.property
  choose graphs hle _ hconnect hbudget using hlocal
  let H := ⨆ j : J, graphs j
  have hsum : (∑ j : J, (componentTerminals G terminals j.val).card) = terminals.card := by
    change (∑ j : ↥(terminals.image G.connectedComponentMk),
      (componentTerminals G terminals j.val).card) = terminals.card
    exact (Finset.sum_coe_sort _ _).trans (sum_componentTerminals G terminals)
  refine ⟨H, iSup_le hle, ?_, ?_⟩
  · intro u hu v hv huv
    let j : J := ⟨G.connectedComponentMk u, Finset.mem_image_of_mem _ hu⟩
    have huC : u ∈ j.val.supp := (j.val.mem_supp_iff u).mpr rfl
    have hvC : v ∈ j.val.supp := (j.val.mem_supp_iff v).mpr
      (SimpleGraph.ConnectedComponent.sound huv).symm
    exact (hconnect j u hu v hv huC hvC).mono (le_iSup graphs j)
  · calc
      (∑ v ∈ terminals, H.degree v) ≤ ∑ v ∈ terminals, ∑ j : J, (graphs j).degree v := by
        apply Finset.sum_le_sum
        intro v _
        exact degree_iSup_le graphs v
      _ = ∑ j : J, ∑ v ∈ terminals, (graphs j).degree v := Finset.sum_comm
      _ ≤ ∑ j : J, 2 * (componentTerminals G terminals j.val).card := by
        exact Finset.sum_le_sum fun j _ => hbudget j
      _ = 2 * ∑ j : J, (componentTerminals G terminals j.val).card := (Finset.mul_sum _ _ _).symm
      _ = 2 * terminals.card := by rw [hsum]

end OnlineSteinerForest.UpperBound
