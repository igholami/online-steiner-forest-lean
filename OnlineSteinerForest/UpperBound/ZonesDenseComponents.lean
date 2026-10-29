import OnlineSteinerForest.UpperBound.ZonesComponentCounts
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Finite
import Lean.Elab.Tactic.Omega

/-! Dense core components have at least 8192 zones, bounding the number of merged hubs. -/
namespace OnlineSteinerForest.UpperBound

open scoped Classical BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem dense_component_size (G : SimpleGraph V) (hdeg : ∀ v, 8191 ≤ G.degree v)
    (C : G.ConnectedComponent) : 8192 ≤ Fintype.card C := by
  let u : C := Classical.choice C.connected_toSimpleGraph.nonempty
  have heq : C.toSimpleGraph.degree u = G.degree u.val := by
    apply SimpleGraph.degree_induce_of_neighborSet_subset
    intro v hv
    exact C.mem_supp_of_adj_mem_supp u.property hv
  have hlt := C.toSimpleGraph.degree_lt_card_verts u
  have hlower := hdeg u.val
  omega

theorem dense_component_count (G : SimpleGraph V) [Fintype G.ConnectedComponent]
    (hdeg : ∀ v, 8191 ≤ G.degree v) :
    8192 * Fintype.card G.ConnectedComponent ≤ Fintype.card V := by
  have hall : Finset.univ.image G.connectedComponentMk = Finset.univ := by
    ext C
    simp only [Finset.mem_image, Finset.mem_univ, true_and, iff_true]
    induction C using SimpleGraph.ConnectedComponent.ind with
    | h v => exact ⟨v, rfl⟩
  have hsum : (∑ C : G.ConnectedComponent, Fintype.card C) = Fintype.card V := by
    have h := sum_componentTerminals G Finset.univ
    simpa only [componentTerminals, Finset.mem_univ, Finset.filter_true,
      Finset.card_univ, hall] using h
  calc
    8192 * Fintype.card G.ConnectedComponent = ∑ _C : G.ConnectedComponent, 8192 := by
      simp [Nat.mul_comm]
    _ ≤ ∑ C : G.ConnectedComponent, Fintype.card C :=
      Finset.sum_le_sum fun C _ => dense_component_size G hdeg C
    _ = Fintype.card V := hsum

end OnlineSteinerForest.UpperBound
