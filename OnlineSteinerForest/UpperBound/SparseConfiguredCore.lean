import OnlineSteinerForest.UpperBound.SparseDegree
import OnlineSteinerForest.UpperBound.SparseParameters
import OnlineSteinerForest.UpperBound.SparsePeeling

/-! Exact manuscript peeling parameters produce the required distinct-neighbor core. -/
namespace OnlineSteinerForest.UpperBound

open scoped Classical

variable {V I : Type*} [Fintype I] [DecidableEq V] [DecidableEq I]

theorem liveEdges_mono (left right : I → V) {S T : Finset V} (hST : S ⊆ T) :
    liveEdges left right S ⊆ liveEdges left right T := by
  intro i hi
  obtain ⟨_, hleft, hright, hne⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hST hleft, hST hright, hne⟩

theorem parallelEdges_mono (left right : I → V) {S T : Finset V} (hST : S ⊆ T) (u v : V) :
    parallelEdges left right S u v ⊆ parallelEdges left right T u v := by
  intro i hi
  obtain ⟨hmem, hp⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨liveEdges_mono left right hST hmem, hp⟩

theorem configured_core_minimum_degree (L : ℕ) (hL : 1 ≤ L) (left right : I → V) (S : Finset V)
    (hcap : ∀ u v, (parallelEdges left right S u v).card ≤ parallelCap L) :
    ∀ v : ↥(sparseCore left right (coreDegree L) S),
      8191 ≤ (zoneNeighborGraph left right (sparseCore left right (coreDegree L) S)).degree v := by
  have hs := sparseCore_spec left right (coreDegree L) S
  apply zone_minimum_degree left right _ (parallelCap L) 8191 (parallelCap_pos L hL)
  · intro u v
    exact (Finset.card_le_card (parallelEdges_mono left right hs.1 u v)).trans (hcap u v)
  · simpa only [coreDegree] using hs.2.1

theorem configured_core_centers (L : ℕ) (hL : 1 ≤ L) (left right : I → V) (S : Finset V)
    (hcap : ∀ u v, (parallelEdges left right S u v).card ≤ parallelCap L) :
    ∃ C : Finset ↥(sparseCore left right (coreDegree L) S),
      (∀ v, v ∈ C ∨ ∃ u ∈ C, (zoneNeighborGraph left right (sparseCore left right (coreDegree L) S)).Adj v u) ∧
      (C.card : ℝ) ≤ (sparseCore left right (coreDegree L) S).card / 512 := by
  simpa only [Fintype.card_coe] using exists_small_dominating_set
    (zoneNeighborGraph left right (sparseCore left right (coreDegree L) S))
    (configured_core_minimum_degree L hL left right S hcap)

end OnlineSteinerForest.UpperBound
