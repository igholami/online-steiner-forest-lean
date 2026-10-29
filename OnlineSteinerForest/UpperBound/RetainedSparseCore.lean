import OnlineSteinerForest.UpperBound.SparseConfiguredCore
import OnlineSteinerForest.UpperBound.SparseConfiguredDiscard
import OnlineSteinerForest.UpperBound.CoreIncidenceSum

/-! The computed sparse core has all degree, rank-density and discarded-cost guarantees. -/
namespace OnlineSteinerForest.UpperBound

open scoped Classical
variable {Z I : Type*} [Fintype I] [DecidableEq Z] [DecidableEq I]

theorem retained_core_density (L : ℕ) (hL : 1 ≤ L) (left right : I → Z) (S : Finset Z) :
    2 * (sparseCore left right (coreDegree L) S).card ≤
      (liveEdges left right (sparseCore left right (coreDegree L) S)).card := by
  apply core_vertices_le_half_edges
  intro v hv
  have hpos := parallelCap_pos L hL
  have hmin := (sparseCore_spec left right (coreDegree L) S).2.1 v hv
  change 8191 * parallelCap L ≤ _ at hmin
  omega

theorem retained_sparse_core_guarantees (L : ℕ) (hL : 1 ≤ L)
    (left right : I → Z) (S : Finset Z)
    (hleft : ∀ i, left i ∈ S) (hright : ∀ i, right i ∈ S)
    (hloops : ∀ z ∈ S, (loopsAt left right z).card ≤ parallelCap L)
    (hparallel : ∀ u v, (parallelEdges left right S u v).card ≤ parallelCap L)
    (scale C : ℝ) (hscale : 0 ≤ scale)
    (hcost : (S.card : ℝ) * zoneMultiplier L * scale ≤ C) :
    let K := sparseCore left right (coreDegree L) S
    K ⊆ S ∧
    (∀ z : ↥K, 8191 ≤ (zoneNeighborGraph left right K).degree z) ∧
    2 * K.card ≤ (liveEdges left right K).card ∧
    ((Fintype.card I - (liveEdges left right K).card : ℕ) : ℝ) * scale ≤
      (2 : ℝ)^28 * cycleFactor L * C := by
  exact ⟨(sparseCore_spec left right (coreDegree L) S).1,
    configured_core_minimum_degree L hL left right S hparallel,
    retained_core_density L hL left right S,
    configured_discarded_count_scale_le L hL left right S hleft hright hloops scale C hscale hcost⟩

end OnlineSteinerForest.UpperBound
