import OnlineSteinerForest.UpperBound.SparseNeighbors
import OnlineSteinerForest.UpperBound.ReplacementDomination

/-! A multiplicity cap turns large labelled degree into many distinct neighbors. -/
namespace OnlineSteinerForest.UpperBound

open scoped Classical

variable {V I : Type*} [Fintype I] [DecidableEq V]

theorem labelled_degree_le_parallel_mul_degree (left right : I → V) (S : Finset V) (B : ℕ)
    (hcap : ∀ u v, (parallelEdges left right S u v).card ≤ B) (v : ↥S) :
    (incidentEdges left right S v.val).card ≤ B * (zoneNeighborGraph left right S).degree v := by
  let f := neighborOf left right S v
  have hf : ∀ u ∈ (incidentEdges left right S v.val).image f,
      ((incidentEdges left right S v.val).filter (fun i => f i = u)).card ≤ B := by
    intro u _
    exact (Finset.card_le_card (neighbor_fiber_subset_parallel left right S v u)).trans
      (hcap v.val u.val)
  have hh := Finset.card_le_mul_card_image (f := f) (incidentEdges left right S v.val) B hf
  have hsub : (incidentEdges left right S v.val).image f ⊆
      (zoneNeighborGraph left right S).neighborFinset v := by
    intro u hu
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    exact ((zoneNeighborGraph left right S).mem_neighborFinset v _).mpr
      (neighborOf_adj left right S v i hi)
  have hc := Nat.mul_le_mul_left B (Finset.card_le_card hsub)
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hc
  exact hh.trans hc

theorem zone_minimum_degree (left right : I → V) (S : Finset V) (B d : ℕ) (hB : 0 < B)
    (hcap : ∀ u v, (parallelEdges left right S u v).card ≤ B)
    (hmin : ∀ v ∈ S, d * B ≤ (incidentEdges left right S v).card) :
    ∀ v : ↥S, d ≤ (zoneNeighborGraph left right S).degree v := by
  intro v
  have hh := (hmin v.val v.prop).trans (labelled_degree_le_parallel_mul_degree left right S B hcap v)
  by_contra hn
  have hlt := Nat.mul_lt_mul_of_pos_left (Nat.lt_of_not_ge hn) hB
  rw [Nat.mul_comm d B] at hh
  omega

/-- This is the source's distinct-neighbor core conclusion followed by center selection. -/
theorem exists_zone_core_centers (left right : I → V) (S : Finset V) (B : ℕ) (hB : 0 < B)
    (hcap : ∀ u v, (parallelEdges left right S u v).card ≤ B)
    (hmin : ∀ v ∈ S, 8191 * B ≤ (incidentEdges left right S v).card) :
    ∃ C : Finset ↥S, (∀ v, v ∈ C ∨ ∃ u ∈ C, (zoneNeighborGraph left right S).Adj v u) ∧
      (C.card : ℝ) ≤ S.card / 512 := by
  simpa only [Fintype.card_coe] using exists_small_dominating_set (zoneNeighborGraph left right S)
    (zone_minimum_degree left right S B 8191 hB hcap hmin)

end OnlineSteinerForest.UpperBound
