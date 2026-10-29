import OnlineSteinerForest.UpperBound.SparseCore
import Mathlib.Combinatorics.SimpleGraph.Finite

/-! The ordinary neighbor graph underlying a loopless labelled zone graph. -/
namespace OnlineSteinerForest.UpperBound

variable {V I : Type*} [Fintype I] [DecidableEq V]

def parallelEdges (left right : I → V) (S : Finset V) (u v : V) : Finset I :=
  (liveEdges left right S).filter (fun i =>
    (left i = u ∧ right i = v) ∨ (left i = v ∧ right i = u))

def zoneNeighborGraph (left right : I → V) (S : Finset V) : SimpleGraph ↥S where
  Adj u v := ∃ i ∈ liveEdges left right S,
    (left i = u.val ∧ right i = v.val) ∨ (left i = v.val ∧ right i = u.val)
  symm.symm u v := by
    rintro ⟨i, hi, h⟩
    exact ⟨i, hi, h.symm⟩
  loopless.irrefl u := by
    rintro ⟨i, hi, h⟩
    have hne := (Finset.mem_filter.mp hi).2.2.2
    rcases h with ⟨hl, hr⟩ | ⟨hl, hr⟩ <;> exact hne (hl.trans hr.symm)

def otherEndpoint (left right : I → V) (v : V) (i : I) : V :=
  if left i = v then right i else left i

theorem otherEndpoint_mem (left right : I → V) (S : Finset V) (v : V) (i : I)
    (hi : i ∈ incidentEdges left right S v) : otherEndpoint left right v i ∈ S := by
  have hlive := (Finset.mem_filter.mp hi).1
  have hends := (Finset.mem_filter.mp hlive).2
  unfold otherEndpoint
  split_ifs
  · exact hends.2.1
  · exact hends.1

theorem endpoint_pair_other (left right : I → V) (S : Finset V) (v : V) (i : I)
    (hi : i ∈ incidentEdges left right S v) :
    (left i = v ∧ right i = otherEndpoint left right v i) ∨
      (left i = otherEndpoint left right v i ∧ right i = v) := by
  by_cases hl : left i = v
  · exact Or.inl ⟨hl, by simp [otherEndpoint, hl]⟩
  · exact Or.inr ⟨by simp [otherEndpoint, hl], (Finset.mem_filter.mp hi).2.resolve_left hl⟩

/-- Send each incident labelled edge to its other endpoint in the current vertex set. -/
noncomputable def neighborOf (left right : I → V) (S : Finset V) (v : ↥S) (i : I) : ↥S := by
  classical
  exact if h : i ∈ incidentEdges left right S v.val then
    ⟨otherEndpoint left right v.val i, otherEndpoint_mem left right S v.val i h⟩ else v

theorem neighborOf_val (left right : I → V) (S : Finset V) (v : ↥S) (i : I)
    (hi : i ∈ incidentEdges left right S v.val) :
    (neighborOf left right S v i).val = otherEndpoint left right v.val i := by
  simp [neighborOf, hi]

theorem neighborOf_adj (left right : I → V) (S : Finset V) (v : ↥S) (i : I)
    (hi : i ∈ incidentEdges left right S v.val) :
    (zoneNeighborGraph left right S).Adj v (neighborOf left right S v i) := by
  refine ⟨i, (Finset.mem_filter.mp hi).1, ?_⟩
  rw [neighborOf_val left right S v i hi]
  exact endpoint_pair_other left right S v.val i hi

theorem neighbor_fiber_subset_parallel (left right : I → V) (S : Finset V) (v u : ↥S) :
    ((incidentEdges left right S v.val).filter (fun i => neighborOf left right S v i = u)) ⊆
      parallelEdges left right S v.val u.val := by
  intro i hi
  obtain ⟨hi, heq⟩ := Finset.mem_filter.mp hi
  have hother : otherEndpoint left right v.val i = u.val := by
    rw [← neighborOf_val left right S v i hi]
    exact congrArg Subtype.val heq
  apply Finset.mem_filter.mpr
  refine ⟨(Finset.mem_filter.mp hi).1, ?_⟩
  simpa only [hother] using endpoint_pair_other left right S v.val i hi

end OnlineSteinerForest.UpperBound
