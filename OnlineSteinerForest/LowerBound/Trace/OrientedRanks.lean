import OnlineSteinerForest.LowerBound.Trace.BoundaryVertices
import OnlineSteinerForest.LowerBound.Probability.BoundaryTuple

/-! Explicit ranks and orientation bits prescribe every shortcut endpoint image. -/
namespace OnlineSteinerForest.LowerBound.Trace.Route

open Probability

variable {m : ℕ} {σ : Equiv.Perm (Fin (2 * m))} {R : Finset (Fin m)}
variable {u v : Fin (2 * m)}

def assignments : {u v : Fin (2 * m)} → Route σ R u v → List (Fin m × Bool)
  | _, _, .nil _ => []
  | _, _, .base _ p => p.assignments
  | a, _, .shortcut i _ _ p => (i, decide (a = rightEndpoint σ i)) :: p.assignments

theorem assignments_fst (p : Route σ R u v) : p.assignments.map Prod.fst = p.ranks := by
  induction p <;> simp [assignments, ranks, *]

theorem assignments_length (p : Route σ R u v) : p.assignments.length = p.ranks.length := by
  simpa only [List.length_map] using congrArg List.length p.assignments_fst

def assignmentSlots (p : Route σ R u v) : List (Fin (2 * m)) :=
  p.assignments.flatMap (fun a => [slotEmbedding (a.1, orientSide a.2 0),
    slotEmbedding (a.1, orientSide a.2 1)])

@[simp] theorem sigma_slot_zero (i : Fin m) : σ (slotEmbedding (i, 0)) = leftEndpoint σ i := rfl
@[simp] theorem sigma_slot_one (i : Fin m) : σ (slotEmbedding (i, 1)) = rightEndpoint σ i := rfl

theorem assignmentSlots_map (p : Route σ R u v) : p.assignmentSlots.map σ = p.shortcutVertices := by
  induction p with
  | nil => rfl
  | base h p ih => exact ih
  | shortcut i hi ho p ih =>
    rcases ho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simpa [assignmentSlots, assignments, shortcutVertices, orientSide,
        endpoints_ne σ i] using congrArg
          (fun xs => leftEndpoint σ i :: rightEndpoint σ i :: xs) ih
    · simpa [assignmentSlots, assignments, shortcutVertices, orientSide] using congrArg
          (fun xs => rightEndpoint σ i :: leftEndpoint σ i :: xs) ih

theorem assignmentSlots_length (p : Route σ R u v) :
    p.assignmentSlots.length = 2 * p.ranks.length := by
  simpa only [List.length_map, shortcutVertices_length] using congrArg List.length p.assignmentSlots_map

theorem boundary_slots_map (i : Fin m) (p : Route σ R (leftEndpoint σ i) (rightEndpoint σ i)) :
    (slotEmbedding (i, 0) :: (p.assignmentSlots ++ [slotEmbedding (i, 1)])).map σ = p.boundaries := by
  simp [boundaries, assignmentSlots_map]

end OnlineSteinerForest.LowerBound.Trace.Route
