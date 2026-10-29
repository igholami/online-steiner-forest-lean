import OnlineSteinerForest.LowerBound.Probability.BoundaryLists
import OnlineSteinerForest.LowerBound.Trace.OrientedRanks
import OnlineSteinerForest.LowerBound.Trace.BadRoute

/-! Extract injective rank/orientation prescriptions from an actual simple alternate route. -/
namespace OnlineSteinerForest.LowerBound.Probability

variable [OnlineSteinerForest.PathSelection]

open Trace

variable {m : ℕ} {σ : Equiv.Perm (Fin (2 * m))} {R : Finset (Fin m)}
variable {u v : Fin (2 * m)}

def routeRanks (i : Fin m) (p : Route σ R u v) (hp : p.realize.IsPath)
    (havoid : ∀ j ∈ R, j ≠ i) : Fin p.ranks.length ↪ {j : Fin m // j ≠ i} where
  toFun k := ⟨p.ranks.get k, havoid _ (p.rank_mem _ (List.get_mem _ k))⟩
  inj' _a _b heq := List.nodup_iff_injective_get.mp (p.ranks_nodup hp) (congrArg Subtype.val heq)

def routeFlips (p : Route σ R u v) (k : Fin p.ranks.length) : Bool :=
  (p.assignments.get ⟨k.val, by simpa only [p.assignments_length] using k.isLt⟩).2

theorem route_assignments_ofFn (i : Fin m) (p : Route σ R u v) (hp : p.realize.IsPath)
    (havoid : ∀ j ∈ R, j ≠ i) :
    List.ofFn (fun j => ((routeRanks i p hp havoid j).val, routeFlips p j)) = p.assignments := by
  have hentry (j : Fin p.ranks.length) :
      ((routeRanks i p hp havoid j).val, routeFlips p j) =
        p.assignments.get ⟨j.val, by simpa only [p.assignments_length] using j.isLt⟩ := by
    apply Prod.ext
    · have hj : j.val < p.assignments.length := by simpa only [p.assignments_length] using j.isLt
      change p.ranks[j.val] = (p.assignments[j.val]'hj).1
      have hmap := congrArg (fun xs : List (Fin m) => xs[j.val]?) p.assignments_fst
      rw [List.getElem?_map, List.getElem?_eq_getElem hj, List.getElem?_eq_getElem j.isLt] at hmap
      simp only [Option.map_some, Option.some.injEq] at hmap
      exact hmap.symm
    · rfl
  calc
    _ = List.ofFn (fun j : Fin p.ranks.length =>
        p.assignments.get ⟨j.val, by simpa only [p.assignments_length] using j.isLt⟩) :=
      congrArg List.ofFn (funext hentry)
    _ = _ := ofFn_get_of_length_eq p.assignments p.assignments_length

theorem route_domain_ofFn (i : Fin m) (p : Route σ R u v) (hp : p.realize.IsPath)
    (havoid : ∀ j ∈ R, j ≠ i) :
    List.ofFn (boundaryTuple i (routeRanks i p hp havoid) (routeFlips p)) =
      slotEmbedding (i, 0) :: (p.assignmentSlots ++ [slotEmbedding (i, 1)]) := by
  rw [boundaryTuple_ofFn, route_assignments_ofFn]
  rfl

/-- Every alternate route provides precisely the injective permutation-image event
used in the finite weighted union bound. -/
theorem test_route_tuple_images (h : ℕ) (σ : Equiv.Perm (Fin (2 * matchingSize h)))
    (i : Fin (matchingSize h))
    (p : Route σ (testRanks h i) (leftEndpoint σ i) (rightEndpoint σ i))
    (hp : p.realize.IsPath) :
    let ranks := routeRanks i p hp (fun _j hj => (Finset.mem_erase.mp hj).1)
    ∀ k : Fin (2 * p.ranks.length + 2),
      σ (boundaryTuple i ranks (routeFlips p) k) =
        p.vertexTuple hp (endpoints_ne σ i) (Trace.test_left_unmatched h σ i)
          (Trace.test_right_unmatched h σ i) k := by
  dsimp only
  have hdom := route_domain_ofFn i p hp (fun _j hj => (Finset.mem_erase.mp hj).1)
  have hmap := (congrArg (List.map σ) hdom).trans (p.boundary_slots_map i)
  rw [List.map_ofFn] at hmap
  have hv : List.ofFn (p.vertexTuple hp (endpoints_ne σ i) (Trace.test_left_unmatched h σ i)
      (Trace.test_right_unmatched h σ i)) = p.boundaries :=
    ofFn_get_of_length_eq p.boundaries p.boundaries_length
  have heq := List.ofFn_injective (hmap.trans hv.symm)
  exact congrFun heq

end OnlineSteinerForest.LowerBound.Probability
