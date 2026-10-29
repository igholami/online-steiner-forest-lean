import OnlineSteinerForest.LowerBound.Probability.BoundaryTuple
import Mathlib.Data.List.OfFn

/-! The tuple of prescribed positions has exactly the expected interleaved list order. -/
namespace OnlineSteinerForest.LowerBound.Probability

variable {m q : ℕ}

theorem ofFn_get_of_length_eq {α : Type*} (xs : List α) (hn : xs.length = q) :
    List.ofFn (fun j : Fin q => xs.get ⟨j.val, by simpa only [hn] using j.isLt⟩) = xs := by
  subst q
  exact List.ofFn_get xs

theorem boundaryTuple_ofFn (i : Fin m) (ranks : Fin q ↪ {j : Fin m // j ≠ i})
    (flip : Fin q → Bool) :
    List.ofFn (boundaryTuple i ranks flip) =
      slotEmbedding (i, 0) ::
        ((List.ofFn (fun j => ((ranks j).val, flip j))).flatMap
          (fun a => [slotEmbedding (a.1, orientSide a.2 0),
            slotEmbedding (a.1, orientSide a.2 1)]) ++ [slotEmbedding (i, 1)]) := by
  rw [List.ofFn_succ, List.ofFn_succ']
  rw [boundaryTuple_zero]
  have hlast : boundaryTuple i ranks flip (Fin.last (2 * q)).succ = slotEmbedding (i, 1) :=
    boundaryTuple_last i ranks flip
  rw [hlast]
  change slotEmbedding (i, 0) ::
    ((List.ofFn (fun k : Fin (2 * q) => boundaryTuple i ranks flip
      ⟨k.val + 1, by omega⟩)).concat (slotEmbedding (i, 1))) = _
  rw [List.ofFn_mul']
  have hmid (j : Fin q) (b : Fin 2) :
      boundaryTuple i ranks flip ⟨2 * j.val + b.val + 1, by omega⟩ =
        slotEmbedding ((ranks j).val, orientSide (flip j) b) :=
    boundaryTuple_shortcut i ranks flip j b
  simp only [hmid]
  simp [List.flatMap_def, List.ofFn_succ, List.concat_eq_append, Function.comp_def]

end OnlineSteinerForest.LowerBound.Probability
