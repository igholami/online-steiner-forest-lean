import OnlineSteinerForest.LowerBound.Probability.BoundaryLists
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin

/-! Encode a bounded list of positive run lengths as a finite vector. -/
namespace OnlineSteinerForest.LowerBound.Trace

variable {B q : ℕ}

def encodeRuns (xs : List (ℕ × Bool)) (hlen : xs.length = q)
    (hpos : ∀ d ∈ xs, 0 < d.1) (hbound : ∀ d ∈ xs, d.1 ≤ B) : Fin q → (Fin B × Bool) :=
  fun k =>
    let d := xs.get ⟨k.val, by simpa only [hlen] using k.isLt⟩
    (⟨d.1 - 1, by
      have hd : d ∈ xs := List.get_mem _ _
      have hp := hpos d hd
      have hb := hbound d hd
      omega⟩, d.2)

theorem encodeRuns_ofFn (xs : List (ℕ × Bool)) (hlen : xs.length = q)
    (hpos : ∀ d ∈ xs, 0 < d.1) (hbound : ∀ d ∈ xs, d.1 ≤ B) :
    List.ofFn (fun k => (((encodeRuns xs hlen hpos hbound k).1.val + 1),
      (encodeRuns xs hlen hpos hbound k).2)) = xs := by
  have hentry (k : Fin q) :
      (((encodeRuns xs hlen hpos hbound k).1.val + 1), (encodeRuns xs hlen hpos hbound k).2) =
      xs.get ⟨k.val, by simpa only [hlen] using k.isLt⟩ := by
    dsimp [encodeRuns]
    apply Prod.ext
    · have hp := hpos _ (List.get_mem xs ⟨k.val, by simpa only [hlen] using k.isLt⟩)
      change 0 < xs[k.val].1 at hp
      change xs[k.val].1 - 1 + 1 = xs[k.val].1
      omega
    · rfl
  calc
    _ = List.ofFn (fun k : Fin q => xs.get ⟨k.val, by simpa only [hlen] using k.isLt⟩) :=
      congrArg List.ofFn (funext hentry)
    _ = xs := Probability.ofFn_get_of_length_eq xs hlen

theorem encodeRuns_sum (xs : List (ℕ × Bool)) (hlen : xs.length = q)
    (hpos : ∀ d ∈ xs, 0 < d.1) (hbound : ∀ d ∈ xs, d.1 ≤ B) :
    (∑ k : Fin q, ((encodeRuns xs hlen hpos hbound k).1.val + 1)) = (xs.map Prod.fst).sum := by
  have hh := congrArg (fun ys : List (ℕ × Bool) => (ys.map Prod.fst).sum)
    (encodeRuns_ofFn xs hlen hpos hbound)
  simpa only [List.map_ofFn, Function.comp_apply, List.sum_ofFn] using hh

end OnlineSteinerForest.LowerBound.Trace
