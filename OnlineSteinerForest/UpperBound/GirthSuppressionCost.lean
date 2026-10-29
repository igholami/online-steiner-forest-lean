import OnlineSteinerForest.UpperBound.GirthSuppress
import Mathlib.Data.Fintype.BigOperators

/-! Degree-two suppression preserves total edge cost exactly. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*} [Fintype I] [DecidableEq I]

theorem suppressedWeight_sum (w : I → ℝ) (d e : Dart I) (hlabels : d.1 ≠ e.1) :
    (∑ i : SuppressedEdge d e, suppressedWeight w d e i) = ∑ i, w i := by
  let S := (Finset.univ : Finset I) \ {d.1, e.1}
  have hsub : (∑ i ∈ S, w i) = ∑ i : {i : I // i ≠ d.1 ∧ i ≠ e.1}, w i := by
    exact Finset.sum_subtype S (by intro i; simp [S]) w
  have hpart : (∑ i ∈ S, w i) + (w d.1 + w e.1) = ∑ i, w i := by
    have hh := Finset.sum_sdiff (f := w) (Finset.subset_univ ({d.1, e.1} : Finset I))
    simpa [S, hlabels] using hh
  rw [Fintype.sum_option]
  change w d.1 + w e.1 + (∑ i : {i : I // i ≠ d.1 ∧ i ≠ e.1}, w i) = _
  rw [← hsub]
  simpa [add_comm] using hpart

end OnlineSteinerForest.UpperBound.Girth
