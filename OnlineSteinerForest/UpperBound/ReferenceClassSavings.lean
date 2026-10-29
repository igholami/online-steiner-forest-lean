import OnlineSteinerForest.UpperBound.ReferenceClassRun
import OnlineSteinerForest.UpperBound.ReferenceSavings
import Mathlib.Algebra.BigOperators.Fin

/-! Savings of the actual class executions telescope to one optimum per class. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def classSaving (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (r : Fin (batchClassCount requests.length)) (b : ℕ) : ℝ :=
  edgeCost c (classReference G c hc requests feasible r b).val -
    edgeCost c (classReference G c hc requests feasible r (b + 1)).val

theorem classSaving_nonneg (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (r : Fin (batchClassCount requests.length)) (b : ℕ) :
    0 ≤ classSaving G c hc requests feasible r b :=
  sub_nonneg.mpr (referenceRun_cost_step G c hc (initialReference G c hc requests feasible)
    (initialReference_spec G c hc requests feasible).1.1 (futureMarks G c requests feasible r) b)

theorem classSaving_sum_le_optimum (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (r : Fin (batchClassCount requests.length)) :
    (∑ b ∈ batchClass requests.length r, classSaving G c hc requests feasible r b.val) ≤
      optimum G c requests feasible := by
  apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun b _ _ => classSaving_nonneg G c hc requests feasible r b.val)).trans
  have h := referenceRun_savings_bound G c hc (initialReference G c hc requests feasible)
    (initialReference_spec G c hc requests feasible).1.1
    (futureMarks G c requests feasible r) (requests.length.log2 + 1)
  have hfinal := h.trans (initialReference_spec G c hc requests feasible).2.2.le
  rw [Fin.sum_univ_eq_sum_range (fun b => classSaving G c hc requests feasible r b)
    (requests.length.log2 + 1)]
  simpa only [classSaving, classReference] using hfinal

end OnlineSteinerForest.UpperBound
