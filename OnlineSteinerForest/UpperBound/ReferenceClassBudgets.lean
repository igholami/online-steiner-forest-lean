import OnlineSteinerForest.UpperBound.ReferenceClassSavings
import OnlineSteinerForest.Graph.Nonnegative

/-! Total savings and reference-cost budgets for all computed residue-class runs. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem all_class_savings_le (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) :
    (∑ r : Fin (batchClassCount requests.length),
      ∑ b ∈ batchClass requests.length r, classSaving G c hc requests feasible r b.val) ≤
      batchClassCount requests.length * optimum G c requests feasible := by
  calc
    _ ≤ ∑ _r : Fin (batchClassCount requests.length), optimum G c requests feasible :=
      Finset.sum_le_sum fun r _ => classSaving_sum_le_optimum G c hc requests feasible r
    _ = _ := by simp

theorem all_class_reference_costs_le (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) :
    (∑ r : Fin (batchClassCount requests.length), ∑ b ∈ batchClass requests.length r,
      edgeCost c (classReference G c hc requests feasible r b.val).val) ≤
      cycleFactor requests.length * optimum G c requests feasible := by
  calc
    _ ≤ ∑ r : Fin (batchClassCount requests.length), ∑ _b ∈ batchClass requests.length r,
        optimum G c requests feasible := by
      apply Finset.sum_le_sum
      intro r _
      exact Finset.sum_le_sum fun b _ => classReference_cost_le_optimum G c hc requests feasible r b.val
    _ = ∑ _b : Fin (requests.length.log2 + 1), optimum G c requests feasible := by
      rw [← Finset.sum_biUnion (fun r hr s hs hrs => batchClass_disjoint _ r s hrs), batchClass_union]
    _ = (Fintype.card (Fin (requests.length.log2 + 1)) : ℝ) * optimum G c requests feasible := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (costBatch_count_le requests.length)
      (optimum_nonneg G c hc requests feasible)

end OnlineSteinerForest.UpperBound
