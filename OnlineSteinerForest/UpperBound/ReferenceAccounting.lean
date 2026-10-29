import OnlineSteinerForest.UpperBound.ReferenceClassBudgets
import OnlineSteinerForest.UpperBound.Accounting

/-! Final numerical summation for the computed batches and actual reference executions. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Once the geometric single-batch bounds and omission budget are proved,
the actual reference states supply all remaining summation budgets. -/
theorem reference_accounting (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (hk : 0 < requests.length) (ho : 0 < optimum G c requests feasible)
    (A : ℝ) (hA : 0 ≤ A)
    (omitted : Fin (batchClassCount requests.length) → Fin (requests.length.log2 + 1) → ℝ)
    (hbatch : ∀ r b, b ∈ batchClass requests.length r →
      (∑ i ∈ costBatch G c requests feasible b, payment G c requests feasible i) ≤
        omitted r b + 64 * cycleFactor requests.length * classSaving G c hc requests feasible r b.val +
          A * edgeCost c (classReference G c hc requests feasible r b.val).val)
    (homitted : (∑ r : Fin (batchClassCount requests.length),
      ∑ b ∈ batchClass requests.length r, omitted r b) ≤ greedyCost G c requests feasible / 32) :
    greedyCost G c requests feasible ≤ (32 / 31 : ℝ) * optimum G c requests feasible *
      (1 + 64 * batchClassCount requests.length * cycleFactor requests.length + A * cycleFactor requests.length) := by
  have hpart := sum_batchClassPayment G c requests feasible
  rw [sum_costBatch_payments G c hc requests feasible hk ho] at hpart
  simp only [batchClassPayment] at hpart
  have hsum : (∑ r : Fin (batchClassCount requests.length), ∑ b ∈ batchClass requests.length r,
      ∑ i ∈ costBatch G c requests feasible b, payment G c requests feasible i) ≤
      (∑ r : Fin (batchClassCount requests.length), ∑ b ∈ batchClass requests.length r, omitted r b) +
      64 * cycleFactor requests.length *
        (∑ r : Fin (batchClassCount requests.length), ∑ b ∈ batchClass requests.length r,
          classSaving G c hc requests feasible r b.val) +
      A * (∑ r : Fin (batchClassCount requests.length), ∑ b ∈ batchClass requests.length r,
        edgeCost c (classReference G c hc requests feasible r b.val).val) := by
    calc
      _ ≤ ∑ r : Fin (batchClassCount requests.length), ∑ b ∈ batchClass requests.length r,
          (omitted r b + 64 * cycleFactor requests.length * classSaving G c hc requests feasible r b.val +
            A * edgeCost c (classReference G c hc requests feasible r b.val).val) := by
        exact Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun b hb => hbatch r b hb
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.mul_sum]
  have hsavings := mul_le_mul_of_nonneg_left (all_class_savings_le G c hc requests feasible)
    (by positivity : (0 : ℝ) ≤ 64 * cycleFactor requests.length)
  have hreference := mul_le_mul_of_nonneg_left
    (all_class_reference_costs_le G c hc requests feasible) hA
  have hlow := lowPayment_sum_le_optimum G c requests feasible hk ho
  apply absorb_omissions (greedyCost G c requests feasible) (optimum G c requests feasible)
    (cycleFactor requests.length) (batchClassCount requests.length) A
  rw [hpart] at hsum
  nlinarith

end OnlineSteinerForest.UpperBound
