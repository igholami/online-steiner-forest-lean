import OnlineSteinerForest.UpperBound.ReferenceBatchBudget
import OnlineSteinerForest.UpperBound.ReferenceAccounting
import OnlineSteinerForest.UpperBound.FinalCoefficient

/-! All remaining numerical upper accounting reduces to the retained-pair geometry. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- This conditional reduction isolates the remaining geometric lemma; it is
not the main upper theorem. All batch and reference states here are computed. -/
theorem upper_from_retained_estimates (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (hk : 0 < requests.length) (ho : 0 < optimum G c requests feasible)
    (hretained : ∀ (r : Fin (batchClassCount requests.length))
      (b : Fin (requests.length.log2 + 1)), b ∈ batchClass requests.length r →
      ((retainedReferenceRequests G c hc requests feasible fallback
        (classReference G c (fun e he => (hc e he).le) requests feasible r b.val).val b).card : ℝ) *
        batchScale G c requests feasible b.val ≤
      32 * cycleFactor requests.length * classSaving G c (fun e he => (hc e he).le) requests feasible r b.val +
        2 ^ 24 * (cycleFactor requests.length : ℝ) ^ 4 *
          (futureMarks G c requests feasible r b.val).card * batchScale G c requests feasible b.val +
        2 ^ 28 * cycleFactor (cycleFactor requests.length) *
          edgeCost c (classReference G c (fun e he => (hc e he).le) requests feasible r b.val).val) :
    greedyCost G c requests feasible ≤ finalUpperConstant * optimum G c requests feasible *
      Real.log (2 * requests.length) * Real.log (Real.log (4 * requests.length)) := by
  let hc₀ := fun e he => (hc e he).le
  have haccount := reference_accounting G c hc₀ requests feasible hk ho
    (2 ^ 30 * cycleFactor (cycleFactor requests.length) + 1) (by positivity)
    (fun _ b => referenceOmittedPayment G c hc requests feasible fallback b)
    (fun r b hb => reference_batch_budget_of_retained_bound G c hc requests feasible fallback hk ho
      r b hb (hretained r b hb))
    (referenceOmitted_class_sum_le G c hc requests feasible fallback hk ho)
  have hcoeff := accountingCoefficient_le_logs requests.length (by omega)
  calc
    greedyCost G c requests feasible ≤ accountingCoefficient requests.length * optimum G c requests feasible := by
      convert haccount using 1 <;> unfold accountingCoefficient <;> ring
    _ ≤ (finalUpperConstant * Real.log (2 * requests.length) *
        Real.log (Real.log (4 * requests.length))) * optimum G c requests feasible :=
      mul_le_mul_of_nonneg_right hcoeff ho.le
    _ = _ := by ring

end OnlineSteinerForest.UpperBound
