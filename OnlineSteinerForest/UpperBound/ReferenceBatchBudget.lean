import OnlineSteinerForest.UpperBound.SmallMain
import OnlineSteinerForest.UpperBound.ReferenceFutureMain
import OnlineSteinerForest.UpperBound.ReferenceClassSavings
import OnlineSteinerForest.UpperBound.ReferenceOmissions
import OnlineSteinerForest.UpperBound.AuxiliaryReferenceAccounting

/-! Assemble the proved small/omitted/mark bounds around a retained-pair replacement estimate. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem reference_batch_budget_of_retained_bound (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (hk : 0 < requests.length) (ho : 0 < optimum G c requests feasible)
    (r : Fin (batchClassCount requests.length)) (b : Fin (requests.length.log2 + 1))
    (hb : b ∈ batchClass requests.length r)
    (hretained :
      ((retainedReferenceRequests G c hc requests feasible fallback
        (classReference G c (fun e he => (hc e he).le) requests feasible r b.val).val b).card : ℝ) *
        batchScale G c requests feasible b.val ≤
      32 * cycleFactor requests.length * classSaving G c (fun e he => (hc e he).le) requests feasible r b.val +
        2 ^ 24 * (cycleFactor requests.length : ℝ) ^ 4 *
          (futureMarks G c requests feasible r b.val).card * batchScale G c requests feasible b.val +
        2 ^ 28 * cycleFactor (cycleFactor requests.length) *
          edgeCost c (classReference G c (fun e he => (hc e he).le) requests feasible r b.val).val) :
    (∑ i ∈ costBatch G c requests feasible b, payment G c requests feasible i) ≤
      referenceOmittedPayment G c hc requests feasible fallback b +
      64 * cycleFactor requests.length * classSaving G c (fun e he => (hc e he).le) requests feasible r b.val +
      (2 ^ 30 * cycleFactor (cycleFactor requests.length) + 1) *
        edgeCost c (classReference G c (fun e he => (hc e he).le) requests feasible r b.val).val := by
  let hc₀ := fun e he => (hc e he).le
  let F := (classReference G c hc₀ requests feasible r b.val).val
  have hinput : ∀ e ∈ F, e ∈ G.edgeSet :=
    (classReference G c hc₀ requests feasible r b.val).property
  have hsmall := small_reference_payment_bound G c hc₀ requests feasible hk F hinput
    (costBatch G c requests feasible b) (batchScale G c requests feasible b.val)
    (batchScale_pos G c requests feasible hk ho b.val)
    (classReference_connects_batch G c hc₀ requests feasible r b hb)
    (fun i hi => ⟨(costBatch_band G c requests feasible hk ho b i hi).1,
      (costBatch_band G c requests feasible hk ho b i hi).2.le⟩)
  have hcover := costBatch_reference_accounting G c hc requests feasible fallback hk ho F b
  have hmark := future_mark_overhead_le_reference G c hc₀ requests feasible hk ho r b hb
  have homit : referenceOmittedPayment G c hc requests feasible fallback b =
      firstOmittedBatchPayment G c requests feasible
        (largeReferencePairs c requests F (costBatch G c requests feasible b) (batchScale G c requests feasible b.val)) +
      longOmittedBatchPayment G c hc requests feasible fallback
        (largeReferencePairs c requests F (costBatch G c requests feasible b) (batchScale G c requests feasible b.val))
        (batchScale G c requests feasible b.val) := by
    unfold referenceOmittedPayment
    rw [batchReference_eq G c hc₀ requests feasible r b hb]
  have href : 0 ≤ edgeCost c F := by
    exact Finset.sum_nonneg fun e he => hc₀ e (hinput e he)
  have hH : 0 ≤ (cycleFactor (cycleFactor requests.length) : ℝ) * edgeCost c F :=
    mul_nonneg (Nat.cast_nonneg _) href
  change _ ≤ 32 * cycleFactor requests.length *
    classSaving G c hc₀ requests feasible r b.val + _ + 2 ^ 28 * cycleFactor (cycleFactor requests.length) * edgeCost c F at hretained
  change _ ≤ _ + 64 * cycleFactor requests.length *
    classSaving G c hc₀ requests feasible r b.val + (2 ^ 30 * cycleFactor (cycleFactor requests.length) + 1) * edgeCost c F
  nlinarith only [hretained, hsmall, hcover, hmark, homit, hH]

end OnlineSteinerForest.UpperBound
