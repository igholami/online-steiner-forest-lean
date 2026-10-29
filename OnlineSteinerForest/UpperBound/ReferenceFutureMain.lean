import OnlineSteinerForest.UpperBound.ReferenceFutureBudget
import OnlineSteinerForest.UpperBound.ReferenceFutureScale
import OnlineSteinerForest.UpperBound.ReferenceFutureConnected
import OnlineSteinerForest.UpperBound.ThresholdMain

/-! The actual future-mark overhead is absorbed by the current reference-forest cost. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem future_mark_overhead_le_reference (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (hk : 0 < requests.length) (ho : 0 < optimum G c requests feasible)
    (r : Fin (batchClassCount requests.length)) (b : Fin (requests.length.log2 + 1))
    (hb : b ∈ batchClass requests.length r) :
    2 ^ 25 * (cycleFactor requests.length : ℝ) ^ 4 *
      (futureMarks G c requests feasible r b.val).card * batchScale G c requests feasible b.val ≤
        edgeCost c (classReference G c hc requests feasible r b.val).val := by
  have href : 0 ≤ edgeCost c (classReference G c hc requests feasible r b.val).val := by
    apply Finset.sum_nonneg
    intro e he
    exact hc e ((classReference G c hc requests feasible r b.val).property e he)
  apply mark_overhead_le_reference requests.length _ _ _ ?_ href
  apply future_marks_scale_budget G c requests feasible r b.val _ _
    (batchScale_pos G c requests feasible hk ho b.val).le href
  exact request_count_mul_separation_le G c hc requests feasible
    (futurePairs G c requests feasible r b.val) (classReference G c hc requests feasible r b.val).val
    (classReference G c hc requests feasible r b.val).property
    (classReference_connects_future G c hc requests feasible r b.val)
    _ (mul_pos (pow_pos (by norm_num) _) (batchScale_pos G c requests feasible hk ho b.val))
    (future_pair_payment_ge G c requests feasible hk ho r b hb)

end OnlineSteinerForest.UpperBound
