import OnlineSteinerForest.UpperBound.OmissionsOriginalSets
import OnlineSteinerForest.UpperBound.OmissionsBatchPayments
import OnlineSteinerForest.UpperBound.OmissionsUnionPayment

/-! The original-index omission payments satisfy the already-proved aggregate budgets. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem firstRequestsForLabel_payment (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (batch : Finset (Fin requests.length)) (label : ℕ) :
    ∑ i ∈ firstRequestsForLabel G c requests feasible batch label, payment G c requests feasible i =
      firstOmittedLabelPayment G c requests feasible batch label := by
  unfold firstRequestsForLabel firstOmittedLabelPayment
  split_ifs with hn
  · dsimp only
    rw [Finset.sum_image (fun _ _ _ _ h => (orderedLabelRequest G c requests feasible batch label _).injective h)]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [blockPayment, dif_pos (orderedLabelRequest G c requests feasible batch label _ j).isLt]
  · simp

theorem longRequestsForLabel_payment (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (batch : Finset (Fin requests.length)) (label : ℕ) (scale : ℝ) :
    ∑ i ∈ longRequestsForLabel G c hc requests feasible fallback batch label scale, payment G c requests feasible i =
      longOmittedLabelPayment G c hc requests feasible fallback batch label scale := by
  unfold longRequestsForLabel longOmittedLabelPayment
  split_ifs with hn
  · dsimp only
    rw [Finset.sum_image (fun _ _ _ _ h => newIndex_injective
      ((orderedLabelRequest G c requests feasible batch label _).injective h))]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [blockPayment, dif_pos (orderedLabelRequest G c requests feasible batch label _ (newIndex j)).isLt]
  · simp

theorem firstOmittedRequests_payment_le (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (batch : Finset (Fin requests.length)) :
    ∑ i ∈ firstOmittedRequests G c requests feasible batch, payment G c requests feasible i ≤
      firstOmittedBatchPayment G c requests feasible batch := by
  unfold firstOmittedRequests firstOmittedBatchPayment
  apply (sum_biUnion_le_sum _ _ _ (payment_nonneg G c hc requests feasible)).trans_eq
  exact Finset.sum_congr rfl (fun label _ => firstRequestsForLabel_payment G c requests feasible batch label)

theorem longOmittedRequests_payment_le (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (batch : Finset (Fin requests.length)) (scale : ℝ) :
    ∑ i ∈ longOmittedRequests G c hc requests feasible fallback batch scale, payment G c requests feasible i ≤
      longOmittedBatchPayment G c hc requests feasible fallback batch scale := by
  unfold longOmittedRequests longOmittedBatchPayment
  apply (sum_biUnion_le_sum _ _ _ (payment_nonneg G c (fun e he => le_of_lt (hc e he)) requests feasible)).trans_eq
  exact Finset.sum_congr rfl (fun label _ => longRequestsForLabel_payment G c hc requests feasible fallback batch label scale)

end OnlineSteinerForest.UpperBound
