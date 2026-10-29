import OnlineSteinerForest.UpperBound.OmissionsLabelPayments
import OnlineSteinerForest.UpperBound.MassPaidLabels

/-! Sum the computed first/long omission tests over the actual paid labels of a batch. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def firstOmittedBatchPayment (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (batch : Finset (Fin requests.length)) : ℝ :=
  ∑ label ∈ paidLabels G c requests feasible, firstOmittedLabelPayment G c requests feasible batch label

noncomputable def longOmittedBatchPayment (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (batch : Finset (Fin requests.length)) (scale : ℝ) : ℝ :=
  ∑ label ∈ paidLabels G c requests feasible,
    longOmittedLabelPayment G c hc requests feasible fallback batch label scale

theorem first_omitted_batch_scaled (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (batch : Finset (Fin requests.length)) :
    (64 * (cycleFactor requests.length : ℝ) ^ 2) * firstOmittedBatchPayment G c requests feasible batch ≤
      cycleFactor requests.length * greedyCost G c requests feasible := by
  rw [firstOmittedBatchPayment, Finset.mul_sum]
  exact (Finset.sum_le_sum (fun label _ => first_omitted_label_scaled G c hc requests feasible batch label)).trans
    (sum_paid_label_mass G c hc requests feasible)

theorem long_omitted_batch_scaled (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (batch : Finset (Fin requests.length)) (scale : ℝ)
    (hbatch : ∀ i ∈ batch, blockPayment G c requests feasible i.val ≤ 2 * scale) :
    (128 * (cycleFactor requests.length : ℝ) ^ 3) * longOmittedBatchPayment G c hc requests feasible fallback batch scale ≤
      2 * (cycleFactor requests.length : ℝ) ^ 2 * greedyCost G c requests feasible := by
  rw [longOmittedBatchPayment, Finset.mul_sum]
  calc
    _ ≤ ∑ label ∈ paidLabels G c requests feasible,
        2 * cycleFactor requests.length * clusterWeight (blockPayment G c requests feasible)
          (finalLifetime G c requests feasible label) :=
      Finset.sum_le_sum (fun label _ => long_omitted_label_scaled G c hc requests feasible fallback batch label scale hbatch)
    _ = (2 * cycleFactor requests.length) *
        ∑ label ∈ paidLabels G c requests feasible,
          clusterWeight (blockPayment G c requests feasible) (finalLifetime G c requests feasible label) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (2 * cycleFactor requests.length) * (cycleFactor requests.length * greedyCost G c requests feasible) :=
      mul_le_mul_of_nonneg_left (sum_paid_label_mass G c (fun e he => le_of_lt (hc e he)) requests feasible) (by positivity)
    _ = _ := by ring

end OnlineSteinerForest.UpperBound
