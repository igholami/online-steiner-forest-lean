import OnlineSteinerForest.UpperBound.AuxiliaryPaymentCoverage
import OnlineSteinerForest.UpperBound.AuxiliaryReferenceSplit

/-! The actual small/large split and retained outputs account for every bucket payment. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem sum_reference_split (c : Sym2 V → ℝ) (requests : List (V × V))
    (F : Finset (Sym2 V)) (batch : Finset (Fin requests.length)) (scale : ℝ) (pay : Fin requests.length → ℝ) :
    ∑ i ∈ batch, pay i = (∑ i ∈ smallReferencePairs c requests F batch scale, pay i) +
      ∑ i ∈ largeReferencePairs c requests F batch scale, pay i := by
  have hs := Finset.sum_sdiff (Finset.filter_subset
    (fun i : Fin requests.length => referenceTreeCost F c requests[i.val].1 <
      65536 * (cycleFactor requests.length : ℝ) ^ 3 * scale) batch) (f := pay)
  simpa only [largeReferencePairs, smallReferencePairs, add_comm] using hs.symm

theorem retained_payment_le_card (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (batch : Finset (Fin requests.length)) (scale : ℝ)
    (hbatch : ∀ i ∈ batch, payment G c requests feasible i ≤ 2 * scale) :
    ∑ i ∈ retainedAuxRequests G c hc requests feasible fallback batch scale, payment G c requests feasible i ≤
      2 * scale * (retainedAuxRequests G c hc requests feasible fallback batch scale).card := by
  calc
    _ ≤ ∑ _i ∈ retainedAuxRequests G c hc requests feasible fallback batch scale, (2 * scale) :=
      Finset.sum_le_sum (fun i hi => hbatch i (Finset.mem_filter.mp hi).1)
    _ = _ := by simp [mul_comm]

theorem batch_reference_accounting (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (F : Finset (Sym2 V)) (batch : Finset (Fin requests.length)) (scale : ℝ) (hs : 0 < scale)
    (hbatch : ∀ i ∈ batch, scale ≤ payment G c requests feasible i ∧ payment G c requests feasible i ≤ 2 * scale) :
    ∑ i ∈ batch, payment G c requests feasible i ≤
      (∑ i ∈ smallReferencePairs c requests F batch scale, payment G c requests feasible i) +
      2 * scale * (retainedAuxRequests G c hc requests feasible fallback
        (largeReferencePairs c requests F batch scale) scale).card +
      firstOmittedBatchPayment G c requests feasible (largeReferencePairs c requests F batch scale) +
      longOmittedBatchPayment G c hc requests feasible fallback (largeReferencePairs c requests F batch scale) scale := by
  have hsub := largeReferencePairs_subset c requests F batch scale
  have hp : ∀ i ∈ largeReferencePairs c requests F batch scale,
      0 < blockPayment G c requests feasible i.val := by
    intro i hi
    have hpos := hs.trans_le (hbatch i (hsub hi)).1
    simpa only [blockPayment, dif_pos i.isLt] using hpos
  have hcover := auxiliary_batch_payment_cover G c hc requests feasible fallback
    (largeReferencePairs c requests F batch scale) scale hp
  have hret := retained_payment_le_card G c hc requests feasible fallback
    (largeReferencePairs c requests F batch scale) scale (fun i hi => (hbatch i (hsub hi)).2)
  rw [sum_reference_split c requests F batch scale (payment G c requests feasible)]
  linarith

end OnlineSteinerForest.UpperBound
