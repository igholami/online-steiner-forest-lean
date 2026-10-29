import OnlineSteinerForest.UpperBound.AuxiliaryOmittedCases
import OnlineSteinerForest.UpperBound.OmissionsOriginalPayments

/-! Account every actual positive batch payment by retained outputs or proved omissions. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem auxiliary_batch_cover (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (batch : Finset (Fin requests.length)) (scale : ℝ)
    (hp : ∀ i ∈ batch, 0 < blockPayment G c requests feasible i.val) :
    batch ⊆ (retainedAuxRequests G c hc requests feasible fallback batch scale ∪
      firstOmittedRequests G c requests feasible batch) ∪
        longOmittedRequests G c hc requests feasible fallback batch scale := by
  intro i hi
  by_cases hr : i ∈ retainedAuxRequests G c hc requests feasible fallback batch scale
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ hr)
  · have hnone : extractAuxiliary G c hc requests feasible fallback batch scale i = none := by
      apply Option.not_isSome_iff_eq_none.mp
      intro hs
      exact hr (Finset.mem_filter.mpr ⟨hi, hs⟩)
    rcases extractAuxiliary_none_cases G c hc requests feasible fallback batch scale i hi (hp i hi) hnone with hf | hl
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hf)
    · exact Finset.mem_union_right _ hl

theorem auxiliary_batch_payment_cover (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (batch : Finset (Fin requests.length)) (scale : ℝ)
    (hp : ∀ i ∈ batch, 0 < blockPayment G c requests feasible i.val) :
    ∑ i ∈ batch, payment G c requests feasible i ≤
      (∑ i ∈ retainedAuxRequests G c hc requests feasible fallback batch scale, payment G c requests feasible i) +
        firstOmittedBatchPayment G c requests feasible batch +
          longOmittedBatchPayment G c hc requests feasible fallback batch scale := by
  have hn := payment_nonneg G c (fun e he => le_of_lt (hc e he)) requests feasible
  calc
    _ ≤ ∑ i ∈ (retainedAuxRequests G c hc requests feasible fallback batch scale ∪
        firstOmittedRequests G c requests feasible batch) ∪ longOmittedRequests G c hc requests feasible fallback batch scale,
          payment G c requests feasible i :=
      Finset.sum_le_sum_of_subset_of_nonneg (auxiliary_batch_cover G c hc requests feasible fallback batch scale hp)
        (fun i _ _ => hn i)
    _ ≤ ((∑ i ∈ retainedAuxRequests G c hc requests feasible fallback batch scale, payment G c requests feasible i) +
        ∑ i ∈ firstOmittedRequests G c requests feasible batch, payment G c requests feasible i) +
          ∑ i ∈ longOmittedRequests G c hc requests feasible fallback batch scale, payment G c requests feasible i :=
      (sum_union_le_add _ _ _ hn).trans (add_le_add (sum_union_le_add _ _ _ hn) le_rfl)
    _ ≤ _ := add_le_add
      (add_le_add le_rfl (firstOmittedRequests_payment_le G c (fun e he => le_of_lt (hc e he)) requests feasible batch))
      (longOmittedRequests_payment_le G c hc requests feasible fallback batch scale)

end OnlineSteinerForest.UpperBound
