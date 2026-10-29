import OnlineSteinerForest.UpperBound.BatchAlgorithm

/-! The computed dyadic batches cover all but at most OPT of the greedy payment. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem lowPayment_sum_le_optimum (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (hk : 0 < requests.length) (ho : 0 < optimum G c requests feasible) :
    ∑ i ∈ lowPaymentSet G c requests feasible, payment G c requests feasible i ≤ optimum G c requests feasible := by
  have hb := dyadicBase_pos G c requests feasible hk ho
  calc
    _ ≤ ∑ _i ∈ lowPaymentSet G c requests feasible, dyadicBase G c requests feasible := by
      apply Finset.sum_le_sum
      intro i hi
      exact le_of_lt (Finset.mem_filter.mp hi).2
    _ = ((lowPaymentSet G c requests feasible).card : ℝ) * dyadicBase G c requests feasible := by simp
    _ ≤ (requests.length : ℝ) * dyadicBase G c requests feasible := by
      apply mul_le_mul_of_nonneg_right _ (le_of_lt hb)
      exact_mod_cast (by simpa only [Fintype.card_fin] using Finset.card_le_univ (s := lowPaymentSet G c requests feasible))
    _ = _ := by
      unfold dyadicBase
      have hn : (requests.length : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk)
      field_simp

theorem costBatch_union (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (hk : 0 < requests.length) (ho : 0 < optimum G c requests feasible) :
    Finset.univ.biUnion (costBatch G c requests feasible) = Finset.univ \ lowPaymentSet G c requests feasible := by
  ext i
  constructor
  · intro hi
    obtain ⟨b, hb, hi⟩ := Finset.mem_biUnion.mp hi
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    intro hlow
    exact not_lt_of_ge (Finset.mem_filter.mp hi).2.1 (Finset.mem_filter.mp hlow).2
  · intro hi
    obtain ⟨b, hb⟩ := costBatch_cover G c hc requests feasible hk ho i (Finset.mem_sdiff.mp hi).2
    exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ _, hb⟩

theorem sum_costBatch_payments (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (hk : 0 < requests.length) (ho : 0 < optimum G c requests feasible) :
    ∑ b : Fin (requests.length.log2 + 1), ∑ i ∈ costBatch G c requests feasible b,
      payment G c requests feasible i = greedyCost G c requests feasible -
        ∑ i ∈ lowPaymentSet G c requests feasible, payment G c requests feasible i := by
  rw [← Finset.sum_biUnion (fun b hb d hd hbd => costBatch_disjoint G c requests feasible b d hbd),
    costBatch_union G c hc requests feasible hk ho]
  have hs := Finset.sum_sdiff (Finset.subset_univ (lowPaymentSet G c requests feasible))
    (f := payment G c requests feasible)
  rw [sum_payments_eq_greedyCost G c requests feasible] at hs
  exact eq_sub_of_add_eq hs

end OnlineSteinerForest.UpperBound
