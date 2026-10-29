import OnlineSteinerForest.UpperBound.ThresholdForestRequests
import OnlineSteinerForest.UpperBound.ThresholdReferenceForest

/-! The threshold lemma stated directly for the implemented greedy algorithm. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Any reference edge set connecting a subset of actual requests pays for their
common lower payment threshold, with the manuscript's explicit logarithmic factor. -/
theorem request_count_mul_separation_le (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (J : Finset (Fin requests.length)) (F : Finset (Sym2 V))
    (hF : ∀ e ∈ F, e ∈ G.edgeSet)
    (hconnect : ∀ i ∈ J, (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).Reachable requests[i.val].1 requests[i.val].2)
    (τ : ℝ) (hτ : 0 < τ)
    (hpay : ∀ i ∈ J, τ ≤ payment G c requests feasible i) :
    (J.card : ℝ) * τ ≤ 4 * cycleFactor J.card * edgeCost c F := by
  classical
  obtain ⟨T, hTF, hT, hreach, _hcost⟩ := exists_reference_forest F c (fun e he => hc e (hF e he))
  let H := SimpleGraph.fromEdgeSet (T : Set (Sym2 V))
  have hHG : H ≤ G := by
    intro u v huv
    exact hF _ (hTF huv.1)
  have hh := request_count_mul_separation_le_forest G H hHG hT c hc requests feasible
    (fun i : ↥J => i.val) Subtype.coe_injective τ hτ (fun i => hpay i.val i.property)
    (fun i => by rw [hreach]; exact hconnect i.val i.property)
  simp only [Fintype.card_coe] at hh
  refine hh.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he
    simp only [SimpleGraph.edgeFinset, Set.mem_toFinset] at he
    have hm : e ∈ (T : Set (Sym2 V)) \ Sym2.diagSet := by
      simpa only [H, SimpleGraph.edgeSet_fromEdgeSet] using he
    exact hTF hm.1
  · intro e he _
    exact hc e (hF e he)

end OnlineSteinerForest.UpperBound
