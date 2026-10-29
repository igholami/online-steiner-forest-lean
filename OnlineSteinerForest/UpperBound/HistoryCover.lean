import OnlineSteinerForest.UpperBound.HistoryMergeEdges
import OnlineSteinerForest.UpperBound.HistoryZeroStep

/-! Active analysis clusters cover exactly the actual purchased edges. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem step_active_clusterEdges (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (state : MergeHistory ℕ) (i : ℕ) (touched : Finset (LabeledCluster ℕ))
    (ht : touched ⊆ state.active) :
    (MergeHistory.step state i touched).active.biUnion (clusterEdges G c requests feasible) =
      purchasedBlock G c requests feasible i ∪ state.active.biUnion (clusterEdges G c requests feasible) := by
  change (insert (MergeHistory.merged i touched) (state.active \ touched)).biUnion
    (clusterEdges G c requests feasible) = _
  rw [Finset.biUnion_insert, merged_clusterEdges]
  ext e
  simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_sdiff]
  constructor
  · rintro ((he | ⟨C, hC, he⟩) | ⟨C, ⟨hC, hCt⟩, he⟩)
    · exact Or.inl he
    · exact Or.inr ⟨C, ht hC, he⟩
    · exact Or.inr ⟨C, hC, he⟩
  · rintro (he | ⟨C, hC, he⟩)
    · exact Or.inl (Or.inl he)
    · by_cases hCt : C ∈ touched
      · exact Or.inl (Or.inr ⟨C, hCt, he⟩)
      · exact Or.inr ⟨C, ⟨hC, hCt⟩, he⟩

theorem greedyHistory_covers (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (i : ℕ) (hi : i ≤ requests.length) :
    (greedyHistory G c requests feasible i).active.biUnion (clusterEdges G c requests feasible) =
      boughtBefore G c requests feasible i := by
  induction i with
  | zero => simp [greedyHistory, scanHistory, MergeHistory.empty]
  | succ i ih =>
    have hi' : i < requests.length := by omega
    have ih := ih (by omega)
    by_cases hp : 0 < blockPayment G c requests feasible i
    · change (scanHistory _ _ (i + 1)).active.biUnion _ = _
      rw [scanHistory, if_pos hp, step_active_clusterEdges G c requests feasible _ i _ (Finset.filter_subset _ _)]
      change purchasedBlock G c requests feasible i ∪
        (greedyHistory G c requests feasible i).active.biUnion _ = _
      rw [ih]
      exact Finset.sdiff_union_of_subset (boughtBefore_mono G c requests feasible i (i + 1) (by omega))
    · have hp' : ¬ 0 < payment G c requests feasible ⟨i, hi'⟩ := by simpa [blockPayment, hi'] using hp
      simpa [greedyHistory, scanHistory, hp, zero_payment_no_change G c hc requests feasible ⟨i, hi'⟩ hp'] using ih

end OnlineSteinerForest.UpperBound
