import OnlineSteinerForest.UpperBound.AuxiliaryExtract
import OnlineSteinerForest.UpperBound.AuxiliaryLabelOmissions
import OnlineSteinerForest.UpperBound.OmissionsOriginalSets

/-! Every omitted positive request is in an explicitly budgeted original-index omission set. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem extractAuxiliary_none_cases (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (batch : Finset (Fin requests.length)) (scale : ℝ) (i : Fin requests.length)
    (hi : i ∈ batch) (hp : 0 < blockPayment G c requests feasible i.val)
    (hn : extractAuxiliary G c hc requests feasible fallback batch scale i = none) :
    i ∈ firstOmittedRequests G c requests feasible batch ∨
      i ∈ longOmittedRequests G c hc requests feasible fallback batch scale := by
  have hlpaid : pairLabel G c requests feasible i.val ∈ paidLabels G c requests feasible :=
    Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩, rfl⟩
  unfold extractAuxiliary at hn
  rw [dif_pos hi, dif_pos hp] at hn
  split_ifs at hn with hb
  have hiS : i ∈ labelBatch G c requests feasible batch (pairLabel G c requests feasible i.val) :=
    Finset.mem_filter.mpr ⟨hi, hp, Finset.nonempty_iff_ne_empty.mpr hb, rfl⟩
  have hnon : (labelBatch G c requests feasible batch (pairLabel G c requests feasible i.val)).Nonempty := ⟨i, hiS⟩
  have hcases := extractLabelAux_none_cases G c hc requests feasible fallback batch _ _ scale _ hn
  rcases hcases with hfirst | ⟨p, hlong, hpos⟩
  · left
    apply Finset.mem_biUnion.mpr
    refine ⟨pairLabel G c requests feasible i.val, hlpaid, ?_⟩
    rw [firstRequestsForLabel, dif_pos hnon]
    exact Finset.mem_image.mpr ⟨_, hfirst,
      orderedLabelRequest_labelPosition G c requests feasible batch _ _ i _⟩
  · right
    apply Finset.mem_biUnion.mpr
    refine ⟨pairLabel G c requests feasible i.val, hlpaid, ?_⟩
    rw [longRequestsForLabel, dif_pos hnon]
    refine Finset.mem_image.mpr ⟨p, hlong, ?_⟩
    rw [hpos]
    exact orderedLabelRequest_labelPosition G c requests feasible batch _ _ i _

end OnlineSteinerForest.UpperBound
