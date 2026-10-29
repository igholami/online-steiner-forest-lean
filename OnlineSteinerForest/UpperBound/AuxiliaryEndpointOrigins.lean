import OnlineSteinerForest.UpperBound.AuxiliaryExtractLabel

/-! Every output endpoint is an original endpoint of a request in the supplied large-pair batch. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem labelFarSequence_origin (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (batch : Finset (Fin requests.length)) (label : ℕ) {n : ℕ}
    (hcard : (labelBatch G c requests feasible batch label).card = n) (j : Fin n) :
    ∃ i ∈ batch, (labelFarSequence G c hc requests feasible fallback batch label hcard j).val = requests[i.val].1 ∨
      (labelFarSequence G c hc requests feasible fallback batch label hcard j).val = requests[i.val].2 := by
  let i := orderedLabelRequest G c requests feasible batch label hcard j
  have hm := Finset.mem_filter.mp (orderedLabelRequest_mem G c requests feasible batch label hcard j)
  refine ⟨i, hm.1, ?_⟩
  exact farEndpoint_eq G c _ _ _ _ _ _

theorem extractLabelAux_endpoint_origin (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (batch : Finset (Fin requests.length)) (label : ℕ) {n : ℕ}
    (hcard : (labelBatch G c requests feasible batch label).card = n + 1) (scale : ℝ)
    (j : Fin (n + 1)) (out : AuxiliaryOutput V)
    (hout : extractLabelAux G c hc requests feasible fallback batch label hcard scale j = some out) :
    (∃ i ∈ batch, out.left = requests[i.val].1 ∨ out.left = requests[i.val].2) ∧
      (∃ i ∈ batch, out.right = requests[i.val].1 ∨ out.right = requests[i.val].2) := by
  have hm := Finset.mem_filter.mp (orderedLabelRequest_mem G c requests feasible batch label hcard j)
  dsimp only [extractLabelAux] at hout
  split_ifs at hout with hcheap hzero hlong
  · have heq := Option.some.inj hout
    subst out
    exact ⟨⟨_, hm.1, Or.inl rfl⟩, ⟨_, hm.1, Or.inr rfl⟩⟩
  · have heq := Option.some.inj hout
    subst out
    exact ⟨labelFarSequence_origin G c hc requests feasible fallback batch label hcard _,
      labelFarSequence_origin G c hc requests feasible fallback batch label hcard _⟩

end OnlineSteinerForest.UpperBound
