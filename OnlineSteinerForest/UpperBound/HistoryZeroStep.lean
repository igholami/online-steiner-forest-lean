import OnlineSteinerForest.UpperBound.HistoryBlocks

/-! With positive input costs, zero-payment requests purchase no edges. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem purchasedBlock_nonempty_iff (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (i : Fin requests.length) :
    (purchasedBlock G c requests feasible i.val).Nonempty ↔ 0 < payment G c requests feasible i := by
  rw [← purchasedBlock_cost]
  constructor
  · intro hne
    exact Finset.sum_pos (fun e he => hc e (purchasedBlock_input G c requests feasible i.val e he)) hne
  · intro hpos
    by_contra h
    have he : purchasedBlock G c requests feasible i.val = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simpa [he, edgeCost] using hpos

theorem zero_payment_no_change (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (i : Fin requests.length)
    (hi : ¬ 0 < payment G c requests feasible i) :
    boughtBefore G c requests feasible (i.val + 1) = boughtBefore G c requests feasible i.val := by
  have he : purchasedBlock G c requests feasible i.val = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp (mt (purchasedBlock_nonempty_iff G c hc requests feasible i).mp hi)
  apply Finset.Subset.antisymm
  · exact Finset.sdiff_eq_empty_iff_subset.mp he
  · exact boughtBefore_mono G c requests feasible i.val (i.val + 1) (by omega)

end OnlineSteinerForest.UpperBound
