import OnlineSteinerForest.UpperBound.HistoryScan
import OnlineSteinerForest.UpperBound.HistoryPayments

/-! Persistent labels computed from the implemented greedy purchased graphs. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Totalized chronological payment; indices outside the request list have weight zero. -/
noncomputable def blockPayment (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (i : ℕ) : ℝ :=
  if hi : i < requests.length then payment G c requests feasible ⟨i, hi⟩ else 0

/-- An existing block component is touched exactly when its representative joins
this request's source in the newly purchased graph. -/
noncomputable def touchesBlock (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (i : ℕ) (C : LabeledCluster ℕ) : Prop :=
  ∃ hi : i < requests.length, ∃ hC : C.label < requests.length,
    (SimpleGraph.fromEdgeSet (boughtBefore G c requests feasible (i + 1) : Set (Sym2 V))).Reachable
      requests[i].1 requests[C.label].1

noncomputable def greedyHistory (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) : ℕ → MergeHistory ℕ :=
  scanHistory (fun i => 0 < blockPayment G c requests feasible i)
    (touchesBlock G c requests feasible)

theorem blockPayment_nonneg (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (i : ℕ) :
    0 ≤ blockPayment G c requests feasible i := by
  unfold blockPayment
  split_ifs with hi
  · exact payment_nonneg G c hc requests feasible ⟨i, hi⟩
  · exact le_rfl

theorem greedyHistory_invariant (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (i : ℕ) :
    HistoryInvariant (greedyHistory G c requests feasible i)
      (scannedBlocks (fun j => 0 < blockPayment G c requests feasible j) i) :=
  scanHistory_invariant _ _ i

theorem sum_blockPayments (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) :
    ∑ i ∈ Finset.range requests.length, blockPayment G c requests feasible i =
      greedyCost G c requests feasible := by
  rw [← Fin.sum_univ_eq_sum_range]
  have heq : (fun i : Fin requests.length => blockPayment G c requests feasible i.val) =
      (fun i => payment G c requests feasible i) := by
    funext i
    simp [blockPayment, i.isLt]
  rw [heq, sum_payments_eq_greedyCost]

end OnlineSteinerForest.UpperBound
