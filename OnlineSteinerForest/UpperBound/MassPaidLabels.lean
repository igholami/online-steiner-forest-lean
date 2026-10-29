import OnlineSteinerForest.UpperBound.MassLabelSum
import OnlineSteinerForest.UpperBound.MassGreedy
import OnlineSteinerForest.UpperBound.MassParameter
import OnlineSteinerForest.UpperBound.HistoryRequestLabels

/-! The mass budget indexed by the actual positive-payment request labels. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def paidLabels (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) : Finset ℕ :=
  (Finset.univ.filter (fun i : Fin requests.length => 0 < blockPayment G c requests feasible i.val)).image
    (fun i => pairLabel G c requests feasible i.val)

theorem paidLabels_snapshot_exists (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (label : ℕ) (hl : label ∈ paidLabels G c requests feasible) :
    ∃ C, IsSnapshot (greedyHistory G c requests feasible requests.length) C ∧ C.label = label := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hl
  have hp := (Finset.mem_filter.mp hi).2
  refine ⟨finalLifetime G c requests feasible (pairLabel G c requests feasible i.val), ?_, ?_⟩
  · exact (finalLifetime_contains_snapshot G c requests feasible (i.val + 1) (by omega)
      (requestCluster G c requests feasible i.val) (Or.inl (requestCluster_active G c requests feasible i.val hp))).1
  · exact finalLifetime_label G c requests feasible (i.val + 1) (by omega)
      (requestCluster G c requests feasible i.val) (Or.inl (requestCluster_active G c requests feasible i.val hp))

theorem sum_paid_label_mass (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) :
    ∑ label ∈ paidLabels G c requests feasible,
      clusterWeight (blockPayment G c requests feasible) (finalLifetime G c requests feasible label) ≤
      cycleFactor requests.length * greedyCost G c requests feasible := by
  have hm := sum_label_weights_le_mass (greedyHistory G c requests feasible requests.length)
    (scanHistory_archive_labels _ _ _) (paidLabels G c requests feasible)
    (blockPayment G c requests feasible) (paidLabels_snapshot_exists G c requests feasible) (by
      intro C hC
      exact Finset.sum_nonneg (fun a ha => blockPayment_nonneg G c hc requests feasible a))
  apply hm.trans
  rw [← lifetimeEdgeMass_eq]
  exact lifetimeEdgeMass_le_pairLog G c hc requests feasible

end OnlineSteinerForest.UpperBound
