import OnlineSteinerForest.UpperBound.HistoryArchiveLabels
import OnlineSteinerForest.UpperBound.HistoryPersistence
import OnlineSteinerForest.UpperBound.HistoryGreedy

/-! A label names exactly one current or retired lifetime snapshot. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical

theorem scanHistory_archive_labels (enabled : ℕ → Prop)
    (touch : ℕ → LabeledCluster ℕ → Prop) (i : ℕ) :
    ArchiveLabels (scanHistory enabled touch i) := by
  induction i with
  | zero => exact ArchiveLabels.empty
  | succ i ih =>
    by_cases hi : enabled i
    · rw [scanHistory, if_pos hi]
      exact ih.step (scanHistory_invariant enabled touch i) i (by simp [scannedBlocks])
        _ (Finset.filter_subset _ _)
    · simpa [scanHistory, hi] using ih

theorem scanHistory_snapshot_label_unique (enabled : ℕ → Prop)
    (touch : ℕ → LabeledCluster ℕ → Prop) (i : ℕ) (C D : LabeledCluster ℕ)
    (hC : IsSnapshot (scanHistory enabled touch i) C)
    (hD : IsSnapshot (scanHistory enabled touch i) D) (heq : C.label = D.label) : C = D := by
  have h := scanHistory_archive_labels enabled touch i
  have hs := scanHistory_invariant enabled touch i
  rcases hC with hC | hC <;> rcases hD with hD | hD
  · exact hs.partition.labels_unique C D hC hD heq
  · exact False.elim (h.separated C hC D hD heq)
  · exact False.elim (h.separated D hD C hC heq.symm)
  · exact h.unique C hC D hD heq

theorem scanHistory_snapshot_label_mem (enabled : ℕ → Prop)
    (touch : ℕ → LabeledCluster ℕ → Prop) (i : ℕ) (C : LabeledCluster ℕ)
    (hC : IsSnapshot (scanHistory enabled touch i) C) : C.label ∈ C.members := by
  rcases hC with hC | hC
  · exact (scanHistory_invariant enabled touch i).partition.label_mem C hC
  · exact (scanHistory_archive_labels enabled touch i).label_mem C hC

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem greedyHistory_snapshot_label_unique (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (i : ℕ) (C D : LabeledCluster ℕ)
    (hC : IsSnapshot (greedyHistory G c requests feasible i) C)
    (hD : IsSnapshot (greedyHistory G c requests feasible i) D) (heq : C.label = D.label) : C = D :=
  scanHistory_snapshot_label_unique _ _ i C D hC hD heq

end OnlineSteinerForest.UpperBound
