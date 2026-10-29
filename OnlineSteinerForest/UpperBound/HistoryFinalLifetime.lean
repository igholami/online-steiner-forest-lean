import OnlineSteinerForest.UpperBound.HistoryLabelUniqueness
import OnlineSteinerForest.UpperBound.HistoryLifetime
import OnlineSteinerForest.UpperBound.HistorySnapshotRequests

/-! Each persistent label has one final lifetime forest containing all its earlier snapshots. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical

noncomputable def snapshotFor (state : MergeHistory ℕ) (label : ℕ) : LabeledCluster ℕ :=
  if h : ∃ C, IsSnapshot state C ∧ C.label = label then Classical.choose h else ⟨label, ∅⟩

theorem snapshotFor_spec (state : MergeHistory ℕ) (label : ℕ)
    (h : ∃ C, IsSnapshot state C ∧ C.label = label) :
    IsSnapshot state (snapshotFor state label) ∧ (snapshotFor state label).label = label := by
  simp only [snapshotFor, dif_pos h]
  exact Classical.choose_spec h

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def finalLifetime (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (label : ℕ) : LabeledCluster ℕ :=
  snapshotFor (greedyHistory G c requests feasible requests.length) label

theorem finalLifetime_contains_snapshot (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (i : ℕ) (hi : i ≤ requests.length) (C : LabeledCluster ℕ)
    (hC : IsSnapshot (greedyHistory G c requests feasible i) C) :
    IsSnapshot (greedyHistory G c requests feasible requests.length)
      (finalLifetime G c requests feasible C.label) ∧
    C.members ⊆ (finalLifetime G c requests feasible C.label).members ∧
    clusterEdges G c requests feasible C ⊆
      clusterEdges G c requests feasible (finalLifetime G c requests feasible C.label) := by
  obtain ⟨D, hD, hl, hs⟩ := scanHistory_persists
    (fun j => 0 < blockPayment G c requests feasible j) (touchesBlock G c requests feasible)
    i requests.length hi C hC
  have hf := snapshotFor_spec (greedyHistory G c requests feasible requests.length) C.label ⟨D, hD, hl⟩
  have heq : finalLifetime G c requests feasible C.label = D :=
    greedyHistory_snapshot_label_unique G c requests feasible requests.length _ D hf.1 hD (hf.2.trans hl.symm)
  rw [heq]
  exact ⟨hD, hs, clusterEdges_mono_members G c requests feasible C D hs⟩

theorem finalLifetime_label (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (i : ℕ) (hi : i ≤ requests.length) (C : LabeledCluster ℕ)
    (hC : IsSnapshot (greedyHistory G c requests feasible i) C) :
    (finalLifetime G c requests feasible C.label).label = C.label := by
  obtain ⟨D, hD, hl, hs⟩ := scanHistory_persists
    (fun j => 0 < blockPayment G c requests feasible j) (touchesBlock G c requests feasible)
    i requests.length hi C hC
  exact (snapshotFor_spec _ C.label ⟨D, hD, hl⟩).2

/-- Assigned request endpoints remain connected inside their unique final lifetime forest. -/
theorem finalLifetime_requests_connected (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (i : ℕ) (hi : i ≤ requests.length)
    (C : LabeledCluster ℕ) (hC : IsSnapshot (greedyHistory G c requests feasible i) C)
    (a b : Fin requests.length) (ha : a.val ∈ C.members) (hb : b.val ∈ C.members) :
    let H := SimpleGraph.fromEdgeSet
      (clusterEdges G c requests feasible (finalLifetime G c requests feasible C.label) : Set (Sym2 V))
    H.Reachable requests[a.val].1 requests[b.val].1 ∧ H.Reachable requests[a.val].1 requests[b.val].2 := by
  have hs := (finalLifetime_contains_snapshot G c requests feasible i hi C hC).2.2
  have hr := snapshot_requests_connected G c hc requests feasible i hi C hC a b ha hb
  exact ⟨reachable_mono_edges hs hr.1, reachable_mono_edges hs hr.2⟩

end OnlineSteinerForest.UpperBound
