import OnlineSteinerForest.UpperBound.HistoryMerge

/-! Structural invariants of the implemented union-by-size analysis bookkeeping. -/
namespace OnlineSteinerForest.UpperBound

variable {ι : Type*} [DecidableEq ι]

/-- Active labeled clusters partition the request blocks processed so far. -/
structure ClusterPartition (active : Finset (LabeledCluster ι)) (U : Finset ι) : Prop where
  nonempty : ∀ C ∈ active, C.members.Nonempty
  disjoint : ∀ C ∈ active, ∀ D ∈ active, C ≠ D → Disjoint C.members D.members
  cover : active.biUnion LabeledCluster.members = U
  label_mem : ∀ C ∈ active, C.label ∈ C.members

namespace ClusterPartition

variable {active : Finset (LabeledCluster ι)} {U : Finset ι}

theorem member_subset (h : ClusterPartition active U) (C : LabeledCluster ι) (hC : C ∈ active) :
    C.members ⊆ U := by
  intro a ha
  rw [← h.cover]
  exact Finset.mem_biUnion.mpr ⟨C, hC, ha⟩

theorem labels_unique (h : ClusterPartition active U) (C D : LabeledCluster ι)
    (hC : C ∈ active) (hD : D ∈ active) (heq : C.label = D.label) : C = D := by
  by_contra hn
  exact Finset.disjoint_left.mp (h.disjoint C hC D hD hn) (h.label_mem C hC) (heq ▸ h.label_mem D hD)

theorem empty : ClusterPartition (∅ : Finset (LabeledCluster ι)) ∅ :=
  ⟨by simp, by simp, by simp, by simp⟩

theorem merged_disjoint_untouched (h : ClusterPartition active U) (new : ι) (hnew : new ∉ U)
    (touched : Finset (LabeledCluster ι)) (ht : touched ⊆ active)
    (C : LabeledCluster ι) (hC : C ∈ active) (hCt : C ∉ touched) :
    Disjoint (MergeHistory.merged new touched).members C.members := by
  apply Finset.disjoint_left.mpr
  intro a ha haC
  rcases Finset.mem_insert.mp ha with rfl | ha
  · exact hnew (h.member_subset C hC haC)
  · obtain ⟨D, hD, haD⟩ := Finset.mem_biUnion.mp ha
    have hDC : D ≠ C := by intro he; subst D; exact hCt hD
    exact Finset.disjoint_left.mp (h.disjoint D (ht hD) C hC hDC) haD haC

/-- A fresh block and any chosen subset of active components can be merged. -/
theorem step (h : ClusterPartition active U) (new : ι) (hnew : new ∉ U)
    (touched : Finset (LabeledCluster ι)) (ht : touched ⊆ active) (retired : List (LabeledCluster ι)) :
    ClusterPartition (MergeHistory.step ⟨active, retired⟩ new touched).active (insert new U) := by
  classical
  let M := MergeHistory.merged new touched
  constructor
  · intro C hC
    rcases Finset.mem_insert.mp hC with rfl | hC
    · exact ⟨new, MergeHistory.new_mem_merged new touched⟩
    · exact h.nonempty C (Finset.mem_sdiff.mp hC).1
  · intro C hC D hD hCD
    rcases Finset.mem_insert.mp hC with rfl | hC
    · have hD' := (Finset.mem_insert.mp hD).resolve_left (Ne.symm hCD)
      exact h.merged_disjoint_untouched new hnew touched ht D
        (Finset.mem_sdiff.mp hD').1 (Finset.mem_sdiff.mp hD').2
    · rcases Finset.mem_insert.mp hD with rfl | hD
      · exact (h.merged_disjoint_untouched new hnew touched ht C
          (Finset.mem_sdiff.mp hC).1 (Finset.mem_sdiff.mp hC).2).symm
      · exact h.disjoint C (Finset.mem_sdiff.mp hC).1 D (Finset.mem_sdiff.mp hD).1 hCD
  · ext a
    constructor
    · intro ha
      obtain ⟨C, hC, haC⟩ := Finset.mem_biUnion.mp ha
      rcases Finset.mem_insert.mp hC with rfl | hC
      · rcases Finset.mem_insert.mp haC with rfl | haC
        · exact Finset.mem_insert_self _ _
        · obtain ⟨D, hD, haD⟩ := Finset.mem_biUnion.mp haC
          exact Finset.mem_insert_of_mem (h.member_subset D (ht hD) haD)
      · exact Finset.mem_insert_of_mem (h.member_subset C (Finset.mem_sdiff.mp hC).1 haC)
    · intro ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact Finset.mem_biUnion.mpr ⟨M, Finset.mem_insert_self _ _, MergeHistory.new_mem_merged a touched⟩
      · rw [← h.cover] at ha
        obtain ⟨C, hC, haC⟩ := Finset.mem_biUnion.mp ha
        by_cases hCt : C ∈ touched
        · exact Finset.mem_biUnion.mpr ⟨M, Finset.mem_insert_self _ _,
            MergeHistory.touched_subset_merged new touched C hCt haC⟩
        · exact Finset.mem_biUnion.mpr ⟨C, Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨hC, hCt⟩), haC⟩
  · intro C hC
    rcases Finset.mem_insert.mp hC with rfl | hC
    · by_cases hne : touched.Nonempty
      · rw [MergeHistory.winner_label_of_nonempty new touched hne]
        exact MergeHistory.touched_subset_merged new touched _ (MergeHistory.chosen_mem touched hne)
          (h.label_mem _ (ht (MergeHistory.chosen_mem touched hne)))
      · have hw : (MergeHistory.merged new touched).label = new := by simp [MergeHistory.merged, MergeHistory.winner, hne]
        rw [hw]
        exact MergeHistory.new_mem_merged new touched
    · exact h.label_mem C (Finset.mem_sdiff.mp hC).1

end ClusterPartition
end OnlineSteinerForest.UpperBound
