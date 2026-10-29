import OnlineSteinerForest.UpperBound.HistoryRetirements

/-! Algorithmic depth invariant for union-by-size lifetime snapshots. -/
namespace OnlineSteinerForest.UpperBound

variable {ι : Type*} [DecidableEq ι]

/-- Only structural partition and geometric-depth properties are stored here;
all are proved for the initial state and every fresh union-by-size update. -/
structure HistoryInvariant (state : MergeHistory ι) (U : Finset ι) : Prop where
  partition : ClusterPartition state.active U
  archive : ∀ C ∈ state.retired, C.members ⊆ U
  depth : ∀ C ∈ state.active, ∀ a ∈ C.members,
    2 ^ MergeHistory.retirementCount state a ≤ C.members.card

namespace HistoryInvariant

open MergeHistory

theorem empty : HistoryInvariant (MergeHistory.empty : MergeHistory ι) ∅ :=
  ⟨ClusterPartition.empty, by simp [MergeHistory.empty], by simp [MergeHistory.empty]⟩

theorem step_archive_old {state : MergeHistory ι} {U : Finset ι} (h : HistoryInvariant state U)
    (new : ι) (touched : Finset (LabeledCluster ι)) (ht : touched ⊆ state.active) :
    ∀ C ∈ (MergeHistory.step state new touched).retired, C.members ⊆ U := by
  intro C hC
  rcases List.mem_append.mp hC with hC | hC
  · exact h.partition.member_subset C (ht (Finset.mem_filter.mp (Finset.mem_toList.mp hC)).1)
  · exact h.archive C hC

/-- Every update performed by the analysis bookkeeping maintains its actual depth bound. -/
theorem step {state : MergeHistory ι} {U : Finset ι} (h : HistoryInvariant state U)
    (new : ι) (hnew : new ∉ U) (touched : Finset (LabeledCluster ι)) (ht : touched ⊆ state.active) :
    HistoryInvariant (MergeHistory.step state new touched) (insert new U) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · exact h.partition.step new hnew touched ht state.retired
  · intro C hC
    exact (h.step_archive_old new touched ht C hC).trans (Finset.subset_insert _ _)
  · intro C hC a ha
    rcases Finset.mem_insert.mp hC with rfl | hC
    · by_cases hanew : a = new
      · subst a
        have hc : retirementCount (MergeHistory.step state new touched) new = 0 :=
          retirementCount_zero_of_fresh _ U (h.step_archive_old new touched ht) new hnew
        rw [hc]
        exact (Finset.card_pos.mpr ⟨new, new_mem_merged new touched⟩)
      · obtain ⟨D, hD, haD⟩ := Finset.mem_biUnion.mp ((Finset.mem_insert.mp ha).resolve_left hanew)
        have hdepth := h.depth D (ht hD) a haD
        have hcount := retirementCount_step h.partition state.retired new touched ht D (ht hD) a haD
        by_cases hDl : D ∈ losers new touched
        · rw [hcount, if_pos hDl, pow_succ]
          have hdouble := loser_doubles h.partition new touched ht D hDl
          exact (Nat.mul_le_mul_right 2 hdepth).trans (by simpa [Nat.mul_comm] using hdouble)
        · rw [hcount, if_neg hDl, Nat.add_zero]
          exact hdepth.trans (Finset.card_le_card (touched_subset_merged new touched D hD))
    · have hCa := (Finset.mem_sdiff.mp hC).1
      have hCt := (Finset.mem_sdiff.mp hC).2
      have hCl : C ∉ losers new touched := by
        intro hCl
        exact hCt (Finset.mem_filter.mp hCl).1
      rw [retirementCount_step h.partition state.retired new touched ht C hCa a ha, if_neg hCl, Nat.add_zero]
      exact h.depth C hCa a ha

theorem retirementCount_le_log2 {state : MergeHistory ι} {U : Finset ι}
    (h : HistoryInvariant state U) (a : ι) (ha : a ∈ U) :
    MergeHistory.retirementCount state a ≤ U.card.log2 := by
  rw [← h.partition.cover] at ha
  obtain ⟨C, hC, haC⟩ := Finset.mem_biUnion.mp ha
  have hpow := (h.depth C hC a haC).trans (Finset.card_le_card (h.partition.member_subset C hC))
  apply (Nat.le_log2 (Finset.card_ne_zero.mpr ⟨C.label, h.partition.member_subset C hC (h.partition.label_mem C hC)⟩)).mpr
  exact hpow

end HistoryInvariant
end OnlineSteinerForest.UpperBound
