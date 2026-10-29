import OnlineSteinerForest.UpperBound.HistoryInvariant

/-! A retired label never reappears and identifies a unique lifetime snapshot. -/
namespace OnlineSteinerForest.UpperBound

variable {ι : Type*} [DecidableEq ι]

structure ArchiveLabels (state : MergeHistory ι) : Prop where
  label_mem : ∀ C ∈ state.retired, C.label ∈ C.members
  separated : ∀ C ∈ state.active, ∀ D ∈ state.retired, C.label ≠ D.label
  unique : ∀ C ∈ state.retired, ∀ D ∈ state.retired, C.label = D.label → C = D

namespace ArchiveLabels

open MergeHistory

theorem empty : ArchiveLabels (MergeHistory.empty : MergeHistory ι) := by
  constructor <;> simp [MergeHistory.empty]

theorem winner_ne_retired {state : MergeHistory ι} {U : Finset ι}
    (h : ArchiveLabels state) (hs : HistoryInvariant state U) (new : ι) (hnew : new ∉ U)
    (touched : Finset (LabeledCluster ι)) (ht : touched ⊆ state.active)
    (D : LabeledCluster ι) (hD : D ∈ state.retired) : winner new touched ≠ D.label := by
  classical
  by_cases hn : touched.Nonempty
  · simpa [winner, hn] using h.separated (chosen touched hn) (ht (chosen_mem touched hn)) D hD
  · simp only [winner, dif_neg hn]
    intro heq
    exact hnew (heq ▸ hs.archive D hD (h.label_mem D hD))

theorem step {state : MergeHistory ι} {U : Finset ι}
    (h : ArchiveLabels state) (hs : HistoryInvariant state U) (new : ι) (hnew : new ∉ U)
    (touched : Finset (LabeledCluster ι)) (ht : touched ⊆ state.active) :
    ArchiveLabels (MergeHistory.step state new touched) := by
  classical
  have hlos : ∀ C ∈ losers new touched, C ∈ state.active :=
    fun C hC => ht (Finset.mem_filter.mp hC).1
  have hret : ∀ C, C ∈ (MergeHistory.step state new touched).retired ↔
      C ∈ losers new touched ∨ C ∈ state.retired := by
    intro C
    simp only [MergeHistory.step, List.mem_append, Finset.mem_toList]
  constructor
  · intro C hC
    rcases (hret C).mp hC with hC | hC
    · exact hs.partition.label_mem C (hlos C hC)
    · exact h.label_mem C hC
  · intro C hC D hD
    rcases Finset.mem_insert.mp hC with rfl | hC
    · rcases (hret D).mp hD with hD | hD
      · exact Ne.symm (Finset.mem_filter.mp hD).2
      · exact h.winner_ne_retired hs new hnew touched ht D hD
    · have hCa := (Finset.mem_sdiff.mp hC).1
      have hCt := (Finset.mem_sdiff.mp hC).2
      rcases (hret D).mp hD with hD | hD
      · intro heq
        have he : C = D := hs.partition.labels_unique C D hCa (hlos D hD) heq
        exact hCt (he ▸ (Finset.mem_filter.mp hD).1)
      · exact h.separated C hCa D hD
  · intro C hC D hD heq
    rcases (hret C).mp hC with hC | hC <;> rcases (hret D).mp hD with hD | hD
    · exact hs.partition.labels_unique C D (hlos C hC) (hlos D hD) heq
    · exact False.elim (h.separated C (hlos C hC) D hD heq)
    · exact False.elim (h.separated D (hlos D hD) C hC heq.symm)
    · exact h.unique C hC D hD heq

end ArchiveLabels
end OnlineSteinerForest.UpperBound
