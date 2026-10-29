import OnlineSteinerForest.UpperBound.HistoryPartition
import Lean.Elab.Tactic.Omega

/-! Losing a label at a maximum-size merge doubles every contained block's component size. -/
namespace OnlineSteinerForest.UpperBound

variable {ι : Type*} [DecidableEq ι]

namespace MergeHistory

theorem loser_doubles {active : Finset (LabeledCluster ι)} {U : Finset ι}
    (hp : ClusterPartition active U) (new : ι) (touched : Finset (LabeledCluster ι))
    (ht : touched ⊆ active) (C : LabeledCluster ι) (hC : C ∈ losers new touched) :
    2 * C.members.card ≤ (merged new touched).members.card := by
  classical
  have hC' := (Finset.mem_filter.mp hC).1
  have hne : touched.Nonempty := ⟨C, hC'⟩
  let D := chosen touched hne
  have hD : D ∈ touched := chosen_mem touched hne
  have hCD : C ≠ D := by
    intro heq
    have hl := (Finset.mem_filter.mp hC).2
    exact hl (heq ▸ (show D.label = winner new touched by simp [D, winner, hne]))
  have hd : Disjoint C.members D.members := hp.disjoint C (ht hC') D (ht hD) hCD
  have hsub : C.members ∪ D.members ⊆ (merged new touched).members :=
    Finset.union_subset (touched_subset_merged new touched C hC') (touched_subset_merged new touched D hD)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd] at hc
  have hm := chosen_max touched hne C hC'
  change C.members.card ≤ D.members.card at hm
  omega

theorem losers_eq_erase_chosen {active : Finset (LabeledCluster ι)} {U : Finset ι}
    (hp : ClusterPartition active U) (new : ι) (touched : Finset (LabeledCluster ι))
    (ht : touched ⊆ active) (hne : touched.Nonempty) :
    losers new touched = touched.erase (chosen touched hne) := by
  classical
  ext C
  simp only [losers, winner, dif_pos hne, Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨hC, hl⟩
    exact ⟨fun he => hl (congrArg LabeledCluster.label he), hC⟩
  · rintro ⟨hneC, hC⟩
    refine ⟨hC, ?_⟩
    intro hl
    exact hneC (hp.labels_unique C _ (ht hC) (ht (chosen_mem touched hne)) hl)

end MergeHistory
end OnlineSteinerForest.UpperBound
