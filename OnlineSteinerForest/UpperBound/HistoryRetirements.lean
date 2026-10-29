import OnlineSteinerForest.UpperBound.HistoryDoubling

/-! Count the retired lifetime snapshots containing an individual positive-payment block. -/
namespace OnlineSteinerForest.UpperBound

variable {ι : Type*} [DecidableEq ι]

namespace MergeHistory

noncomputable def retirementCount (state : MergeHistory ι) (a : ι) : ℕ :=
  (state.retired.filter (fun C => decide (a ∈ C.members))).length

theorem retirementCount_zero_of_fresh (state : MergeHistory ι) (U : Finset ι)
    (harchive : ∀ C ∈ state.retired, C.members ⊆ U) (a : ι) (ha : a ∉ U) :
    retirementCount state a = 0 := by
  rw [retirementCount, List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro C hC
  simpa only [decide_eq_true_eq] using (fun hmem => ha (harchive C hC hmem))

theorem losers_filter_owner {active : Finset (LabeledCluster ι)} {U : Finset ι}
    (hp : ClusterPartition active U) (new : ι) (touched : Finset (LabeledCluster ι))
    (ht : touched ⊆ active) (C : LabeledCluster ι) (hC : C ∈ active) (a : ι) (ha : a ∈ C.members) :
    (losers new touched).filter (fun D => a ∈ D.members) =
      if C ∈ losers new touched then {C} else ∅ := by
  classical
  have howner : ∀ D ∈ losers new touched, a ∈ D.members → D = C := by
    intro D hD haD
    by_contra hDC
    have hDa : D ∈ active := ht (Finset.mem_filter.mp hD).1
    exact Finset.disjoint_left.mp (hp.disjoint D hDa C hC hDC) haD ha
  by_cases hCl : C ∈ losers new touched
  · rw [if_pos hCl]
    ext D
    constructor
    · intro hD
      exact Finset.mem_singleton.mpr (howner D (Finset.mem_filter.mp hD).1 (Finset.mem_filter.mp hD).2)
    · intro hD
      have heq := Finset.mem_singleton.mp hD
      subst D
      exact Finset.mem_filter.mpr ⟨hCl, ha⟩
  · rw [if_neg hCl]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro D hD
    have heq := howner D (Finset.mem_filter.mp hD).1 (Finset.mem_filter.mp hD).2
    exact hCl (heq ▸ (Finset.mem_filter.mp hD).1)

theorem retirementCount_step {active : Finset (LabeledCluster ι)} {U : Finset ι}
    (hp : ClusterPartition active U) (retired : List (LabeledCluster ι))
    (new : ι) (touched : Finset (LabeledCluster ι)) (ht : touched ⊆ active)
    (C : LabeledCluster ι) (hC : C ∈ active) (a : ι) (ha : a ∈ C.members) :
    retirementCount (step ⟨active, retired⟩ new touched) a =
      retirementCount ⟨active, retired⟩ a + if C ∈ losers new touched then 1 else 0 := by
  classical
  have hlen : ((losers new touched).toList.filter (fun D => decide (a ∈ D.members))).length =
      ((losers new touched).filter (fun D => a ∈ D.members)).card := by
    rw [← List.toFinset_card_of_nodup ((Finset.nodup_toList _).filter _), List.toFinset_filter]
    simp only [Finset.toList_toFinset, decide_eq_true_eq]
  simp only [retirementCount, step, List.filter_append, List.length_append]
  rw [hlen, losers_filter_owner hp new touched ht C hC a ha]
  split_ifs <;> simp <;> omega

end MergeHistory
end OnlineSteinerForest.UpperBound
