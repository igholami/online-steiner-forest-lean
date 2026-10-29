import OnlineSteinerForest.UpperBound.HistoryScan

/-! A label's component grows until retirement and its final lifetime is preserved. -/
namespace OnlineSteinerForest.UpperBound

variable {ι : Type*} [DecidableEq ι]

def IsSnapshot (state : MergeHistory ι) (C : LabeledCluster ι) : Prop :=
  C ∈ state.active ∨ C ∈ state.retired

/-- Every old component is either preserved, retired, or enlarged under its surviving label. -/
theorem snapshot_step_persists (state : MergeHistory ι) (new : ι)
    (touched : Finset (LabeledCluster ι)) (C : LabeledCluster ι) (hC : IsSnapshot state C) :
    ∃ D, IsSnapshot (MergeHistory.step state new touched) D ∧
      D.label = C.label ∧ C.members ⊆ D.members := by
  classical
  rcases hC with hC | hC
  · by_cases hCt : C ∈ touched
    · by_cases hl : C.label = MergeHistory.winner new touched
      · refine ⟨MergeHistory.merged new touched, Or.inl (MergeHistory.merged_mem_step _ _ _), ?_,
          MergeHistory.touched_subset_merged new touched C hCt⟩
        exact hl.symm
      · refine ⟨C, Or.inr ?_, rfl, Finset.Subset.refl _⟩
        apply List.mem_append_left
        exact Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨hCt, hl⟩)
    · exact ⟨C, Or.inl (MergeHistory.untouched_mem_step state new touched C hC hCt), rfl,
        Finset.Subset.refl _⟩
  · exact ⟨C, Or.inr (List.mem_append_right _ hC), rfl, Finset.Subset.refl _⟩

/-- At every later time, a label has a lifetime snapshot containing its earlier component. -/
theorem scanHistory_persists (enabled : ℕ → Prop)
    (touch : ℕ → LabeledCluster ℕ → Prop) (i j : ℕ) (hij : i ≤ j)
    (C : LabeledCluster ℕ) (hC : IsSnapshot (scanHistory enabled touch i) C) :
    ∃ D, IsSnapshot (scanHistory enabled touch j) D ∧ D.label = C.label ∧
      C.members ⊆ D.members := by
  classical
  induction j with
  | zero =>
    have hi : i = 0 := by omega
    subst i
    exact ⟨C, hC, rfl, Finset.Subset.refl _⟩
  | succ j ih =>
    by_cases heq : i = j + 1
    · subst i
      exact ⟨C, hC, rfl, Finset.Subset.refl _⟩
    · obtain ⟨D, hD, hlabel, hsub⟩ := ih (by omega)
      by_cases hj : enabled j
      · obtain ⟨E, hE, hEl, hDE⟩ := snapshot_step_persists (scanHistory enabled touch j) j
          ((scanHistory enabled touch j).active.filter (touch j)) D hD
        refine ⟨E, ?_, hEl.trans hlabel, hsub.trans hDE⟩
        simpa [scanHistory, hj] using hE
      · exact ⟨D, by simpa [scanHistory, hj] using hD, hlabel, hsub⟩

end OnlineSteinerForest.UpperBound
