import OnlineSteinerForest.UpperBound.MassHistoryAccounting

/-! A chronological implementation of persistent union-by-size labels. -/
namespace OnlineSteinerForest.UpperBound

open scoped Classical

/-- Process enabled request blocks chronologically. The graph-specific predicate
selects touched components; filtering ensures only active components are merged. -/
noncomputable def scanHistory (enabled : ℕ → Prop)
    (touch : ℕ → LabeledCluster ℕ → Prop) : ℕ → MergeHistory ℕ
  | 0 => MergeHistory.empty
  | i + 1 => if enabled i then
      MergeHistory.step (scanHistory enabled touch i) i
        ((scanHistory enabled touch i).active.filter (touch i))
    else scanHistory enabled touch i

noncomputable def scannedBlocks (enabled : ℕ → Prop) (i : ℕ) : Finset ℕ :=
  (Finset.range i).filter enabled

theorem scanHistory_invariant (enabled : ℕ → Prop)
    (touch : ℕ → LabeledCluster ℕ → Prop) (i : ℕ) :
    HistoryInvariant (scanHistory enabled touch i) (scannedBlocks enabled i) := by
  induction i with
  | zero => simpa [scanHistory, scannedBlocks] using HistoryInvariant.empty (ι := ℕ)
  | succ i ih =>
    by_cases hi : enabled i
    · have hfresh : i ∉ scannedBlocks enabled i := by simp [scannedBlocks]
      have hblocks : scannedBlocks enabled (i + 1) = insert i (scannedBlocks enabled i) := by
        simp [scannedBlocks, Finset.range_add_one, Finset.filter_insert, hi]
      rw [scanHistory, if_pos hi, hblocks]
      exact ih.step i hfresh _ (Finset.filter_subset _ _)
    · simpa [scanHistory, scannedBlocks, Finset.range_add_one, Finset.filter_insert, hi] using ih

/-- The proved mass budget for the chronological implementation itself. -/
theorem scanHistory_mass (enabled : ℕ → Prop)
    (touch : ℕ → LabeledCluster ℕ → Prop) (w : ℕ → ℝ)
    (hw : ∀ a, enabled a → 0 ≤ w a) (i : ℕ) :
    lifetimeMass (scanHistory enabled touch i) w ≤
      (((scannedBlocks enabled i).card.log2 : ℝ) + 1) *
        ∑ a ∈ scannedBlocks enabled i, w a := by
  apply lifetimeMass_le_log2 _ _ _ (scanHistory_invariant enabled touch i)
  intro a ha
  exact hw a (Finset.mem_filter.mp ha).2

end OnlineSteinerForest.UpperBound
