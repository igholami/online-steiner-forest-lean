import OnlineSteinerForest.UpperBound.HistoryFinalLifetime
import OnlineSteinerForest.UpperBound.NearestNeighborDistances

/-! Summing distinct label lifetimes uses at most the proved snapshot mass budget. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical

theorem sum_label_weights_le_mass (state : MergeHistory ℕ) (ha : ArchiveLabels state)
    (labels : Finset ℕ) (w : ℕ → ℝ)
    (hlabels : ∀ l ∈ labels, ∃ C, IsSnapshot state C ∧ C.label = l)
    (hw : ∀ C, IsSnapshot state C → 0 ≤ clusterWeight w C) :
    ∑ l ∈ labels, clusterWeight w (snapshotFor state l) ≤ lifetimeMass state w := by
  let family := state.active ∪ state.retired.toFinset
  let chosen := labels.image (snapshotFor state)
  have hinj : ∀ a ∈ labels, ∀ b ∈ labels, snapshotFor state a = snapshotFor state b → a = b := by
    intro a ha b hb heq
    have hA := (snapshotFor_spec state a (hlabels a ha)).2
    have hB := (snapshotFor_spec state b (hlabels b hb)).2
    exact hA.symm.trans ((congrArg LabeledCluster.label heq).trans hB)
  have hsub : chosen ⊆ family := by
    intro C hC
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hC
    rcases (snapshotFor_spec state l (hlabels l hl)).1 with hC | hC
    · exact Finset.mem_union_left _ hC
    · exact Finset.mem_union_right _ (List.mem_toFinset.mpr hC)
  have hsum : (∑ l ∈ labels, clusterWeight w (snapshotFor state l)) = ∑ C ∈ chosen, clusterWeight w C := by
    exact (Finset.sum_image hinj).symm
  have hfamily : ∀ C ∈ family, IsSnapshot state C := by
    intro C hC
    rcases Finset.mem_union.mp hC with hC | hC
    · exact Or.inl hC
    · exact Or.inr (List.mem_toFinset.mp hC)
  have hdis : Disjoint state.active state.retired.toFinset := by
    apply Finset.disjoint_left.mpr
    intro C hC hCr
    exact ha.separated C hC C (List.mem_toFinset.mp hCr) rfl
  have hlist := sum_toFinset_le_sum_map state.retired (clusterWeight w)
    (fun C hC => hw C (Or.inr hC))
  rw [hsum]
  calc
    _ ≤ ∑ C ∈ family, clusterWeight w C :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun C hC _ => hw C (hfamily C hC))
    _ = (∑ C ∈ state.active, clusterWeight w C) + ∑ C ∈ state.retired.toFinset, clusterWeight w C :=
      Finset.sum_union hdis
    _ ≤ lifetimeMass state w := by
      unfold lifetimeMass
      linarith

end OnlineSteinerForest.UpperBound
