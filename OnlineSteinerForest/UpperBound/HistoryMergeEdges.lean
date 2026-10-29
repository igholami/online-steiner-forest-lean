import OnlineSteinerForest.UpperBound.HistoryBlocks

/-! Union-by-size bookkeeping realizes the literal union of purchased edge blocks. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem merged_clusterEdges (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (i : ℕ) (touched : Finset (LabeledCluster ℕ)) :
    clusterEdges G c requests feasible (MergeHistory.merged i touched) =
      purchasedBlock G c requests feasible i ∪
        touched.biUnion (clusterEdges G c requests feasible) := by
  ext e
  simp only [clusterEdges, MergeHistory.merged, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_union]
  constructor
  · rintro ⟨j, hj, he⟩
    rcases hj with rfl | ⟨C, hC, hj⟩
    · exact Or.inl he
    · exact Or.inr ⟨C, hC, j, hj, he⟩
  · rintro (he | ⟨C, hC, j, hj, he⟩)
    · exact ⟨i, Or.inl rfl, he⟩
    · exact ⟨j, Or.inr ⟨C, hC, hj⟩, he⟩

/-- Any touched old snapshot is contained in the new snapshot as an actual input-edge set. -/
theorem touched_clusterEdges_subset (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (i : ℕ) (touched : Finset (LabeledCluster ℕ)) (C : LabeledCluster ℕ) (hC : C ∈ touched) :
    clusterEdges G c requests feasible C ⊆
      clusterEdges G c requests feasible (MergeHistory.merged i touched) := by
  rw [merged_clusterEdges]
  intro e he
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨C, hC, he⟩)

end OnlineSteinerForest.UpperBound
