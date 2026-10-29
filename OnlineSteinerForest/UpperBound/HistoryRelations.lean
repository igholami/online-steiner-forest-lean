import OnlineSteinerForest.UpperBound.HistoryScan

/-! Members of each live component remain related under any monotone connectivity relation. -/
namespace OnlineSteinerForest.UpperBound

open scoped Classical

/-- Union-by-size labels preserve graph-component membership. The relation
hypotheses are only equivalence, monotonicity, and the definition of a touch. -/
theorem scanHistory_members_related (enabled : ℕ → Prop)
    (touch : ℕ → LabeledCluster ℕ → Prop) (R : ℕ → ℕ → ℕ → Prop)
    (hR : ∀ i, Equivalence (R i))
    (hmono : ∀ i a b, R i a b → R (i + 1) a b)
    (htouch : ∀ i C, touch i C → R (i + 1) i C.label) (i : ℕ) :
    ∀ C ∈ (scanHistory enabled touch i).active,
      ∀ a ∈ C.members, ∀ b ∈ C.members, R i a b := by
  induction i with
  | zero => simp [scanHistory, MergeHistory.empty]
  | succ i ih =>
    intro C hC a ha b hb
    by_cases hi : enabled i
    · rw [scanHistory, if_pos hi] at hC
      rcases Finset.mem_insert.mp hC with rfl | hC
      · have hall : ∀ a ∈ (MergeHistory.merged i
            ((scanHistory enabled touch i).active.filter (touch i))).members, R (i + 1) a i := by
          intro a ha
          rcases Finset.mem_insert.mp ha with hai | ha
          · subst a
            exact (hR (i + 1)).refl i
          · obtain ⟨D, hD, haD⟩ := Finset.mem_biUnion.mp ha
            obtain ⟨hDa, hDt⟩ := Finset.mem_filter.mp hD
            have haLabel := ih D hDa a haD D.label
              ((scanHistory_invariant enabled touch i).partition.label_mem D hDa)
            exact (hR (i + 1)).trans (hmono i a D.label haLabel)
              ((hR (i + 1)).symm (htouch i D hDt))
        exact (hR (i + 1)).trans (hall a ha) ((hR (i + 1)).symm (hall b hb))
      · exact hmono i a b (ih C (Finset.mem_sdiff.mp hC).1 a ha b hb)
    · have hC' : C ∈ (scanHistory enabled touch i).active := by simpa [scanHistory, hi] using hC
      exact hmono i a b (ih C hC' a ha b hb)

end OnlineSteinerForest.UpperBound
