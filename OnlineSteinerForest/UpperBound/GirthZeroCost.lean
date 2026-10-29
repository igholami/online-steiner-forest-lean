import OnlineSteinerForest.UpperBound.GirthMinimumDegree

/-! Removing the positive-total-cost restriction from the weighted short-cycle lemma. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*} [Fintype V] [Fintype I] [DecidableEq I] [DecidableEq V] [Nonempty I]

theorem minimum_degree_short_cycle_nonneg (left right : I → V)
    (hdegree : ∀ v, 3 ≤ degree left right v) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (n : ℕ) (hn : 2 * (Fintype.card V : ℝ) < (2 : ℝ) ^ n) :
    ∃ z, ∃ c : (edgeSubdivision left right).Walk z z, c.IsCycle ∧
      (c.edges.map (subdivisionCost w)).sum ≤
        4 * (n + 1 : ℕ) * (∑ i, w i) / Fintype.card I := by
  by_cases hC : 0 < ∑ i, w i
  · exact minimum_degree_short_cycle left right hdegree w hw hC n hn
  · have hzero : ∑ i, w i = 0 := le_antisymm (le_of_not_gt hC)
      (Finset.sum_nonneg (by intro i _; exact hw i))
    have hwzero : ∀ i, w i = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg (by intro i _; exact hw i)).mp hzero i (Finset.mem_univ i)
    have hunit : 0 < ∑ _i : I, (1 : ℝ) := by simp; positivity
    obtain ⟨z, c, hc, _⟩ := minimum_degree_short_cycle left right hdegree
      (fun _ => 1) (by intro; norm_num) hunit n hn
    refine ⟨z, c, hc, ?_⟩
    have hwfun : w = fun _ => 0 := funext hwzero
    rw [hwfun]
    have hz : subdivisionCost (V := V) (fun _ : I => (0 : ℝ)) = fun _ => 0 := by
      funext e
      induction e using Sym2.inductionOn with
      | _ a b => cases a <;> cases b <;> simp [subdivisionCost]
    rw [hz]
    simp

end OnlineSteinerForest.UpperBound.Girth
