import OnlineSteinerForest.LowerBound.Probability.RankWeights
import Mathlib.Order.Interval.Finset.Fin

/-! The average exponential weight of all remaining ranks is at most twice their prefix fraction. -/
namespace OnlineSteinerForest.LowerBound.Probability

variable [OnlineSteinerForest.PathSelection]

noncomputable def meanShortcutWeight (h : ℕ) (i : Fin (matchingSize h)) : ℝ :=
  (∑ j ∈ testRanks h i, shortcutWeight h i j) / (testRanks h i).card

@[simp] theorem card_testRanks (h : ℕ) (i : Fin (matchingSize h)) :
    (testRanks h i).card = matchingSize h - 1 := by
  simp [testRanks]

theorem testRanks_card_pos (h : ℕ) (hh : 32 ≤ h) (i : Fin (matchingSize h)) :
    0 < (testRanks h i).card := by
  have hp := scaled_linear_le_power h hh
  change 1024 * h ≤ logSize h at hp
  have hLm := logSize_le_matchingSize h
  rw [card_testRanks]
  omega

theorem sum_shortcutWeight_le (h : ℕ) (i : Fin (matchingSize h))
    (hi : firstRank h ≤ i.val + 1) :
    (∑ j ∈ testRanks h i, shortcutWeight h i j) ≤
      (i.val : ℝ) + (testRanks h i).card * Real.exp (-4 * (h : ℝ)) := by
  have hfree : (testRanks h i).filter (fun j => j < i) = Finset.Iio i := by
    ext j
    simp only [testRanks, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
      and_true, Finset.mem_Iio]
    exact ⟨fun hj => hj.2, fun hj => ⟨ne_of_lt hj, hj⟩⟩
  have hsfree : (∑ j ∈ testRanks h i, if j < i then (1 : ℝ) else 0) = i.val := by
    rw [← Finset.sum_filter, hfree]
    simp
  calc
    _ ≤ ∑ j ∈ testRanks h i, ((if j < i then (1 : ℝ) else 0) + Real.exp (-4 * (h : ℝ))) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hji : j < i
      · rw [shortcutWeight_earlier h i j hji]
        simp only [hji, ↓reduceIte]
        linarith [Real.exp_pos (-4 * (h : ℝ))]
      · simp only [hji, ↓reduceIte, zero_add]
        exact shortcutWeight_later_le h i j hi (le_of_not_gt hji)
    _ = _ := by rw [Finset.sum_add_distrib, hsfree]; simp [nsmul_eq_mul]

theorem meanShortcutWeight_nonneg (h : ℕ) (i : Fin (matchingSize h)) :
    0 ≤ meanShortcutWeight h i :=
  div_nonneg (Finset.sum_nonneg (fun j _ => shortcutWeight_nonneg h i j)) (Nat.cast_nonneg _)

theorem meanShortcutWeight_le (h : ℕ) (hh : 32 ≤ h) (i : Fin (matchingSize h))
    (hi : firstRank h ≤ i.val + 1) : meanShortcutWeight h i ≤ 2 * rankFraction h i := by
  have hcard := testRanks_card_pos h hh i
  have hM : (0 : ℝ) < matchingSize h := Nat.cast_pos.mpr (Nat.zero_lt_of_lt i.isLt)
  have hcardeq : ((testRanks h i).card : ℝ) = (matchingSize h : ℝ) - 1 := by
    rw [card_testRanks, Nat.cast_sub (show 1 ≤ matchingSize h by omega), Nat.cast_one]
  have hidx : (i.val : ℝ) + 1 ≤ matchingSize h := by
    exact_mod_cast Nat.succ_le_of_lt i.isLt
  have hfree : (i.val : ℝ) ≤ rankFraction h i * (testRanks h i).card := by
    unfold rankFraction
    rw [hcardeq, div_mul_eq_mul_div]
    apply (le_div_iff₀ hM).mpr
    push_cast
    nlinarith
  have hstep : meanShortcutWeight h i ≤ rankFraction h i + Real.exp (-4 * (h : ℝ)) := by
    unfold meanShortcutWeight
    apply (div_le_iff₀ (Nat.cast_pos.mpr hcard)).mpr
    nlinarith [sum_shortcutWeight_le h i hi]
  have he := (exp_neg_four_le_inv_logSize h).trans (inv_logSize_le_quarter_fraction h hh i hi)
  have hfrac := rankFraction_pos h i
  linarith

end OnlineSteinerForest.LowerBound.Probability
