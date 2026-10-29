import OnlineSteinerForest.LowerBound.Probability.MeanWeight
import OnlineSteinerForest.LowerBound.Probability.SamplingMoment

/-! Sum all distinct rank assignments using the sampling-without-replacement inequality. -/
namespace OnlineSteinerForest.LowerBound.Probability

variable [OnlineSteinerForest.PathSelection]

open scoped Classical

abbrev RemainingRanks (h : ℕ) (i : Fin (matchingSize h)) :=
  {j : Fin (matchingSize h) // j ≠ i}

theorem card_remainingRanks (h : ℕ) (i : Fin (matchingSize h)) :
    Fintype.card (RemainingRanks h i) = (testRanks h i).card := by
  rw [Fintype.card_subtype]
  apply congrArg Finset.card
  ext j
  simp [testRanks]

theorem remaining_mean_eq (h : ℕ) (i : Fin (matchingSize h)) :
    (∑ j : RemainingRanks h i, shortcutWeight h i j.val) / Fintype.card (RemainingRanks h i) =
      meanShortcutWeight h i := by
  have hs : (∑ j : RemainingRanks h i, shortcutWeight h i j.val) =
      ∑ j ∈ testRanks h i, shortcutWeight h i j :=
    (Finset.sum_subtype (testRanks h i) (by intro j; simp [testRanks]) (shortcutWeight h i)).symm
  rw [hs, card_remainingRanks]
  rfl

theorem shortcut_assignment_sum_le (h : ℕ) (hh : 32 ≤ h) (i : Fin (matchingSize h))
    (hi : firstRank h ≤ i.val + 1) (q : ℕ) (hq : q + 1 ≤ matchingSize h) :
    (∑ ranks : Fin q ↪ RemainingRanks h i, ∏ j : Fin q, shortcutWeight h i (ranks j).val) ≤
      (matchingSize h : ℝ) ^ q * (2 * rankFraction h i) ^ q := by
  have hpop : 0 < Fintype.card (RemainingRanks h i) := by
    rw [card_remainingRanks]
    exact testRanks_card_pos h hh i
  let : Nonempty (RemainingRanks h i) := Fintype.card_pos_iff.mp hpop
  have hqpop : q ≤ Fintype.card (RemainingRanks h i) := by
    rw [card_remainingRanks, card_testRanks]
    omega
  have hm := sum_embedding_products_le (fun j : RemainingRanks h i => shortcutWeight h i j.val)
    (fun j => shortcutWeight_nonneg h i j.val) hqpop
  rw [remaining_mean_eq] at hm
  have hc : Fintype.card (RemainingRanks h i) ≤ matchingSize h := by
    rw [card_remainingRanks, card_testRanks]
    omega
  have hcount : ((Fintype.card (RemainingRanks h i)).descFactorial q : ℝ) ≤
      (matchingSize h : ℝ) ^ q := by
    calc
      _ ≤ (Fintype.card (RemainingRanks h i) : ℝ) ^ q := by
        exact_mod_cast Nat.descFactorial_le_pow (Fintype.card (RemainingRanks h i)) q
      _ ≤ _ := pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr hc) q
  have hmean := pow_le_pow_left₀ (meanShortcutWeight_nonneg h i) (meanShortcutWeight_le h hh i hi) q
  exact hm.trans (mul_le_mul hcount hmean
    (pow_nonneg (meanShortcutWeight_nonneg h i) q) (pow_nonneg (Nat.cast_nonneg _) q))

end OnlineSteinerForest.LowerBound.Probability
