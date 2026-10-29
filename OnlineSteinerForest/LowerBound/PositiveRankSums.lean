import OnlineSteinerForest.LowerBound.BadPrice
import OnlineSteinerForest.LowerBound.PrefixBounds
import OnlineSteinerForest.LowerBound.InverseSquare

/-! Reindex finite positive-rank sums by their natural rank numbers. -/
namespace OnlineSteinerForest.LowerBound

variable [OnlineSteinerForest.PathSelection]

theorem sum_positiveRanks_eq_Icc (h : ℕ) (ha : 1 ≤ firstRank h) (f : ℕ → ℝ) :
    (∑ i ∈ positiveRanks h, f (i.val + 1)) =
      ∑ j ∈ Finset.Icc (firstRank h) (matchingSize h), f j := by
  classical
  refine Finset.sum_bij (fun i _ => i.val + 1) ?_ ?_ ?_ ?_
  · intro i hi
    have hia := (Finset.mem_filter.mp hi).2
    exact Finset.mem_Icc.mpr ⟨hia, by omega⟩
  · intro i _ j _ hij
    exact Fin.ext (by omega)
  · intro j hj
    obtain ⟨hja, hjm⟩ := Finset.mem_Icc.mp hj
    refine ⟨⟨j - 1, by omega⟩, ?_, by change j - 1 + 1 = j; omega⟩
    simp only [positiveRanks, Finset.mem_filter, Finset.mem_univ, true_and]
    change firstRank h ≤ j - 1 + 1
    omega
  · intro i hi
    rfl

theorem firstRank_ge_two (h : ℕ) (hh : 32 ≤ h) : 2 ≤ firstRank h := by
  have hc := Nat.le_ceil (prefixFraction h * matchingSize h)
  change prefixFraction h * matchingSize h ≤ (firstRank h : ℚ) at hc
  exact_mod_cast (prefix_mass_ge_two h hh).trans hc

theorem sum_inverse_square_Icc_le (a b : ℕ) (ha : 2 ≤ a) :
    (∑ j ∈ Finset.Icc a b, ((j : ℝ)⁻¹) ^ 2) ≤ (((a - 1 : ℕ) : ℝ)⁻¹) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  exact sum_inverse_square_range_le a (b + 1 - a) ha

end OnlineSteinerForest.LowerBound
