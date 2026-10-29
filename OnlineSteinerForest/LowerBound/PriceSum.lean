import OnlineSteinerForest.LowerBound.Tests
import OnlineSteinerForest.LowerBound.Harmonic
import Mathlib.Tactic.FieldSimp

/-! Rewrite the actual rank-price sum as the harmonic tail in Section 5.3. -/
namespace OnlineSteinerForest.LowerBound

variable [OnlineSteinerForest.PathSelection]

theorem totalPrice_eq_sum_Icc (h : ℕ) :
    totalPrice h = ∑ i ∈ Finset.Icc 1 (matchingSize h), (price h i : ℝ) := by
  unfold totalPrice rankPrice
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (price h (i + 1) : ℝ)) (matchingSize h),
    Finset.range_eq_Ico,
    Finset.sum_Ico_add' (fun i : ℕ => (price h i : ℝ)) 0 (matchingSize h) 1]
  simp only [zero_add, Finset.Ico_add_one_right_eq_Icc]

theorem cast_price_of_ge (h i : ℕ) (hi : firstRank h ≤ i) :
    (price h i : ℝ) = (logSize h : ℝ) * matchingSize h / (1024 * i) := by
  rw [price_of_ge h i hi]
  push_cast
  norm_num

theorem totalPrice_eq_harmonic (h : ℕ) (ha : 1 ≤ firstRank h) :
    totalPrice h = (logSize h : ℝ) * matchingSize h / 1024 *
      ∑ i ∈ Finset.Icc (firstRank h) (matchingSize h), (i : ℝ)⁻¹ := by
  have hsub : Finset.Icc (firstRank h) (matchingSize h) ⊆ Finset.Icc 1 (matchingSize h) := by
    intro i hi
    exact Finset.mem_Icc.mpr ⟨ha.trans (Finset.mem_Icc.mp hi).1, (Finset.mem_Icc.mp hi).2⟩
  have hz : ∀ i ∈ Finset.Icc 1 (matchingSize h), i ∉ Finset.Icc (firstRank h) (matchingSize h) →
      (price h i : ℝ) = 0 := by
    intro i hi hn
    have hlt : i < firstRank h := by
      by_contra hnlt
      exact hn (Finset.mem_Icc.mpr ⟨Nat.le_of_not_gt hnlt, (Finset.mem_Icc.mp hi).2⟩)
    simp [price_of_lt h i hlt]
  rw [totalPrice_eq_sum_Icc, ← Finset.sum_subset hsub hz, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hia := (Finset.mem_Icc.mp hi).1
  have hip : (i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [cast_price_of_ge h i hia]
  field_simp

theorem totalPrice_ge_log (h : ℕ) (ha : 1 ≤ firstRank h)
    (hab : firstRank h ≤ matchingSize h + 1) :
    (logSize h : ℝ) * matchingSize h / 1024 *
      Real.log (((matchingSize h + 1 : ℕ) : ℝ) / firstRank h) ≤ totalPrice h := by
  rw [totalPrice_eq_harmonic h ha]
  exact mul_le_mul_of_nonneg_left (log_div_le_sum_inv _ _ (by omega) hab) (by positivity)

end OnlineSteinerForest.LowerBound
