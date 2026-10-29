import OnlineSteinerForest.LowerBound.PriceSum
import OnlineSteinerForest.LowerBound.LogPriceBounds

/-! First quantitative assertion of the manuscript's matching-existence lemma. -/
namespace OnlineSteinerForest.LowerBound

variable [OnlineSteinerForest.PathSelection]

theorem totalPrice_lower (h : ℕ) (hh : 32 ≤ h) :
    (vertexCount h : ℝ) * logSize h * h * Real.log 2 / 2 ^ 12 ≤ totalPrice h := by
  have ha : 1 ≤ firstRank h := firstRank_pos h hh
  have ht := totalPrice_ge_log h ha ((firstRank_le_matchingSize h hh).trans (Nat.le_succ _))
  have hlog := log_harmonic_tail_lower h hh
  calc
    _ = (logSize h : ℝ) * matchingSize h / 1024 * ((h : ℝ) * Real.log 2 / 2) := by
      rw [← twice_matchingSize h, Nat.cast_mul, Nat.cast_ofNat]
      ring
    _ ≤ (logSize h : ℝ) * matchingSize h / 1024 *
        Real.log (((matchingSize h + 1 : ℕ) : ℝ) / firstRank h) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ ≤ _ := ht

end OnlineSteinerForest.LowerBound
