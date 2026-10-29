import OnlineSteinerForest.LowerBound.PrefixBounds
import OnlineSteinerForest.LowerBound.PriceSum

/-! Every tested positive price is at most the manuscript's `L^2` pattern cutoff. -/
namespace OnlineSteinerForest.LowerBound

variable [OnlineSteinerForest.PathSelection]

theorem rank_times_logSize_ge_matchingSize (h : ℕ) (hh : 32 ≤ h)
    (i : Fin (matchingSize h)) (hi : firstRank h ≤ i.val + 1) :
    (matchingSize h : ℚ) ≤ ((i.val + 1 : ℕ) : ℚ) * logSize h := by
  have hL : (0 : ℚ) < logSize h := Nat.cast_pos.mpr (logSize_pos h)
  have hc := Nat.le_ceil (prefixFraction h * matchingSize h)
  change prefixFraction h * matchingSize h ≤ (firstRank h : ℚ) at hc
  have hidx : (firstRank h : ℚ) ≤ ((i.val + 1 : ℕ) : ℚ) := Nat.cast_le.mpr hi
  have hmass := hc.trans hidx
  unfold prefixFraction at hmass
  rw [div_mul_eq_mul_div] at hmass
  have hm := (div_le_iff₀ hL).mp hmass
  have hfac : (1 : ℚ) ≤ 2 ^ 8 * h := by
    have hh' : (32 : ℚ) ≤ h := Nat.cast_le.mpr hh
    norm_num
    linarith
  have hm' : (matchingSize h : ℚ) ≤ 2 ^ 8 * h * matchingSize h := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hfac (show (0 : ℚ) ≤ matchingSize h from Nat.cast_nonneg _)
  exact hm'.trans hm

theorem rankPrice_le_logSize_sq (h : ℕ) (hh : 32 ≤ h)
    (i : Fin (matchingSize h)) (hi : firstRank h ≤ i.val + 1) :
    rankPrice h i ≤ (logSize h : ℝ) ^ 2 := by
  have hb := (Rat.cast_le (K := ℝ)).mpr (rank_times_logSize_ge_matchingSize h hh i hi)
  simp only [Rat.cast_mul, Rat.cast_natCast] at hb
  have hmul := mul_le_mul_of_nonneg_left hb (show (0 : ℝ) ≤ logSize h from Nat.cast_nonneg _)
  unfold rankPrice
  rw [cast_price_of_ge h _ hi]
  apply (div_le_iff₀ (show (0 : ℝ) < 1024 * ((i.val + 1 : ℕ) : ℝ) by positivity)).mpr
  have hp := mul_nonneg (show (0 : ℝ) ≤ ((i.val + 1 : ℕ) : ℝ) from Nat.cast_nonneg _)
    (sq_nonneg (logSize h : ℝ))
  nlinarith

end OnlineSteinerForest.LowerBound
