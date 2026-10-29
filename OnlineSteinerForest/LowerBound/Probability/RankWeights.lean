import OnlineSteinerForest.LowerBound.Tests
import OnlineSteinerForest.LowerBound.PriceSum
import OnlineSteinerForest.LowerBound.PrefixBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp

/-! Exponential shortcut weights and the uniform bound for every later rank. -/
namespace OnlineSteinerForest.LowerBound.Probability

variable [OnlineSteinerForest.PathSelection]

noncomputable def rankFraction (h : ℕ) (i : Fin (matchingSize h)) : ℝ :=
  ((i.val + 1 : ℕ) : ℝ) / matchingSize h

noncomputable def shortcutWeight (h : ℕ) (i j : Fin (matchingSize h)) : ℝ :=
  Real.exp (-(16 * rankFraction h i) * testPrice h i j)

theorem rankFraction_pos (h : ℕ) (i : Fin (matchingSize h)) : 0 < rankFraction h i := by
  unfold rankFraction
  have hm : 0 < matchingSize h := Nat.zero_lt_of_lt i.isLt
  exact div_pos (by positivity) (Nat.cast_pos.mpr hm)

theorem rank_logSize_ge_prefix (h : ℕ) (i : Fin (matchingSize h))
    (hi : firstRank h ≤ i.val + 1) :
    (256 : ℚ) * h * matchingSize h ≤ ((i.val + 1 : ℕ) : ℚ) * logSize h := by
  have hc := Nat.le_ceil (prefixFraction h * matchingSize h)
  change prefixFraction h * matchingSize h ≤ (firstRank h : ℚ) at hc
  have hmass := hc.trans (Nat.cast_le.mpr hi)
  unfold prefixFraction at hmass
  norm_num at hmass
  rw [div_mul_eq_mul_div] at hmass
  norm_num only [Nat.cast_add, Nat.cast_one]
  exact (div_le_iff₀ (Nat.cast_pos.mpr (logSize_pos h))).mp hmass

theorem tilt_later_price_ge (h : ℕ) (i j : Fin (matchingSize h))
    (hi : firstRank h ≤ i.val + 1) (hij : i ≤ j) :
    4 * (h : ℝ) ≤ 16 * rankFraction h i * testPrice h i j := by
  have hb := (Rat.cast_le (K := ℝ)).mpr (rank_logSize_ge_prefix h i hi)
  simp only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] at hb
  have hm : (matchingSize h : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hjpos : (0 : ℝ) < ((j.val + 1 : ℕ) : ℝ) := by positivity
  have hjprefix : firstRank h ≤ j.val + 1 := hi.trans (by omega)
  unfold testPrice
  rw [ite_eq_right (not_lt_of_ge hij)]
  unfold rankPrice rankFraction
  rw [cast_price_of_ge h _ hjprefix]
  have heq : 16 * (((i.val + 1 : ℕ) : ℝ) / matchingSize h) *
      ((logSize h : ℝ) * matchingSize h / (1024 * ((j.val + 1 : ℕ) : ℝ))) =
      ((i.val + 1 : ℕ) : ℝ) * logSize h / (64 * ((j.val + 1 : ℕ) : ℝ)) := by
    field_simp
    ring
  rw [heq]
  apply (le_div_iff₀ (mul_pos (by norm_num) hjpos)).mpr
  have hidx : (((j.val + 1 : ℕ) : ℝ)) ≤ matchingSize h := Nat.cast_le.mpr (by omega)
  have hs := mul_le_mul_of_nonneg_left hidx (show (0 : ℝ) ≤ 256 * (h : ℝ) by positivity)
  nlinarith

@[simp] theorem shortcutWeight_earlier (h : ℕ) (i j : Fin (matchingSize h)) (hji : j < i) :
    shortcutWeight h i j = 1 := by simp [shortcutWeight, testPrice, hji]

theorem shortcutWeight_nonneg (h : ℕ) (i j : Fin (matchingSize h)) :
    0 ≤ shortcutWeight h i j := (Real.exp_pos _).le

theorem shortcutWeight_later_le (h : ℕ) (i j : Fin (matchingSize h))
    (hi : firstRank h ≤ i.val + 1) (hij : i ≤ j) :
    shortcutWeight h i j ≤ Real.exp (-4 * (h : ℝ)) := by
  apply Real.exp_le_exp.mpr
  nlinarith [tilt_later_price_ge h i j hi hij]

theorem exp_neg_four_le_inv_logSize (h : ℕ) :
    Real.exp (-4 * (h : ℝ)) ≤ (logSize h : ℝ)⁻¹ := by
  have hl : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at hh
    exact hh
  have hlog : -4 * (h : ℝ) ≤ -Real.log (logSize h : ℝ) := by
    simp only [logSize, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    nlinarith [mul_le_mul_of_nonneg_left hl (show (0 : ℝ) ≤ h from Nat.cast_nonneg _)]
  calc
    _ ≤ Real.exp (-Real.log (logSize h : ℝ)) := Real.exp_le_exp.mpr hlog
    _ = _ := by rw [Real.exp_neg, Real.exp_log (Nat.cast_pos.mpr (logSize_pos h))]

theorem inv_logSize_le_quarter_fraction (h : ℕ) (hh : 32 ≤ h)
    (i : Fin (matchingSize h)) (hi : firstRank h ≤ i.val + 1) :
    (logSize h : ℝ)⁻¹ ≤ rankFraction h i / 4 := by
  have hb := (Rat.cast_le (K := ℝ)).mpr (rank_logSize_ge_prefix h i hi)
  simp only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] at hb
  have hfac : (4 : ℝ) ≤ 256 * (h : ℝ) := by
    have hh' : (32 : ℝ) ≤ h := Nat.cast_le.mpr hh
    linarith
  have hs := mul_le_mul_of_nonneg_right hfac (show (0 : ℝ) ≤ matchingSize h from Nat.cast_nonneg _)
  have hm : (0 : ℝ) < matchingSize h := Nat.cast_pos.mpr (by omega)
  have hL : (0 : ℝ) < logSize h := Nat.cast_pos.mpr (logSize_pos h)
  calc
    _ = 1 / (logSize h : ℝ) := by simp [one_div]
    _ ≤ ((i.val + 1 : ℕ) : ℝ) / (4 * matchingSize h) :=
      (div_le_div_iff₀ hL (mul_pos (by norm_num) hm)).mpr (by nlinarith)
    _ = rankFraction h i / 4 := by unfold rankFraction; ring

end OnlineSteinerForest.LowerBound.Probability
