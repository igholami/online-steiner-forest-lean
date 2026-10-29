import OnlineSteinerForest.LowerBound.ExponentialPrefactor
import OnlineSteinerForest.LowerBound.PowerEstimates

/-! The polynomial-logarithmic factor is absorbed by the large vertex count. -/
namespace OnlineSteinerForest.LowerBound

variable [OnlineSteinerForest.PathSelection]

theorem logSize_mul_root_le_vertexCount (h : ℕ) (hh : 32 ≤ h) :
    (logSize h : ℝ) * (vertexCount h : ℝ) ^ (1 / 32 : ℝ) ≤ vertexCount h := by
  have hLpos : (0 : ℝ) < logSize h := Nat.cast_pos.mpr (logSize_pos h)
  have hNpos : (0 : ℝ) < vertexCount h := Nat.cast_pos.mpr (vertexCount_pos h)
  have hlogL : Real.log (logSize h : ℝ) = (h : ℝ) * Real.log 2 := by
    simp only [logSize, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  have hlogN : Real.log (vertexCount h : ℝ) = (logSize h : ℝ) * Real.log 2 := by
    simp only [vertexCount, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  have hlarge : (1024 : ℝ) * h ≤ logSize h := by exact_mod_cast scaled_linear_le_power h hh
  have hln : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hmul := mul_le_mul_of_nonneg_right hlarge hln
  have hhn := mul_nonneg (show (0 : ℝ) ≤ h from Nat.cast_nonneg _) hln
  calc
    _ = Real.exp (Real.log (logSize h : ℝ) + Real.log (vertexCount h : ℝ) * (1 / 32)) := by
      rw [Real.rpow_def_of_pos hNpos, Real.exp_add, Real.exp_log hLpos]
    _ ≤ Real.exp (Real.log (vertexCount h : ℝ)) := by
      apply Real.exp_le_exp.mpr
      rw [hlogL, hlogN]
      nlinarith
    _ = _ := Real.exp_log hNpos

end OnlineSteinerForest.LowerBound
