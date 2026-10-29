import OnlineSteinerForest.LowerBound.RequestLogs

/-! Select a construction whose ambient path size straddles a requested exact length. -/
namespace OnlineSteinerForest.LowerBound
variable [OnlineSteinerForest.PathSelection.{0}]


theorem vertexCount_mono : Monotone vertexCount := by
  intro a b hab
  exact Nat.pow_le_pow_right (by decide)
    (Nat.pow_le_pow_right (by decide) hab)

theorem exists_padding_level (k : ℕ) (hk : vertexCount 32 ≤ k) :
    ∃ h : ℕ, 32 ≤ h ∧ vertexCount h ≤ k ∧ k < vertexCount (h + 1) := by
  have hex : ∃ t : ℕ, k < vertexCount t :=
    ⟨k, (show k < 2 ^ k from Nat.lt_two_pow_self).trans
      (show 2 ^ k < 2 ^ (2 ^ k) from Nat.lt_two_pow_self)⟩
  let t := Nat.find hex
  have ht : k < vertexCount t := Nat.find_spec hex
  have ht32 : 32 < t := by
    by_contra hn
    have := (vertexCount_mono (show t ≤ 32 by omega)).trans hk
    omega
  refine ⟨t - 1, by omega, ?_, ?_⟩
  · exact Nat.le_of_not_gt (Nat.find_min hex (show t - 1 < t by omega))
  · simpa only [Nat.sub_add_cancel (show 1 ≤ t by omega)] using ht

theorem padding_log_bounds (k h : ℕ) (hh : 32 ≤ h) (hk : vertexCount 32 ≤ k)
    (hupper : k < vertexCount (h + 1)) :
    0 ≤ Real.log k ∧ Real.log k ≤ 2 * (logSize h : ℝ) * Real.log 2 ∧
      Real.log (Real.log k) ≤ 2 * (h : ℝ) * Real.log 2 := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr ((vertexCount_pos 32).trans_le hk)
  have hklarge : 1 < k := lt_of_lt_of_le
    (show 1 < vertexCount 32 from (show 1 < vertexCount 1 by norm_num [vertexCount, logSize]).trans_le
      (vertexCount_mono (show 1 ≤ 32 by omega))) hk
  have hlogpos : 0 < Real.log k := Real.log_pos (Nat.one_lt_cast.mpr hklarge)
  have hlog := Real.log_le_log hkpos (Nat.cast_le.mpr hupper.le)
  have heq : logSize (h + 1) = 2 * logSize h := by simp [logSize, pow_succ]; omega
  simp only [vertexCount, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, heq,
    Nat.cast_mul] at hlog
  have hlogtwo : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num)
    linarith
  have hsimple : Real.log k ≤ (logSize (h + 1) : ℝ) := by
    rw [heq, Nat.cast_mul, Nat.cast_ofNat]
    exact hlog.trans (by nlinarith [show (0 : ℝ) ≤ logSize h from Nat.cast_nonneg _])
  have hll := Real.log_le_log hlogpos hsimple
  simp only [logSize, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at hll
  refine ⟨hlogpos.le, hlog, hll.trans ?_⟩
  have hhreal : (h : ℝ) + 1 ≤ 2 * h := by exact_mod_cast (show h + 1 ≤ 2 * h by omega)
  push_cast
  exact mul_le_mul_of_nonneg_right hhreal (Real.log_pos (by norm_num)).le

end OnlineSteinerForest.LowerBound
