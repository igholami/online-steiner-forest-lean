import OnlineSteinerForest.UpperBound.FinalConstants

/-! Uniform natural-log bounds for every factor in the manuscript's final accounting. -/
namespace OnlineSteinerForest.UpperBound

theorem pair_log_ge (k : ℕ) (hk : 1 ≤ k) : Real.log 2 ≤ Real.log (2 * k) := by
  exact Real.log_le_log (by norm_num) (by exact_mod_cast Nat.mul_le_mul_left 2 hk)

theorem iterated_log_ge (k : ℕ) (hk : 1 ≤ k) :
    iteratedLogFloor ≤ Real.log (Real.log (4 * k)) := by
  have h4 : Real.log 4 ≤ Real.log (4 * (k : ℝ)) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast Nat.mul_le_mul_left 4 hk)
  exact Real.log_le_log (Real.log_pos (by norm_num)) h4

theorem log_cycleFactor_le (k : ℕ) (hk : 1 ≤ k) :
    Real.log (cycleFactor k) ≤ Real.log pairLogConstant + Real.log (Real.log (4 * k)) := by
  have hLpos : (0 : ℝ) < cycleFactor k := Nat.cast_pos.mpr (cycleFactor_pos k)
  have hspos : 0 < Real.log (2 * (k : ℝ)) := lt_of_lt_of_le log_two_pos (pair_log_ge k hk)
  have hlog := Real.log_le_log hLpos (cycleFactor_le_pair_log k hk)
  have ha := pairLogConstant_pos
  change Real.log (cycleFactor k) ≤ Real.log (pairLogConstant * Real.log (2 * (k : ℝ))) at hlog
  rw [Real.log_mul ha.ne' hspos.ne'] at hlog
  have hs4 : Real.log (2 * (k : ℝ)) ≤ Real.log (4 * k) :=
    Real.log_le_log (by positivity) (by nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))])
  exact hlog.trans (add_le_add le_rfl (Real.log_le_log hspos hs4))

/-- Absorb a fixed nonnegative additive constant into a positive logarithm. -/
theorem absorb_affine_constant (a d b t : ℝ) (ha : 0 ≤ a) (hb : 0 < b) (ht : b ≤ t) :
    a + d * t ≤ (a / b + d) * t := by
  have hh : a ≤ a / b * t := by
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hb).mpr (mul_le_mul_of_nonneg_left ht ha)
  nlinarith

theorem batchClassCount_le_iterated_log (k : ℕ) (hk : 1 ≤ k) :
    (batchClassCount k : ℝ) ≤ classLogConstant * Real.log (Real.log (4 * k)) := by
  let t := Real.log (Real.log (4 * (k : ℝ)))
  have ht : iteratedLogFloor ≤ t := iterated_log_ge k hk
  have hlog := log_cycleFactor_le k hk
  have hbase : (batchClassCount k : ℝ) ≤
      (29 + 5 * Real.log pairLogConstant / Real.log 2) + (5 / Real.log 2) * t := by
    have hh := mul_le_mul_of_nonneg_left hlog
      (show 0 ≤ 5 / Real.log 2 from div_nonneg (by norm_num) log_two_pos.le)
    calc
      _ ≤ 29 + 5 * Real.log (cycleFactor k) / Real.log 2 := batchClassCount_le_log k hk
      _ = 29 + (5 / Real.log 2) * Real.log (cycleFactor k) := by ring
      _ ≤ 29 + (5 / Real.log 2) * (Real.log pairLogConstant + t) := add_le_add le_rfl hh
      _ = _ := by ring
  have ha : 0 ≤ 29 + 5 * Real.log pairLogConstant / Real.log 2 := by
    have h := log_pairLogConstant_pos
    have h2 := log_two_pos
    positivity
  exact hbase.trans (absorb_affine_constant _ _ _ _ ha iteratedLogFloor_pos ht)

theorem cycleFactor_cycleFactor_le_iterated_log (k : ℕ) (hk : 1 ≤ k) :
    (cycleFactor (cycleFactor k) : ℝ) ≤ cycleLogConstant * Real.log (Real.log (4 * k)) := by
  let t := Real.log (Real.log (4 * (k : ℝ)))
  have ht : iteratedLogFloor ≤ t := iterated_log_ge k hk
  have hlog := log_cycleFactor_le k hk
  have hbase : (cycleFactor (cycleFactor k) : ℝ) ≤
      (5 + Real.log pairLogConstant / Real.log 2) + (1 / Real.log 2) * t := by
    have hh := div_le_div_of_nonneg_right hlog log_two_pos.le
    calc
      _ ≤ Real.log (cycleFactor k) / Real.log 2 + 5 :=
        cycleFactor_le_log (cycleFactor k) (cycleFactor_pos k)
      _ ≤ (Real.log pairLogConstant + t) / Real.log 2 + 5 := add_le_add hh le_rfl
      _ = _ := by ring
  have ha : 0 ≤ 5 + Real.log pairLogConstant / Real.log 2 := by
    have h := log_pairLogConstant_pos
    have h2 := log_two_pos
    positivity
  exact hbase.trans (absorb_affine_constant _ _ _ _ ha iteratedLogFloor_pos ht)

end OnlineSteinerForest.UpperBound
