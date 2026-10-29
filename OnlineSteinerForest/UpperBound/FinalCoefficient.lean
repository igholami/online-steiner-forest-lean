import OnlineSteinerForest.UpperBound.FinalLogFactors

/-! Extract a single absolute constant from the manuscript's final discrete bound. -/
namespace OnlineSteinerForest.UpperBound

noncomputable def accountingCoefficient (k : ℕ) : ℝ :=
  (32 / 31 : ℝ) * (1 + 64 * batchClassCount k * cycleFactor k +
    (2 ^ 30 * cycleFactor (cycleFactor k) + 1) * cycleFactor k)

noncomputable def finalUpperConstant : ℝ :=
  (32 / 31 : ℝ) * (1 / (Real.log 2 * iteratedLogFloor) +
    64 * classLogConstant * pairLogConstant +
    2 ^ 30 * cycleLogConstant * pairLogConstant + pairLogConstant / iteratedLogFloor)

theorem finalUpperConstant_pos : 0 < finalUpperConstant := by
  unfold finalUpperConstant
  have ha := log_two_pos
  have hb := iteratedLogFloor_pos
  have hc := classLogConstant_pos
  have hd := cycleLogConstant_pos
  have he := pairLogConstant_pos
  positivity

/-- The last `O(log k log log k)` conversion is uniform, including `k = 1`. -/
theorem accountingCoefficient_le_logs (k : ℕ) (hk : 1 ≤ k) :
    accountingCoefficient k ≤ finalUpperConstant * Real.log (2 * k) *
      Real.log (Real.log (4 * k)) := by
  let L : ℝ := cycleFactor k
  let M : ℝ := batchClassCount k
  let R : ℝ := cycleFactor (cycleFactor k)
  let s := Real.log (2 * (k : ℝ))
  let t := Real.log (Real.log (4 * (k : ℝ)))
  have hs : Real.log 2 ≤ s := pair_log_ge k hk
  have ht : iteratedLogFloor ≤ t := iterated_log_ge k hk
  have hspos : 0 < s := log_two_pos.trans_le hs
  have htpos : 0 < t := iteratedLogFloor_pos.trans_le ht
  have hL : L ≤ pairLogConstant * s := cycleFactor_le_pair_log k hk
  have hM : M ≤ classLogConstant * t := batchClassCount_le_iterated_log k hk
  have hR : R ≤ cycleLogConstant * t := cycleFactor_cycleFactor_le_iterated_log k hk
  have hL0 : 0 ≤ L := Nat.cast_nonneg _
  have hML : M * L ≤ classLogConstant * pairLogConstant * s * t := by
    convert mul_le_mul hM hL hL0 (mul_nonneg classLogConstant_pos.le htpos.le) using 1 <;> ring
  have hRL : R * L ≤ cycleLogConstant * pairLogConstant * s * t := by
    convert mul_le_mul hR hL hL0 (mul_nonneg cycleLogConstant_pos.le htpos.le) using 1 <;> ring
  have hOne : 1 ≤ (1 / (Real.log 2 * iteratedLogFloor)) * s * t := by
    have hprod := mul_le_mul hs ht iteratedLogFloor_pos.le hspos.le
    have hh : 1 ≤ s * t / (Real.log 2 * iteratedLogFloor) :=
      (le_div_iff₀ (mul_pos log_two_pos iteratedLogFloor_pos)).mpr (by simpa using hprod)
    convert hh using 1 <;> ring
  have hLt : L ≤ (pairLogConstant / iteratedLogFloor) * s * t := by
    have hh : pairLogConstant * s ≤ (pairLogConstant * s) / iteratedLogFloor * t := by
      rw [div_mul_eq_mul_div]
      exact (le_div_iff₀ iteratedLogFloor_pos).mpr
        (mul_le_mul_of_nonneg_left ht (mul_nonneg pairLogConstant_pos.le hspos.le))
    convert hL.trans hh using 1 <;> ring
  have hinner : 1 + 64 * M * L + (2 ^ 30 * R + 1) * L ≤
      (1 / (Real.log 2 * iteratedLogFloor) + 64 * classLogConstant * pairLogConstant +
        2 ^ 30 * cycleLogConstant * pairLogConstant + pairLogConstant / iteratedLogFloor) * s * t := by
    calc
      _ = 1 + 64 * (M * L) + 2 ^ 30 * (R * L) + L := by ring
      _ ≤ (1 / (Real.log 2 * iteratedLogFloor)) * s * t +
          64 * (classLogConstant * pairLogConstant * s * t) +
          2 ^ 30 * (cycleLogConstant * pairLogConstant * s * t) +
          (pairLogConstant / iteratedLogFloor) * s * t :=
        add_le_add (add_le_add (add_le_add hOne (mul_le_mul_of_nonneg_left hML (by norm_num)))
          (mul_le_mul_of_nonneg_left hRL (by positivity))) hLt
      _ = _ := by ring
  change (32 / 31 : ℝ) * (1 + 64 * M * L + (2 ^ 30 * R + 1) * L) ≤ finalUpperConstant * s * t
  calc
    _ ≤ (32 / 31 : ℝ) *
        ((1 / (Real.log 2 * iteratedLogFloor) + 64 * classLogConstant * pairLogConstant +
          2 ^ 30 * cycleLogConstant * pairLogConstant + pairLogConstant / iteratedLogFloor) * s * t) :=
      mul_le_mul_of_nonneg_left hinner (by norm_num)
    _ = _ := by unfold finalUpperConstant; ring

end OnlineSteinerForest.UpperBound
