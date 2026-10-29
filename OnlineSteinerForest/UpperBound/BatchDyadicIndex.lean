import OnlineSteinerForest.UpperBound.FinalParameters

/-! Exact dyadic bucket computation using the natural floor and binary logarithm. -/
namespace OnlineSteinerForest.UpperBound

noncomputable def dyadicFloorIndex (base x : ℝ) : ℕ := (⌊x / base⌋₊).log2

theorem dyadic_floor_band (base x : ℝ) (hb : 0 < base) (hx : base ≤ x) :
    (2 : ℝ) ^ dyadicFloorIndex base x * base ≤ x ∧
      x < 2 * ((2 : ℝ) ^ dyadicFloorIndex base x * base) := by
  let q : ℕ := ⌊x / base⌋₊
  have hratio : 1 ≤ x / base := (le_div_iff₀ hb).mpr (by simpa using hx)
  have hq : 1 ≤ q := (Nat.one_le_floor_iff _).mpr hratio
  have hqfloor : (q : ℝ) ≤ x / base := Nat.floor_le (by linarith)
  have hpow : (2 : ℝ) ^ q.log2 ≤ (q : ℝ) := by
    exact_mod_cast Nat.log2_self_le (by omega : q ≠ 0)
  have hlo : (2 : ℝ) ^ q.log2 ≤ x / base := hpow.trans hqfloor
  have hqupper : (q : ℝ) + 1 ≤ (2 : ℝ) ^ (q.log2 + 1) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Nat.lt_log2_self (n := q)))
  have hhi : x / base < (2 : ℝ) ^ (q.log2 + 1) := (Nat.lt_floor_add_one _).trans_le hqupper
  constructor
  · exact (le_div_iff₀ hb).mp hlo
  · have hmul := (div_lt_iff₀ hb).mp hhi
    simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm, dyadicFloorIndex, q] using hmul

theorem dyadic_floor_index_le (base x : ℝ) (k : ℕ) (hb : 0 < base)
    (hx : base ≤ x) (hk : 0 < k) (hxk : x ≤ k * base) : dyadicFloorIndex base x ≤ k.log2 := by
  let q : ℕ := ⌊x / base⌋₊
  have hratio : 1 ≤ x / base := (le_div_iff₀ hb).mpr (by simpa using hx)
  have hq : 1 ≤ q := (Nat.one_le_floor_iff _).mpr hratio
  have hqfloor : (q : ℝ) ≤ x / base := Nat.floor_le (by linarith)
  have hqk : q ≤ k := by
    exact_mod_cast hqfloor.trans ((div_le_iff₀ hb).mpr hxk)
  exact (Nat.le_log2 (Nat.ne_of_gt hk)).mpr ((Nat.log2_self_le (by omega : q ≠ 0)).trans hqk)

end OnlineSteinerForest.UpperBound
