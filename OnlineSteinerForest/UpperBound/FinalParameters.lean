import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The manuscript's cycle, pair-count, and separated-batch parameters. -/
namespace OnlineSteinerForest.UpperBound

noncomputable def cycleFactor (n : ℕ) : ℕ := ⌈Real.logb 2 (8 * n)⌉₊ + 1

noncomputable def batchClassCount (k : ℕ) : ℕ := 28 + ⌈5 * Real.logb 2 (cycleFactor k)⌉₊

theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

theorem log_eight_mul_nat (n : ℕ) (hn : 1 ≤ n) :
    Real.log (8 * (n : ℝ)) = 3 * Real.log 2 + Real.log n := by
  rw [Real.log_mul (by norm_num) (Nat.cast_ne_zero.mpr (by omega))]
  have he : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  rw [he]

theorem cycleFactor_pos (n : ℕ) : 0 < cycleFactor n := Nat.succ_pos _

theorem cycleFactor_le_log (n : ℕ) (hn : 1 ≤ n) :
    (cycleFactor n : ℝ) ≤ Real.log n / Real.log 2 + 5 := by
  have ha := log_two_pos
  have hlog := log_eight_mul_nat n hn
  have hnlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr hn)
  have hx : 0 ≤ Real.logb 2 (8 * (n : ℝ)) := by
    rw [Real.logb, hlog]
    positivity
  have hc := Nat.ceil_lt_add_one hx
  have hceil : (cycleFactor n : ℝ) ≤ Real.logb 2 (8 * (n : ℝ)) + 2 := by
    unfold cycleFactor
    push_cast
    linarith
  have heq : Real.logb 2 (8 * (n : ℝ)) + 2 = Real.log n / Real.log 2 + 5 := by
    rw [Real.logb, hlog]
    field_simp
    ring
  exact hceil.trans_eq heq

theorem four_le_cycleFactor (n : ℕ) (hn : 1 ≤ n) : 4 ≤ cycleFactor n := by
  have ha := log_two_pos
  have hnlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr hn)
  have hlow : (3 : ℝ) ≤ Real.logb 2 (8 * (n : ℝ)) := by
    rw [Real.logb, log_eight_mul_nat n hn]
    apply (le_div_iff₀ ha).mpr
    linarith
  have hc : (3 : ℝ) ≤ (⌈Real.logb 2 (8 * (n : ℝ))⌉₊ : ℝ) := hlow.trans (Nat.le_ceil _)
  have hnat : 3 ≤ ⌈Real.logb 2 (8 * (n : ℝ))⌉₊ := by exact_mod_cast hc
  exact Nat.succ_le_succ hnat

theorem cycleFactor_le_pair_log (k : ℕ) (hk : 1 ≤ k) :
    (cycleFactor k : ℝ) ≤ (5 / Real.log 2) * Real.log (2 * k) := by
  have ha := log_two_pos
  have hL := cycleFactor_le_log k hk
  have hklog : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr hk)
  have hlog : Real.log (2 * (k : ℝ)) = Real.log 2 + Real.log k :=
    Real.log_mul (by norm_num) (Nat.cast_ne_zero.mpr (by omega))
  have hL' : (cycleFactor k : ℝ) * Real.log 2 ≤ Real.log k + 5 * Real.log 2 := by
    have hh := mul_le_mul_of_nonneg_right hL ha.le
    simpa only [add_mul, div_mul_cancel₀ _ ha.ne'] using hh
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ ha).mpr
  rw [hlog]
  linarith

theorem batchClassCount_le_log (k : ℕ) (_hk : 1 ≤ k) :
    (batchClassCount k : ℝ) ≤ 29 + 5 * Real.log (cycleFactor k) / Real.log 2 := by
  have hL : (1 : ℝ) ≤ cycleFactor k := Nat.one_le_cast.mpr (cycleFactor_pos k)
  have hx : 0 ≤ 5 * Real.logb 2 (cycleFactor k) := by
    rw [Real.logb]
    exact mul_nonneg (by norm_num) (div_nonneg (Real.log_nonneg hL) log_two_pos.le)
  have hc := Nat.ceil_lt_add_one hx
  unfold batchClassCount
  push_cast
  rw [Real.logb] at hc ⊢
  calc
    _ ≤ 29 + 5 * (Real.log (cycleFactor k) / Real.log 2) := by linarith
    _ = _ := by ring

end OnlineSteinerForest.UpperBound
