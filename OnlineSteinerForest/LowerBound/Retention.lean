import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Deterministic price retention after the probabilistic existence argument.
These finite inequalities do not assume or establish matching existence. -/
namespace OnlineSteinerForest.LowerBound

/-- At least half of the total price is retained if at most half is bad. -/
theorem good_price_ge_half {ι : Type*} [DecidableEq ι]
    (ranks bad : Finset ι) (price : ι → ℝ)
    (hbad : bad ⊆ ranks)
    (h : ∑ i ∈ bad, price i ≤ (∑ i ∈ ranks, price i) / 2) :
    (∑ i ∈ ranks, price i) / 2 ≤ ∑ i ∈ ranks \ bad, price i := by
  have ht := Finset.sum_sdiff hbad (f := price)
  linarith

/-- The final retained-price versus comparison-path calculation, without division
by OPT. All assumptions here are numerical and remain to be justified for graphs. -/
theorem ratio_from_retention (ALG OPT total vertices logSize level : ℝ)
    (hpath : OPT ≤ vertices - 1)
    (hretain : total / 2 ≤ ALG)
    (htotal : vertices * logSize * level * Real.log 2 / 2 ^ 12 ≤ total)
    (hscale : 0 ≤ logSize * level * Real.log 2) :
    OPT * (logSize * level * Real.log 2 / 2 ^ 13) ≤ ALG := by
  have hmul := mul_le_mul_of_nonneg_right hpath
    (show 0 ≤ logSize * level * Real.log 2 / 2 ^ 13 by positivity)
  nlinarith

end OnlineSteinerForest.LowerBound
