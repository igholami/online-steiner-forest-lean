import OnlineSteinerForest.UpperBound.ThresholdCharging
import OnlineSteinerForest.UpperBound.GirthComponentAverage

/-! A dense auxiliary core pays at most sixteen logarithmic factors of its zone cost. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {W J : Type*} [Fintype W] [Fintype J] [DecidableEq W] [DecidableEq J]

theorem charging_dense_count_scale_le (H : SimpleGraph W) (hH : H.IsAcyclic)
    (left right : J → W) (hne : ∀ j, left j ≠ right j) (time : J ↪ ℕ)
    (c : Sym2 W → ℝ) (hc : ∀ e, 0 ≤ c e) (d : ℕ → W → W → ENNReal)
    (hrefl : ∀ i w, d i w w = 0) (hsymm : ∀ i u v, d i u v = d i v u)
    (htriangle : ∀ i u v z, d i u z ≤ d i u v + d i v z)
    (scale : ℝ) (hscale : 0 ≤ scale)
    (hsep : ∀ j, ENNReal.ofReal (scale / 2) ≤ d (time j) (left j) (right j))
    (hprior : ∀ i j, time j < i → d i (left j) (right j) = 0)
    (href : ∀ i {u v}, H.Adj u v → d i u v ≤ ENNReal.ofReal (c s(u, v)))
    (hdense : 2 * Nat.card H.ConnectedComponent ≤ Fintype.card J)
    (k : ℕ) (hcount : Fintype.card J ≤ k) :
    (Fintype.card J : ℝ) * scale ≤ 16 * cycleFactor k * edgeCost c H.edgeFinset := by
  let r := Girth.cycleRank (Charging.physicalLeft H left right) (Charging.physicalRight H left right)
  have hC : 0 ≤ edgeCost c H.edgeFinset := Finset.sum_nonneg (by intro e _; exact hc e)
  by_cases hJ : Fintype.card J = 0
  · simp only [hJ, Nat.cast_zero, zero_mul]
    positivity
  have hqr : Fintype.card J ≤ 2 * r := Charging.auxCount_le_twice_cycleRank H hH left right hdense
  have hr : 1 ≤ r := by omega
  have hrk : r ≤ k := (Charging.cycleRank_le_auxCount H hH left right).trans hcount
  have hlog : (cycleFactor r : ℝ) ≤ cycleFactor k := Nat.cast_le.mpr (Girth.cycleFactor_mono hr hrk)
  have hcharge := charging_rank_mul_separation_le H hH left right hne time c hc d hrefl hsymm htriangle
    (scale / 2) hsep hprior href hr
  have hqr' : (Fintype.card J : ℝ) ≤ 2 * (r : ℝ) := by exact_mod_cast hqr
  have hmul := mul_le_mul_of_nonneg_right hqr' hscale
  have hlogmul := mul_le_mul_of_nonneg_right hlog hC
  change (r : ℝ) * (scale / 2) ≤ 4 * cycleFactor r * edgeCost c H.edgeFinset at hcharge
  nlinarith

end OnlineSteinerForest.UpperBound
