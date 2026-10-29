import OnlineSteinerForest.UpperBound.ThresholdCharging
import OnlineSteinerForest.UpperBound.SparseMultiplicityRank
import OnlineSteinerForest.UpperBound.SparseParameters
import OnlineSteinerForest.UpperBound.GirthComponentAverage

/-! The actual two-tree charging construction implies the manuscript multiplicity cap. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {W J : Type*} [Fintype W] [Fintype J] [DecidableEq W] [DecidableEq J]

theorem charging_two_component_multiplicity_cap (H : SimpleGraph W) (hH : H.IsAcyclic)
    (left right : J → W) (hne : ∀ j, left j ≠ right j) (time : J ↪ ℕ)
    (c : Sym2 W → ℝ) (hc : ∀ e, 0 ≤ c e) (d : ℕ → W → W → ENNReal)
    (hrefl : ∀ i w, d i w w = 0) (hsymm : ∀ i u v, d i u v = d i v u)
    (htriangle : ∀ i u v z, d i u z ≤ d i u v + d i v z)
    (scale : ℝ) (hscale : 0 < scale)
    (hsep : ∀ j, ENNReal.ofReal (scale / 2) ≤ d (time j) (left j) (right j))
    (hprior : ∀ i j, time j < i → d i (left j) (right j) = 0)
    (href : ∀ i {u v}, H.Adj u v → d i u v ≤ ENNReal.ofReal (c s(u, v)))
    (hcomponents : Nat.card H.ConnectedComponent ≤ 2)
    (L : ℕ) (hL : 1 ≤ L) (hcost : edgeCost c H.edgeFinset ≤ 6 * zoneMultiplier L * scale) :
    Fintype.card J ≤ parallelCap L := by
  have hB := parallelCap_pos L hL
  by_cases hsmall : Fintype.card J ≤ 1
  · omega
  let r := Girth.cycleRank (Charging.physicalLeft H left right) (Charging.physicalRight H left right)
  have hqr : Fintype.card J - 1 ≤ r := charging_two_component_rank H hH left right (by omega) hcomponents
  have hr : 1 ≤ r := by omega
  have hrq : r ≤ Fintype.card J := Charging.cycleRank_le_auxCount H hH left right
  have hlog : (cycleFactor r : ℝ) ≤ cycleFactor (Fintype.card J) :=
    Nat.cast_le.mpr (Girth.cycleFactor_mono hr hrq)
  have hC : 0 ≤ edgeCost c H.edgeFinset := Finset.sum_nonneg (by intro e _; exact hc e)
  have hh := charging_rank_mul_separation_le H hH left right hne time c hc d hrefl hsymm htriangle
    (scale / 2) hsep hprior href hr
  have hqr' : ((Fintype.card J : ℝ) - 1) ≤ r := by
    have hh' : (((Fintype.card J - 1 : ℕ) : ℝ)) ≤ r := Nat.cast_le.mpr hqr
    simpa only [Nat.cast_sub (by omega : 1 ≤ Fintype.card J), Nat.cast_one] using hh'
  have ha := mul_le_mul_of_nonneg_right hqr' (show 0 ≤ scale / 2 by positivity)
  have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ) ≤ 4)) hC
  have hc' := mul_le_mul_of_nonneg_left hcost (show 0 ≤ 4 * (cycleFactor (Fintype.card J) : ℝ) by positivity)
  change (r : ℝ) * (scale / 2) ≤ 4 * cycleFactor r * edgeCost c H.edgeFinset at hh
  have hbound : (((Fintype.card J : ℝ) - 1) * scale) ≤
      (48 * (zoneMultiplier L : ℝ) * cycleFactor (Fintype.card J)) * scale := by nlinarith
  exact multiplicity_le_parallelCap L (Fintype.card J) hL (by omega)
    ((mul_le_mul_iff_left₀ hscale).mp (by simpa [mul_comm] using hbound))

end OnlineSteinerForest.UpperBound
