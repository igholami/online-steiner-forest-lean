import OnlineSteinerForest.UpperBound.ThresholdRankBound
import OnlineSteinerForest.UpperBound.ChronologyChargingReference
import OnlineSteinerForest.UpperBound.ChargingRank
import OnlineSteinerForest.UpperBound.ChargingCost

/-! Cycle-rank charging for a concrete base forest and chronological auxiliary pairs. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {W J : Type*} [Fintype W] [Fintype J] [DecidableEq W] [DecidableEq J]

theorem charging_rank_mul_separation_le (H : SimpleGraph W) (hH : H.IsAcyclic)
    (left right : J → W) (hne : ∀ j, left j ≠ right j) (time : J ↪ ℕ)
    (c : Sym2 W → ℝ) (hc : ∀ e, 0 ≤ c e) (d : ℕ → W → W → ENNReal)
    (hrefl : ∀ i w, d i w w = 0) (hsymm : ∀ i u v, d i u v = d i v u)
    (htriangle : ∀ i u v z, d i u z ≤ d i u v + d i v z)
    (sep : ℝ) (hsep : ∀ j, ENNReal.ofReal sep ≤ d (time j) (left j) (right j))
    (hprior : ∀ i j, time j < i → d i (left j) (right j) = 0)
    (href : ∀ i {u v}, H.Adj u v → d i u v ≤ ENNReal.ofReal (c s(u, v)))
    (hr : 1 ≤ Girth.cycleRank (Charging.physicalLeft H left right) (Charging.physicalRight H left right)) :
    (Girth.cycleRank (Charging.physicalLeft H left right) (Charging.physicalRight H left right) : ℝ) * sep ≤
      4 * cycleFactor (Girth.cycleRank (Charging.physicalLeft H left right) (Charging.physicalRight H left right)) *
        edgeCost c H.edgeFinset := by
  have hedges : Function.Injective (fun i : Charging.PhysicalEdge H J =>
      s(Charging.physicalLeft H left right i, Charging.physicalRight H left right i)) := by
    simpa only [Charging.physical_pair] using Charging.physical_injective H left right hne
  have hh := rank_mul_separation_le (Charging.graph H left right)
    (Charging.physicalLeft H left right) (Charging.physicalRight H left right)
    (Charging.physical_adjacent H left right) hedges (Charging.cost c) (Charging.cost_nonneg c hc) hr
    (fun e => (Charging.edgeLabel right e).map time) (charging_timed_reference_acyclic H hH left right hne time)
    (Charging.timedLabel_unique right time) d (Charging.projection left) hrefl htriangle sep
    (fun {a b} _hab i hl => charging_pair_separation left right time d hsymm _ hsep i hl)
    (charging_reference_metric H left right time c d hrefl href)
    (fun i j {a b} _hab hl hij => charging_pair_prior_zero left right time d hsymm hprior i j hl hij)
  simpa only [Charging.physical_cost_sum] using hh

end OnlineSteinerForest.UpperBound
