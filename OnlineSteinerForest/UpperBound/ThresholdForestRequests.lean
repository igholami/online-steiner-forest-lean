import OnlineSteinerForest.UpperBound.ThresholdRankBound
import OnlineSteinerForest.UpperBound.ThresholdGadgetPrior
import OnlineSteinerForest.UpperBound.ThresholdGadgetReference
import OnlineSteinerForest.UpperBound.ChargingRank
import OnlineSteinerForest.UpperBound.ChargingCost

/-! The threshold bound for actual greedy requests and an ordinary connecting reference forest. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V J : Type*} [Fintype V] [Fintype J] [DecidableEq V] [DecidableEq J]

theorem request_count_mul_separation_le_forest (G H : SimpleGraph V) (hHG : H ≤ G)
    (hH : H.IsAcyclic) (c : Sym2 V → ℝ) (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (index : J → Fin requests.length) (hinj : Function.Injective index) (τ : ℝ) (hτ : 0 < τ)
    (hpay : ∀ j, τ ≤ payment G c requests feasible (index j))
    (hconnect : ∀ j, H.Reachable requests[(index j).val].1 requests[(index j).val].2) :
    (Fintype.card J : ℝ) * τ ≤ 4 * cycleFactor (Fintype.card J) * edgeCost c H.edgeFinset := by
  let left := requestLeft requests index
  let right := requestRight requests index
  have hne : ∀ j, left j ≠ right j := by
    intro j
    exact request_positive_endpoints_ne G c hc requests feasible (index j) (hτ.trans_le (hpay j))
  have hcost : edgeCost (fun e => max (c e) 0) H.edgeFinset = edgeCost c H.edgeFinset := by
    apply Finset.sum_congr rfl
    intro e he
    exact max_eq_left (hc e (SimpleGraph.edgeSet_mono hHG (H.mem_edgeFinset.mp he)))
  have hC : 0 ≤ edgeCost c H.edgeFinset := Finset.sum_nonneg (by
    intro e he
    exact hc e (SimpleGraph.edgeSet_mono hHG (H.mem_edgeFinset.mp he)))
  by_cases hJ : Fintype.card J = 0
  · simp only [hJ, Nat.cast_zero, zero_mul]
    positivity
  have hrank := Charging.cycleRank_eq_auxCount H hH left right hconnect
  have hadj := Charging.physical_adjacent H left right
  have hedges : Function.Injective (fun i : Charging.PhysicalEdge H J =>
      s(Charging.physicalLeft H left right i, Charging.physicalRight H left right i)) := by
    simpa only [Charging.physical_pair] using Charging.physical_injective H left right hne
  have hh := rank_mul_separation_le (Charging.graph H left right)
    (Charging.physicalLeft H left right) (Charging.physicalRight H left right) hadj hedges
    (Charging.cost (fun e => max (c e) 0))
    (Charging.cost_nonneg _ (fun e => le_max_right (c e) 0)) (by rw [hrank]; omega)
    (requestLabel requests index) (requestLabel_reference_forest H hH requests index hne)
    (requestLabel_unique requests index hinj) (requestMetric G c requests feasible)
    (requestProjection requests index) (requestMetric_refl G c hc requests feasible)
    (requestMetric_triangle G c hc requests feasible) τ
    (request_gadget_separation G H c requests feasible index τ hpay)
    (request_gadget_reference_bound G H hHG c hc requests feasible index)
    (request_gadget_prior_zero G H c hc requests feasible index)
  rw [hrank, Charging.physical_cost_sum, hcost] at hh
  exact hh

end OnlineSteinerForest.UpperBound
