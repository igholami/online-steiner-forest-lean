import OnlineSteinerForest.UpperBound.ChargingEdges
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Physical auxiliary spokes cost zero, so total charging cost is just reference cost. -/
namespace OnlineSteinerForest.UpperBound.Charging

open scoped Classical
variable {W J : Type*} [Fintype W] [Fintype J] [DecidableEq W] [DecidableEq J]

theorem cost_map_reference (c : Sym2 W → ℝ) (e : Sym2 W) :
    cost (J := J) c (Sym2.map Sum.inl e) = c e := by
  refine Sym2.ind (fun _ _ => rfl) e

theorem physical_cost_sum (H : SimpleGraph W) (left right : J → W) (c : Sym2 W → ℝ) :
    (∑ e : PhysicalEdge H J, cost c s(physicalLeft H left right e, physicalRight H left right e)) =
      edgeCost c H.edgeFinset := by
  simp_rw [physical_pair]
  rw [Fintype.sum_sum_type]
  have haux : (∑ e : J × Bool, cost c (physical H left right (.inr e))) = 0 := by
    apply Finset.sum_eq_zero
    rintro ⟨j, b⟩ _
    cases b <;> rfl
  rw [haux, add_zero]
  simp only [physical, cost_map_reference]
  exact (Finset.sum_subtype H.edgeFinset (fun _ => Iff.rfl) c).symm

theorem cost_nonneg (c : Sym2 W → ℝ) (hc : ∀ e, 0 ≤ c e) (e : Sym2 (W ⊕ J)) : 0 ≤ cost c e := by
  refine Sym2.ind (fun x y => ?_) e
  cases x <;> cases y <;> first | exact hc _ | exact le_rfl

end OnlineSteinerForest.UpperBound.Charging
