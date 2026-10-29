import OnlineSteinerForest.UpperBound.ChargingEndpoints
import OnlineSteinerForest.UpperBound.ChargingComponents
import OnlineSteinerForest.UpperBound.ChargingForestEuler
import OnlineSteinerForest.UpperBound.GirthComponents

/-! Exact charging cycle rank and the dense-core rank lower bound. -/
namespace OnlineSteinerForest.UpperBound.Charging

open scoped Classical
variable {W J : Type*} [Fintype W] [Fintype J] [DecidableEq W] [DecidableEq J]

theorem physical_count (H : SimpleGraph W) :
    Fintype.card (PhysicalEdge H J) = H.edgeFinset.card + 2 * Fintype.card J := by
  simp only [PhysicalEdge, Fintype.card_sum, Fintype.card_coe, Fintype.card_prod, Fintype.card_bool]
  omega

theorem charging_componentCount (H : SimpleGraph W) (left right : J → W)
    (hpairs : ∀ j, H.Reachable (left j) (right j)) :
    Girth.componentCount (physicalLeft H left right) (physicalRight H left right) =
      Nat.card H.ConnectedComponent := by
  exact Nat.card_congr ((Girth.endpointComponentEquiv (physicalLeft H left right)
    (physicalRight H left right)).trans ((endpointComponentEquiv H left right).trans
      (baseComponentEquiv H left right hpairs)))

theorem cycleRank_eq_auxCount (H : SimpleGraph W) (hH : H.IsAcyclic) (left right : J → W)
    (hpairs : ∀ j, H.Reachable (left j) (right j)) :
    Girth.cycleRank (physicalLeft H left right) (physicalRight H left right) = Fintype.card J := by
  have he := forest_euler H hH
  unfold Girth.cycleRank
  rw [charging_componentCount H left right hpairs, physical_count]
  simp only [Fintype.card_sum]
  omega

theorem cycleRank_ge_aux_sub_components (H : SimpleGraph W) (hH : H.IsAcyclic) (left right : J → W) :
    Fintype.card J - Nat.card H.ConnectedComponent ≤
      Girth.cycleRank (physicalLeft H left right) (physicalRight H left right) := by
  have he := forest_euler H hH
  unfold Girth.cycleRank
  rw [physical_count]
  simp only [Fintype.card_sum]
  omega

theorem auxCount_le_twice_cycleRank (H : SimpleGraph W) (hH : H.IsAcyclic) (left right : J → W)
    (hdense : 2 * Nat.card H.ConnectedComponent ≤ Fintype.card J) :
    Fintype.card J ≤ 2 * Girth.cycleRank (physicalLeft H left right) (physicalRight H left right) := by
  have h := cycleRank_ge_aux_sub_components H hH left right
  omega

theorem cycleRank_le_auxCount (H : SimpleGraph W) (hH : H.IsAcyclic) (left right : J → W) :
    Girth.cycleRank (physicalLeft H left right) (physicalRight H left right) ≤ Fintype.card J := by
  have he := forest_euler H hH
  have hc : Girth.componentCount (physicalLeft H left right) (physicalRight H left right) ≤
      Nat.card H.ConnectedComponent := by
    have hcard := Nat.card_congr ((Girth.endpointComponentEquiv (physicalLeft H left right)
      (physicalRight H left right)).trans (endpointComponentEquiv H left right))
    exact hcard.le.trans (base_componentCount_le H left right)
  unfold Girth.cycleRank
  rw [physical_count]
  simp only [Fintype.card_sum]
  omega

end OnlineSteinerForest.UpperBound.Charging
