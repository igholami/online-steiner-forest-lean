import OnlineSteinerForest.UpperBound.ChargingRank

/-! Any nonempty auxiliary family on at most two reference trees has rank at least its size minus one. -/
namespace OnlineSteinerForest.UpperBound

open scoped Classical
variable {W J : Type*} [Fintype W] [Fintype J] [DecidableEq W] [DecidableEq J]

theorem charging_two_component_rank (H : SimpleGraph W) (hH : H.IsAcyclic)
    (left right : J → W) (hJ : 1 ≤ Fintype.card J) (hcomponents : Nat.card H.ConnectedComponent ≤ 2) :
    Fintype.card J - 1 ≤ Girth.cycleRank (Charging.physicalLeft H left right) (Charging.physicalRight H left right) := by
  letI : Nonempty J := Fintype.card_pos_iff.mp hJ
  have hcc : 0 < Girth.componentCount (Charging.physicalLeft H left right) (Charging.physicalRight H left right) :=
    Nat.card_pos
  have heuler := forest_euler H hH
  unfold Girth.cycleRank
  rw [Charging.physical_count]
  simp only [Fintype.card_sum]
  omega

end OnlineSteinerForest.UpperBound
