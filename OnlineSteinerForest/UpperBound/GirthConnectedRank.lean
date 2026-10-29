import OnlineSteinerForest.UpperBound.GirthComponents
import OnlineSteinerForest.UpperBound.GirthEndpointGraph

/-! Cycle rank on a connected endpoint graph is the ordinary Euler count. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*} [Fintype V] [Fintype I]

theorem componentCount_eq_one (left right : I → V) (hc : (endpointGraph left right).Connected) :
    componentCount left right = 1 := by
  letI : Nonempty V := hc.nonempty
  letI : Subsingleton (endpointGraph left right).ConnectedComponent := hc.preconnected.subsingleton_connectedComponent
  have hh := Nat.card_congr (endpointComponentEquiv left right)
  exact hh.trans Nat.card_unique

theorem cycleRank_le_edgeCount (left right : I → V) : cycleRank left right ≤ Fintype.card I := by
  have hc := componentCount_le_vertices left right
  unfold cycleRank
  omega

theorem connected_cycleRank_eq (left right : I → V) (hc : (endpointGraph left right).Connected) :
    cycleRank left right = Fintype.card I + 1 - Fintype.card V := by
  unfold cycleRank
  rw [componentCount_eq_one left right hc]

end OnlineSteinerForest.UpperBound.Girth
