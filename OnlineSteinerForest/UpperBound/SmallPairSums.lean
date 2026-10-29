import OnlineSteinerForest.UpperBound.SmallPairComponents
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Each selected pair is charged to exactly one actual reference component. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem sum_componentPairs (F : Finset (Sym2 V)) (requests : List (V × V))
    (selected : Finset (Fin requests.length)) (a : Fin requests.length → ℝ) :
    (∑ C ∈ referenceComponents (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))),
      ∑ i ∈ componentPairs F requests selected C, a i) = ∑ i ∈ selected, a i := by
  apply Finset.sum_fiberwise_of_maps_to
  intro i _
  exact Finset.mem_image_of_mem _ (Finset.mem_univ requests[i.val].1)

theorem reference_componentEdges_subset (F : Finset (Sym2 V))
    (C : (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).ConnectedComponent) :
    componentEdges (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))) C ⊆ F := by
  intro e he
  induction e using Sym2.ind with
  | _ u v => exact ((mem_componentEdges _ C u v).mp he).1.1

end OnlineSteinerForest.UpperBound
