import OnlineSteinerForest.Graph.Feasibility
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! Every finite reference edge set has a no-more-expensive spanning forest. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_reference_forest (F : Finset (Sym2 V)) (c : Sym2 V → ℝ) (hc : ∀ e ∈ F, 0 ≤ c e) :
    ∃ T : Finset (Sym2 V), T ⊆ F ∧
      (SimpleGraph.fromEdgeSet (T : Set (Sym2 V))).IsAcyclic ∧
      (SimpleGraph.fromEdgeSet (T : Set (Sym2 V))).Reachable =
        (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).Reachable ∧ edgeCost c T ≤ edgeCost c F := by
  classical
  let H := SimpleGraph.fromEdgeSet (F : Set (Sym2 V))
  obtain ⟨S, hSH, hS, hreach⟩ := H.exists_isAcyclic_reachable_eq_le
  let T := S.edgeFinset
  have hfrom : SimpleGraph.fromEdgeSet (T : Set (Sym2 V)) = S := by simp [T]
  have hsub : T ⊆ F := by
    intro e he
    have hmem := SimpleGraph.edgeSet_mono hSH (show e ∈ S.edgeSet by simpa [T] using he)
    have hh : e ∈ (F : Set (Sym2 V)) \ Sym2.diagSet := by
      simpa only [H, SimpleGraph.edgeSet_fromEdgeSet] using hmem
    exact hh.1
  refine ⟨T, hsub, hfrom ▸ hS, ?_, ?_⟩
  · rw [hfrom]
    exact hreach
  · exact Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro e he _; exact hc e he)

end OnlineSteinerForest.UpperBound
