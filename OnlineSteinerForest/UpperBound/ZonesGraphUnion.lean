import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! The degree of a finite graph union is bounded by the sum of the component degrees. -/
namespace OnlineSteinerForest.UpperBound

open scoped Classical BigOperators

theorem degree_iSup_le {V I : Type*} [Fintype V] [Fintype I] [DecidableEq V]
    (graphs : I → SimpleGraph V) (v : V) :
    (⨆ i, graphs i).degree v ≤ ∑ i, (graphs i).degree v := by
  have hneighbors : (⨆ i, graphs i).neighborFinset v =
      Finset.univ.biUnion (fun i => (graphs i).neighborFinset v) := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.iSup_adj,
      Finset.mem_biUnion, Finset.mem_univ, true_and]
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hneighbors]
  simpa only [SimpleGraph.card_neighborFinset_eq_degree] using
    (Finset.card_biUnion_le (s := Finset.univ) (t := fun i => (graphs i).neighborFinset v))

end OnlineSteinerForest.UpperBound
