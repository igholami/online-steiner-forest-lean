import OnlineSteinerForest.UpperBound.ReferenceRun
import OnlineSteinerForest.UpperBound.Accounting

/-! The actual reference execution has the manuscript's telescoping savings budget. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem referenceRun_savings_bound (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (initial : Finset (Sym2 V))
    (hinput : ∀ e ∈ initial, e ∈ G.edgeSet) (marks : ℕ → Finset V) (n : ℕ) :
    (∑ i ∈ Finset.range n,
      (edgeCost c (referenceRun G c hc initial hinput marks i).val -
        edgeCost c (referenceRun G c hc initial hinput marks (i + 1)).val)) ≤
      edgeCost c initial := by
  exact total_savings_le_initial
    (fun i => edgeCost c (referenceRun G c hc initial hinput marks i).val) n
    (referenceRun_cost_nonneg G c hc initial hinput marks n)

end OnlineSteinerForest.UpperBound
