import OnlineSteinerForest.UpperBound.AuxiliaryLifetimePoint
import OnlineSteinerForest.UpperBound.AuxiliaryDirectPath

/-! The lifetime component uses exactly original input-edge weights and embeds in the input graph. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem lifetimeGraph_le_input (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (label : ℕ) :
    lifetimeGraph G c requests feasible label ≤ G := by
  intro u v huv
  exact G.mem_edgeSet.mp (lifetimeEdges_input G c requests feasible label s(u, v) huv.1)

theorem lifetimeComponent_weights_nonneg (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V) (label : ℕ) :
    ∀ e ∈ (lifetimeComponent G c requests feasible fallback label).toSimpleGraph.edgeSet,
      0 ≤ c (Sym2.map Subtype.val e) := by
  intro e
  refine Sym2.ind (fun u v huv => ?_) e
  exact hc s(u.val, v.val) (G.mem_edgeSet.mpr (lifetimeGraph_le_input G c requests feasible label huv))

end OnlineSteinerForest.UpperBound
