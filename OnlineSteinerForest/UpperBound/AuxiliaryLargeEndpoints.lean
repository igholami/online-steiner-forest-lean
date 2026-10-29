import OnlineSteinerForest.UpperBound.AuxiliaryRetainedOrigins
import OnlineSteinerForest.UpperBound.AuxiliaryReferenceSplit

/-! Both retained auxiliary endpoints lie in large standard reference components. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem retained_large_endpoints (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (F : Finset (Sym2 V)) (batch : Finset (Fin requests.length)) (scale : ℝ)
    (hF : ∀ j ∈ batch, (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).Reachable requests[j.val].1 requests[j.val].2)
    (i : Fin requests.length)
    (hi : i ∈ retainedAuxRequests G c hc requests feasible fallback (largeReferencePairs c requests F batch scale) scale) :
    let out := retainedAuxOutput G c hc requests feasible fallback (largeReferencePairs c requests F batch scale) scale i hi
    65536 * (cycleFactor requests.length : ℝ) ^ 3 * scale ≤ referenceTreeCost F c out.left ∧
      65536 * (cycleFactor requests.length : ℝ) ^ 3 * scale ≤ referenceTreeCost F c out.right :=
  retainedAuxOutput_endpoints G c hc requests feasible fallback (largeReferencePairs c requests F batch scale) scale
    (fun v => 65536 * (cycleFactor requests.length : ℝ) ^ 3 * scale ≤ referenceTreeCost F c v)
    (largeReferencePairs_endpoints c requests F batch scale hF) i hi

end OnlineSteinerForest.UpperBound
