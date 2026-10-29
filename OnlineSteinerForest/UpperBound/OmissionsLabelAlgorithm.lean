import OnlineSteinerForest.UpperBound.NearestNeighborLabelParameter

/-! The first/long omission tests on each chronologically ordered actual label batch. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def labelProxyLength (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (batch : Finset (Fin requests.length)) (label : ℕ) {n : ℕ}
    (hcard : (labelBatch G c requests feasible batch label).card = n + 1) (j : Fin n) : ℝ :=
  insertionDistance (lifetimeComponent G c requests feasible fallback label).toSimpleGraph
    (fun e => c (Sym2.map Subtype.val e))
    (lifetimeComponent G c requests feasible fallback label).connected_toSimpleGraph.preconnected
    (labelFarSequence G c hc requests feasible fallback batch label hcard) j

noncomputable def longLabelPositions (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (batch : Finset (Fin requests.length)) (label : ℕ) {n : ℕ}
    (hcard : (labelBatch G c requests feasible batch label).card = n + 1) (scale : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun j =>
    256 * (cycleFactor requests.length : ℝ) ^ 3 * scale <
      labelProxyLength G c hc requests feasible fallback batch label hcard j ∧
    64 * (cycleFactor requests.length : ℝ) ^ 2 * blockPayment G c requests feasible
      (orderedLabelRequest G c requests feasible batch label hcard (newIndex j)).val <
        clusterWeight (blockPayment G c requests feasible) (finalLifetime G c requests feasible label))

noncomputable def firstLabelPositions (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (batch : Finset (Fin requests.length)) (label : ℕ) {n : ℕ}
    (hcard : (labelBatch G c requests feasible batch label).card = n + 1) : Finset (Fin (n + 1)) :=
  ({0} : Finset (Fin (n + 1))).filter (fun j =>
    64 * (cycleFactor requests.length : ℝ) ^ 2 * blockPayment G c requests feasible
      (orderedLabelRequest G c requests feasible batch label hcard j).val <
        clusterWeight (blockPayment G c requests feasible) (finalLifetime G c requests feasible label))

end OnlineSteinerForest.UpperBound
