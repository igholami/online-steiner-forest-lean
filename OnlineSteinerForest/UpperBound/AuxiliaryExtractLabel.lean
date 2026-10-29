import OnlineSteinerForest.UpperBound.AuxiliaryOutput
import OnlineSteinerForest.UpperBound.AuxiliaryProxyChronology
import OnlineSteinerForest.UpperBound.AuxiliaryDirectPath

/-! Execute the manuscript's direct/first/long/proxy extraction branches for a label batch. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

def predecessorPosition {n : ℕ} (j : Fin (n + 1)) (hj : j.val ≠ 0) : Fin n := ⟨j.val - 1, by omega⟩

theorem newIndex_predecessorPosition {n : ℕ} (j : Fin (n + 1)) (hj : j.val ≠ 0) :
    newIndex (predecessorPosition j hj) = j := by apply Fin.ext; simp [newIndex, predecessorPosition]; omega

noncomputable def directAuxOutput (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (i : Fin requests.length)
    (hp : 0 < blockPayment G c requests feasible i.val) : AuxiliaryOutput V :=
  ⟨requests[i.val].1, requests[i.val].2, directAuxEdges G c hc requests feasible i hp⟩

noncomputable def proxyAuxOutput (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (batch : Finset (Fin requests.length)) (label : ℕ) {n : ℕ}
    (hcard : (labelBatch G c requests feasible batch label).card = n + 1) (j : Fin n) : AuxiliaryOutput V :=
  ⟨(labelFarSequence G c hc requests feasible fallback batch label hcard (newIndex j)).val,
    (labelFarSequence G c hc requests feasible fallback batch label hcard
      (labelProxyParent G c hc requests feasible fallback batch label hcard j)).val,
    labelProxyEdges G c hc requests feasible fallback batch label hcard j⟩

noncomputable def extractLabelAux (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (batch : Finset (Fin requests.length)) (label : ℕ) {n : ℕ}
    (hcard : (labelBatch G c requests feasible batch label).card = n + 1) (scale : ℝ) (j : Fin (n + 1)) :
    Option (AuxiliaryOutput V) :=
  let i := orderedLabelRequest G c requests feasible batch label hcard j
  let hp := (Finset.mem_filter.mp (orderedLabelRequest_mem G c requests feasible batch label hcard j)).2.1
  if clusterWeight (blockPayment G c requests feasible) (finalLifetime G c requests feasible label) ≤
      64 * (cycleFactor requests.length : ℝ) ^ 2 * payment G c requests feasible i then
    some (directAuxOutput G c hc requests feasible i hp)
  else if hzero : j.val = 0 then none
  else if 256 * (cycleFactor requests.length : ℝ) ^ 3 * scale <
      labelProxyLength G c hc requests feasible fallback batch label hcard (predecessorPosition j hzero) then none
  else some (proxyAuxOutput G c hc requests feasible fallback batch label hcard (predecessorPosition j hzero))

end OnlineSteinerForest.UpperBound
