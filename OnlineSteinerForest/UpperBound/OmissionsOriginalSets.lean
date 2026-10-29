import OnlineSteinerForest.UpperBound.OmissionsLabelPayments
import OnlineSteinerForest.UpperBound.MassPaidLabels

/-! Express the budgeted omission positions as finite sets of original request indices. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def firstRequestsForLabel (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (batch : Finset (Fin requests.length)) (label : ℕ) : Finset (Fin requests.length) :=
  if h : (labelBatch G c requests feasible batch label).Nonempty then
    let hcard : (labelBatch G c requests feasible batch label).card =
        (labelBatch G c requests feasible batch label).card - 1 + 1 := by have := Finset.card_pos.mpr h; omega
    (firstLabelPositions G c requests feasible batch label hcard).image
      (orderedLabelRequest G c requests feasible batch label hcard)
  else ∅

noncomputable def longRequestsForLabel (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (batch : Finset (Fin requests.length)) (label : ℕ) (scale : ℝ) : Finset (Fin requests.length) :=
  if h : (labelBatch G c requests feasible batch label).Nonempty then
    let hcard : (labelBatch G c requests feasible batch label).card =
        (labelBatch G c requests feasible batch label).card - 1 + 1 := by have := Finset.card_pos.mpr h; omega
    (longLabelPositions G c hc requests feasible fallback batch label hcard scale).image
      (fun j => orderedLabelRequest G c requests feasible batch label hcard (newIndex j))
  else ∅

noncomputable def firstOmittedRequests (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (batch : Finset (Fin requests.length)) : Finset (Fin requests.length) :=
  (paidLabels G c requests feasible).biUnion (firstRequestsForLabel G c requests feasible batch)

noncomputable def longOmittedRequests (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (batch : Finset (Fin requests.length)) (scale : ℝ) : Finset (Fin requests.length) :=
  (paidLabels G c requests feasible).biUnion
    (fun label => longRequestsForLabel G c hc requests feasible fallback batch label scale)

end OnlineSteinerForest.UpperBound
