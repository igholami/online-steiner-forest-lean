import OnlineSteinerForest.UpperBound.AuxiliaryExtractCorrect
import OnlineSteinerForest.UpperBound.AuxiliaryRequestPosition

/-! Execute auxiliary extraction at original request indices, including births. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def extractAuxiliary (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (batch : Finset (Fin requests.length)) (scale : ℝ) (i : Fin requests.length) : Option (AuxiliaryOutput V) :=
  if hi : i ∈ batch then
    if hp : 0 < blockPayment G c requests feasible i.val then
      if hb : isBirth G c requests feasible i.val then some (directAuxOutput G c hc requests feasible i hp)
      else
        let label := pairLabel G c requests feasible i.val
        let hiS : i ∈ labelBatch G c requests feasible batch label := Finset.mem_filter.mpr
          ⟨hi, hp, Finset.nonempty_iff_ne_empty.mpr hb, rfl⟩
        let hcard : (labelBatch G c requests feasible batch label).card =
            (labelBatch G c requests feasible batch label).card - 1 + 1 := by
          have := Finset.card_pos.mpr ⟨i, hiS⟩; omega
        extractLabelAux G c hc requests feasible fallback batch label hcard scale
          (labelPosition G c requests feasible batch label hcard i hiS)
    else none
  else none

noncomputable def retainedAuxRequests (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (batch : Finset (Fin requests.length)) (scale : ℝ) : Finset (Fin requests.length) :=
  batch.filter (fun i => (extractAuxiliary G c hc requests feasible fallback batch scale i).isSome)

noncomputable def retainedAuxOutput (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (batch : Finset (Fin requests.length)) (scale : ℝ) (i : Fin requests.length)
    (hi : i ∈ retainedAuxRequests G c hc requests feasible fallback batch scale) : AuxiliaryOutput V :=
  (extractAuxiliary G c hc requests feasible fallback batch scale i).get (Finset.mem_filter.mp hi).2

end OnlineSteinerForest.UpperBound
