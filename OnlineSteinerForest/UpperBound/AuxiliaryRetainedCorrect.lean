import OnlineSteinerForest.UpperBound.AuxiliaryExtract
import OnlineSteinerForest.UpperBound.AuxiliaryEndpointOrigins

/-! Every retained original request is assigned an actual helpful auxiliary output. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem extractAuxiliary_helpful (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (batch : Finset (Fin requests.length)) (scale : ℝ) (hs : 0 ≤ scale)
    (hbatch : ∀ i ∈ batch, scale ≤ payment G c requests feasible i ∧ payment G c requests feasible i ≤ 2 * scale)
    (i : Fin requests.length) (out : AuxiliaryOutput V)
    (hout : extractAuxiliary G c hc requests feasible fallback batch scale i = some out) :
    HelpfulAt G c requests feasible i scale out := by
  unfold extractAuxiliary at hout
  split_ifs at hout with hi hp hb
  · have heq := Option.some.inj hout
    subst out
    exact directAuxOutput_helpful G c hc requests feasible i hp scale hs (hbatch i hi).1 (hbatch i hi).2 (Or.inl hb)
  · have hcorrect := extractLabelAux_helpful G c hc requests feasible fallback batch _ _ scale hs hbatch _ out hout
    convert hcorrect using 1
    exact (orderedLabelRequest_labelPosition G c requests feasible batch _ _ i _).symm

theorem retainedAuxOutput_helpful (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (batch : Finset (Fin requests.length)) (scale : ℝ) (hs : 0 ≤ scale)
    (hbatch : ∀ i ∈ batch, scale ≤ payment G c requests feasible i ∧ payment G c requests feasible i ≤ 2 * scale)
    (i : Fin requests.length) (hi : i ∈ retainedAuxRequests G c hc requests feasible fallback batch scale) :
    HelpfulAt G c requests feasible i scale (retainedAuxOutput G c hc requests feasible fallback batch scale i hi) := by
  apply extractAuxiliary_helpful G c hc requests feasible fallback batch scale hs hbatch i
  exact (Option.some_get (Finset.mem_filter.mp hi).2).symm

end OnlineSteinerForest.UpperBound
