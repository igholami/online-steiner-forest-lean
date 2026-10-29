import OnlineSteinerForest.UpperBound.ChargingExpandedFamily
import OnlineSteinerForest.UpperBound.AuxiliaryEarlierZero

/-! Actual retained helpful outputs supply the mixed charging metric chronology. -/
namespace OnlineSteinerForest.UpperBound

universe uSelection
variable [OnlineSteinerForest.PathSelection.{uSelection}]

open scoped Classical
variable {V W : Type uSelection} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

theorem HelpfulAt.expanded_separated {G : SimpleGraph V} {c : Sym2 V → ℝ}
    {requests : List (V × V)} {feasible : ∀ q ∈ requests, G.Reachable q.1 q.2}
    {i : Fin requests.length} {scale : ℝ} {out : AuxiliaryOutput V}
    (h : HelpfulAt G c requests feasible i scale out)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (E : Finset (Sym2 V)) (hE : ∀ e ∈ E, e ∈ G.edgeSet)
    (F : Finset (Sym2 W)) (d : Sym2 W → ℝ) (cert : ZoneSubdivisionCertificate E c F d)
    (hsep : ∀ e : Sym2 V, Sym2.map cert.vertices e ∉ F) :
    ENNReal.ofReal (scale / 2) ≤ expandedRequestMetric G c requests feasible cert.vertices F d i.val
      (cert.vertices out.left) (cert.vertices out.right) := by
  rw [expandedRequestMetric, mixedResidualMetric_embedded G c hc E hE F d cert hsep _ _ _ h.reachable]
  exact ENNReal.ofReal_le_ofReal h.separated

theorem HelpfulAt.expanded_prior_zero {G : SimpleGraph V} {c : Sym2 V → ℝ}
    {requests : List (V × V)} {feasible : ∀ q ∈ requests, G.Reachable q.1 q.2}
    {i : Fin requests.length} {scale : ℝ} {out : AuxiliaryOutput V}
    (h : HelpfulAt G c requests feasible i scale out)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (E : Finset (Sym2 V)) (hE : ∀ e ∈ E, e ∈ G.edgeSet)
    (F : Finset (Sym2 W)) (d : Sym2 W → ℝ) (cert : ZoneSubdivisionCertificate E c F d)
    (hsep : ∀ e : Sym2 V, Sym2.map cert.vertices e ∉ F) (j : ℕ) (hij : i.val < j) :
    expandedRequestMetric G c requests feasible cert.vertices F d j
      (cert.vertices out.left) (cert.vertices out.right) = 0 := by
  rw [expandedRequestMetric, mixedResidualMetric_embedded G c hc E hE F d cert hsep _ _ _ h.reachable,
    h.before_zero_of_lt hc j hij]
  simp

end OnlineSteinerForest.UpperBound
