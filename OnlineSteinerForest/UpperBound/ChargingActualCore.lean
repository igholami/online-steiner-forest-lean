import OnlineSteinerForest.UpperBound.ChargingCopiedHelpful
import OnlineSteinerForest.UpperBound.SparseCoreCharge

/-! Actual greedy helpful outputs charge every dense copied-reference core. -/
namespace OnlineSteinerForest.UpperBound

universe uSelection
variable [OnlineSteinerForest.PathSelection.{uSelection}]

open scoped Classical
variable {V W X : Type uSelection} {J : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype X] [DecidableEq X] [Fintype J] [DecidableEq J]
variable (G : SimpleGraph V) (c : Sym2 V → ℝ) (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e)
  (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
  (E : Finset (Sym2 V)) (hE : ∀ e ∈ E, e ∈ G.edgeSet)
  (F : Finset (Sym2 W)) (d : Sym2 W → ℝ) (cert : ZoneSubdivisionCertificate E c F d)
  (hsep : ∀ e : Sym2 V, Sym2.map cert.vertices e ∉ F) (hd : ∀ e ∈ F, 0 ≤ d e)
  (project : X → W) (H : SimpleGraph X) (hH : H.IsAcyclic)
  (href : ∀ u v, H.Adj u v → project u ≠ project v ∧ s(project u, project v) ∈ F)
  (left right : J → X) (time : J ↪ Fin requests.length) (out : J → AuxiliaryOutput V) (scale : ℝ)
  (helpful : ∀ j, HelpfulAt G c requests feasible (time j) scale (out j))
  (hleft : ∀ j, project (left j) = cert.vertices (out j).left)
  (hright : ∀ j, project (right j) = cert.vertices (out j).right)

include hc hE hsep hd hH href helpful hleft hright

theorem actual_copied_dense_charge (hs : 0 < scale)
    (hdense : 2 * Nat.card H.ConnectedComponent ≤ Fintype.card J) :
    (Fintype.card J : ℝ) * scale ≤ 16 * cycleFactor requests.length *
      edgeCost (copiedReferenceCost d project) H.edgeFinset := by
  apply charging_dense_count_scale_le H hH left right
    (copiedHelpful_endpoints_ne G c hc requests feasible E hE F d cert hsep project left right time out scale
      helpful hleft hright hd hs) (auxiliaryTimes time)
    (copiedReferenceCost d project) (copiedReferenceCost_nonneg d project)
    (copiedRequestMetric G c requests feasible cert.vertices F d project)
    (copiedRequestMetric_refl G c hc requests feasible cert.vertices F d hsep hd project)
    (copiedRequestMetric_symm G c requests feasible cert.vertices F d project)
    (copiedRequestMetric_triangle G c hc requests feasible cert.vertices F d hsep hd project)
    scale hs.le
    (copiedHelpful_separated G c hc requests feasible E hE F d cert hsep project left right time out scale
      helpful hleft hright)
    (copiedHelpful_prior_zero G c hc requests feasible E hE F d cert hsep project left right time out scale
      helpful hleft hright)
    (fun i {_ _} h => copiedRequestMetric_reference G c hc requests feasible cert.vertices F d hsep hd
      project H href i h) hdense requests.length
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective time time.injective

end OnlineSteinerForest.UpperBound
