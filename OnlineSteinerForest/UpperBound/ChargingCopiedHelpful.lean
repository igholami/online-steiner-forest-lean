import OnlineSteinerForest.UpperBound.ChargingCopiedMetric
import OnlineSteinerForest.UpperBound.ChargingHelpfulMetric

/-! Assigned copied endpoints inherit actual helpful-pair separation and chronological zeros. -/
namespace OnlineSteinerForest.UpperBound

universe uSelection
variable [OnlineSteinerForest.PathSelection.{uSelection}]

open scoped Classical
variable {V W X : Type uSelection} {J : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

noncomputable def auxiliaryTimes {n : ℕ} (time : J ↪ Fin n) : J ↪ ℕ :=
  ⟨fun j => (time j).val, fun _ _ h => time.injective (Fin.val_injective h)⟩

variable (G : SimpleGraph V) (c : Sym2 V → ℝ) (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e)
  (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
  (E : Finset (Sym2 V)) (hE : ∀ e ∈ E, e ∈ G.edgeSet)
  (F : Finset (Sym2 W)) (d : Sym2 W → ℝ) (cert : ZoneSubdivisionCertificate E c F d)
  (hsep : ∀ e : Sym2 V, Sym2.map cert.vertices e ∉ F)
  (project : X → W) (left right : J → X) (time : J ↪ Fin requests.length)
  (out : J → AuxiliaryOutput V) (scale : ℝ)
  (helpful : ∀ j, HelpfulAt G c requests feasible (time j) scale (out j))
  (hleft : ∀ j, project (left j) = cert.vertices (out j).left)
  (hright : ∀ j, project (right j) = cert.vertices (out j).right)

include hc hE hsep helpful hleft hright

theorem copiedHelpful_separated (j : J) : ENNReal.ofReal (scale / 2) ≤
    copiedRequestMetric G c requests feasible cert.vertices F d project (auxiliaryTimes time j) (left j) (right j) := by
  unfold copiedRequestMetric
  rw [hleft, hright]
  exact (helpful j).expanded_separated hc E hE F d cert hsep

theorem copiedHelpful_prior_zero (i : ℕ) (j : J) (hji : auxiliaryTimes time j < i) :
    copiedRequestMetric G c requests feasible cert.vertices F d project i (left j) (right j) = 0 := by
  unfold copiedRequestMetric
  rw [hleft, hright]
  exact (helpful j).expanded_prior_zero hc E hE F d cert hsep i hji

theorem copiedHelpful_endpoints_ne (hd : ∀ e ∈ F, 0 ≤ d e) (hs : 0 < scale) (j : J) : left j ≠ right j := by
  intro heq
  have h := copiedHelpful_separated G c hc requests feasible E hE F d cert hsep project left right time out scale
    helpful hleft hright j
  rw [heq, copiedRequestMetric_refl G c hc requests feasible cert.vertices F d hsep hd] at h
  exact (not_le_of_gt (ENNReal.ofReal_pos.mpr (by linarith : 0 < scale / 2))) h

end OnlineSteinerForest.UpperBound
