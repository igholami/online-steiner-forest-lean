import OnlineSteinerForest.UpperBound.ZonesSubdivisionMetric
import OnlineSteinerForest.UpperBound.ThresholdGreedyMetric

/-! The actual mixed residual metric preserves original auxiliary separation and zero distances. -/
namespace OnlineSteinerForest.UpperBound

universe uSelection
variable [OnlineSteinerForest.PathSelection.{uSelection}]

open scoped Classical
variable {V W : Type uSelection} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

noncomputable def mixedResidualMetric (G : SimpleGraph V) (f : V ↪ W) (F : Finset (Sym2 W))
    (d : Sym2 W → ℝ) (c : Sym2 V → ℝ) (B : Finset (Sym2 V)) : W → W → ENNReal :=
  residualEDistance (mixedSubdivisionGraph G f F) (mixedSubdivisionCost f F d c) (B.image (Sym2.map f))

theorem mixedResidualMetric_embedded (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (E : Finset (Sym2 V)) (hE : ∀ e ∈ E, e ∈ G.edgeSet)
    (F : Finset (Sym2 W)) (d : Sym2 W → ℝ) (cert : ZoneSubdivisionCertificate E c F d)
    (hsep : ∀ e : Sym2 V, Sym2.map cert.vertices e ∉ F) (B : Finset (Sym2 V))
    (a b : V) (hab : G.Reachable a b) :
    mixedResidualMetric G cert.vertices F d c B (cert.vertices a) (cert.vertices b) =
      ENNReal.ofReal (residualDistance G c B a b hab) := by
  have hm : (mixedSubdivisionGraph G cert.vertices F).Reachable (cert.vertices a) (cert.vertices b) :=
    hab.map (mixedOriginalHom G cert.vertices F)
  rw [mixedResidualMetric, residualEDistance_of_reachable _ _ _ _ _ hm,
    residualDistance_subdivision_eq G c hc E hE F d cert hsep B a b hab hm]

theorem mixedResidualMetric_reference (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (F : Finset (Sym2 W)) (d : Sym2 W → ℝ)
    (f : V ↪ W) (hsep : ∀ e : Sym2 V, Sym2.map f e ∉ F) (hd : ∀ e ∈ F, 0 ≤ d e)
    (B : Finset (Sym2 V)) {a b : W} (hab : a ≠ b) (he : s(a, b) ∈ F) :
    mixedResidualMetric G f F d c B a b ≤ ENNReal.ofReal (d s(a, b)) := by
  have hm : (mixedSubdivisionGraph G f F).Adj a b := ⟨Finset.mem_union_left _ he, hab⟩
  have h := residualEDistance_adj_le _ _ (mixedSubdivisionGraph_nonneg G f F d c hsep hd hc)
    (B.image (Sym2.map f)) hm
  rwa [mixedSubdivisionCost_reference f F d c he] at h

end OnlineSteinerForest.UpperBound
