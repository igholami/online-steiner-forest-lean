import OnlineSteinerForest.UpperBound.ZonesSubdivisionResidualPath

/-! Subdivision cannot decrease pre-step separation between embedded original vertices. -/
namespace OnlineSteinerForest.UpperBound

universe uSelection
variable [OnlineSteinerForest.PathSelection.{uSelection}]

open scoped Classical
variable {V W : Type uSelection} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

theorem residualDistance_le_subdivision (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (E : Finset (Sym2 V))
    (hE : ∀ e ∈ E, e ∈ G.edgeSet) (F : Finset (Sym2 W)) (d : Sym2 W → ℝ)
    (cert : ZoneSubdivisionCertificate E c F d)
    (hsep : ∀ e : Sym2 V, Sym2.map cert.vertices e ∉ F)
    (B : Finset (Sym2 V)) (a b : V) (hab : G.Reachable a b)
    (hm : (mixedSubdivisionGraph G cert.vertices F).Reachable (cert.vertices a) (cert.vertices b)) :
    residualDistance G c B a b hab ≤
      residualDistance (mixedSubdivisionGraph G cert.vertices F) (mixedSubdivisionCost cert.vertices F d c)
        (B.image (Sym2.map cert.vertices)) (cert.vertices a) (cert.vertices b) hm :=
  residualDistance_le_mixed_path G c hc E hE F d cert hsep B a b hab _
    (shortestPathEdges_spec _ _ _ _ _ hm).1

end OnlineSteinerForest.UpperBound
