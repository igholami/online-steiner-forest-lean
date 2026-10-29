import OnlineSteinerForest.Graph.ResidualMetric
import Mathlib.Tactic.Linarith

/-! Nearest vertices in a finite bought component, using the actual residual distance. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def nearestIn (G : SimpleGraph V) (c : Sym2 V → ℝ) (B : Finset (Sym2 V))
    (s : V) (C : Finset V) (hC : C.Nonempty) (hsC : ∀ v ∈ C, G.Reachable s v) : ↥C :=
  Classical.choose ((Finset.univ : Finset ↥C).exists_min_image
    (fun v => residualDistance G c B s v.val (hsC v.val v.prop))
    ⟨⟨hC.choose, hC.choose_spec⟩, Finset.mem_univ _⟩)

noncomputable def distanceTo (G : SimpleGraph V) (c : Sym2 V → ℝ) (B : Finset (Sym2 V))
    (s : V) (C : Finset V) (hC : C.Nonempty) (hsC : ∀ v ∈ C, G.Reachable s v) : ℝ :=
  residualDistance G c B s (nearestIn G c B s C hC hsC).val
    (hsC _ (nearestIn G c B s C hC hsC).prop)

theorem distanceTo_le (G : SimpleGraph V) (c : Sym2 V → ℝ) (B : Finset (Sym2 V))
    (s : V) (C : Finset V) (hC : C.Nonempty) (hsC : ∀ v ∈ C, G.Reachable s v)
    (w : V) (hw : w ∈ C) :
    distanceTo G c B s C hC hsC ≤ residualDistance G c B s w (hsC w hw) := by
  exact (Classical.choose_spec ((Finset.univ : Finset ↥C).exists_min_image
    (fun v => residualDistance G c B s v.val (hsC v.val v.prop))
    ⟨⟨hC.choose, hC.choose_spec⟩, Finset.mem_univ _⟩)).2 ⟨w, hw⟩ (Finset.mem_univ _)

/-- A bought-connected set has residual diameter zero, so distances through its
nearest points bound the request's residual distance. -/
theorem residualDistance_le_distanceTo_add (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (B : Finset (Sym2 V))
    (hB : ∀ e ∈ B, e ∈ G.edgeSet) (s t : V) (hst : G.Reachable s t)
    (C : Finset V) (hC : C.Nonempty) (hsC : ∀ v ∈ C, G.Reachable s v)
    (hCC : ∀ u ∈ C, ∀ v ∈ C,
      (SimpleGraph.fromEdgeSet (B : Set (Sym2 V))).Reachable u v) :
    residualDistance G c B s t hst ≤ distanceTo G c B s C hC hsC +
      distanceTo G c B t C hC (fun v hv => hst.symm.trans (hsC v hv)) := by
  let a := nearestIn G c B s C hC hsC
  let b := nearestIn G c B t C hC (fun v hv => hst.symm.trans (hsC v hv))
  have hsa : G.Reachable s a := hsC a.val a.prop
  have htb : G.Reachable t b := hst.symm.trans (hsC b.val b.prop)
  have hab : G.Reachable a b := hsa.symm.trans (hsC b.val b.prop)
  have hat : G.Reachable a t := hsa.symm.trans hst
  have h1 := residualDistance_triangle G c hc B s a t hsa hat
  have h2 := residualDistance_triangle G c hc B a b t hab htb.symm
  have hzero := residualDistance_eq_zero_of_bought G c hc B hB a b hab
    (hCC a a.prop b b.prop)
  have hsym := residualDistance_symm G c B b t htb.symm
  change residualDistance G c B s t hst ≤ residualDistance G c B s a hsa +
    residualDistance G c B t b htb
  linarith

/-- At least one request endpoint is separated from every vertex of the old
component by half the current greedy payment (manuscript Lemma 4.1). -/
theorem one_endpoint_far (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (B : Finset (Sym2 V))
    (hB : ∀ e ∈ B, e ∈ G.edgeSet) (s t : V) (hst : G.Reachable s t)
    (C : Finset V) (hC : C.Nonempty) (hsC : ∀ v ∈ C, G.Reachable s v)
    (hCC : ∀ u ∈ C, ∀ v ∈ C,
      (SimpleGraph.fromEdgeSet (B : Set (Sym2 V))).Reachable u v) :
    (∀ (w : V) (hw : w ∈ C), residualDistance G c B s t hst / 2 ≤ residualDistance G c B s w (hsC w hw)) ∨
    (∀ (w : V) (hw : w ∈ C), residualDistance G c B s t hst / 2 ≤
      residualDistance G c B t w (hst.symm.trans (hsC w hw))) := by
  have hsum := residualDistance_le_distanceTo_add G c hc B hB s t hst C hC hsC hCC
  by_cases hs : residualDistance G c B s t hst / 2 ≤ distanceTo G c B s C hC hsC
  · exact Or.inl (fun w hw => hs.trans (distanceTo_le G c B s C hC hsC w hw))
  · right
    intro w hw
    have ht : residualDistance G c B s t hst / 2 ≤
        distanceTo G c B t C hC (fun v hv => hst.symm.trans (hsC v hv)) := by linarith
    exact ht.trans (distanceTo_le G c B t C hC _ w hw)

end OnlineSteinerForest.UpperBound
