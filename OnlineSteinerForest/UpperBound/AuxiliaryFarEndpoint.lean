import OnlineSteinerForest.UpperBound.AuxiliaryNearest
import OnlineSteinerForest.UpperBound.AuxiliaryAfterStep

/-! Explicit far-endpoint choice and the actual before/after proxy separation. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def farEndpoint (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (B : Finset (Sym2 V)) (s t : V) (hst : G.Reachable s t)
    (C : Finset V) (hsC : ∀ v ∈ C, G.Reachable s v) : V :=
  if ∀ (w : V) (hw : w ∈ C), residualDistance G c B s t hst / 2 ≤
    residualDistance G c B s w (hsC w hw) then s else t

theorem farEndpoint_eq (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (B : Finset (Sym2 V)) (s t : V) (hst : G.Reachable s t)
    (C : Finset V) (hsC : ∀ v ∈ C, G.Reachable s v) :
    farEndpoint G c B s t hst C hsC = s ∨ farEndpoint G c B s t hst C hsC = t := by
  unfold farEndpoint
  split_ifs <;> simp

theorem farEndpoint_reachable (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (B : Finset (Sym2 V)) (s t : V) (hst : G.Reachable s t)
    (C : Finset V) (hsC : ∀ v ∈ C, G.Reachable s v) (w : V) (hw : w ∈ C) :
    G.Reachable (farEndpoint G c B s t hst C hsC) w := by
  rcases farEndpoint_eq G c B s t hst C hsC with h | h <;> rw [h]
  · exact hsC w hw
  · exact hst.symm.trans (hsC w hw)

/-- A proxy to any vertex of the touched old component has half-payment
separation before this actual greedy step and residual distance zero after it. -/
theorem farEndpoint_proxy (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (B : Finset (Sym2 V))
    (hB : ∀ e ∈ B, e ∈ G.edgeSet) (s t : V) (hst : G.Reachable s t)
    (C : Finset V) (hC : C.Nonempty) (hsC : ∀ v ∈ C, G.Reachable s v)
    (hCC : ∀ u ∈ C, ∀ v ∈ C,
      (SimpleGraph.fromEdgeSet (B : Set (Sym2 V))).Reachable u v)
    (p : G.Walk s t) (heq : p.edges.toFinset = shortestPathEdges G c B s t hst)
    (htouch : ∃ w ∈ C, w ∈ p.support) (w : V) (hw : w ∈ C) :
    residualDistance G c B s t hst / 2 ≤
      residualDistance G c B (farEndpoint G c B s t hst C hsC) w
        (farEndpoint_reachable G c B s t hst C hsC w hw) ∧
    residualDistance G c (greedyStep G c B s t hst)
      (farEndpoint G c B s t hst C hsC) w
        (farEndpoint_reachable G c B s t hst C hsC w hw) = 0 := by
  have hfar := one_endpoint_far G c hc B hB s t hst C hC hsC hCC
  have hzero := greedyStep_residual_zero_to_component G c hc B hB s t hst C hsC hCC p heq htouch w hw
  unfold farEndpoint
  split_ifs with hs
  · exact ⟨hs w hw, hzero.1⟩
  · exact ⟨(hfar.resolve_left hs) w hw, hzero.2⟩

end OnlineSteinerForest.UpperBound
