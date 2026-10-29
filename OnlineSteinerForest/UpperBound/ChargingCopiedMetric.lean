import OnlineSteinerForest.UpperBound.ChargingExpandedFamily

/-! Pull the actual mixed residual metrics back to copied reference vertices. -/
namespace OnlineSteinerForest.UpperBound

universe uSelection
variable [OnlineSteinerForest.PathSelection.{uSelection}]

open scoped Classical
variable {V W X : Type uSelection} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

noncomputable def copiedRequestMetric (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (f : V ↪ W) (F : Finset (Sym2 W)) (d : Sym2 W → ℝ) (project : X → W)
    (i : ℕ) (u v : X) : ENNReal := expandedRequestMetric G c requests feasible f F d i (project u) (project v)

noncomputable def copiedReferenceCost (d : Sym2 W → ℝ) (project : X → W) (e : Sym2 X) : ℝ :=
  max (d (Sym2.map project e)) 0

theorem copiedReferenceCost_nonneg (d : Sym2 W → ℝ) (project : X → W) (e : Sym2 X) :
    0 ≤ copiedReferenceCost d project e := le_max_right _ _

theorem copiedRequestMetric_refl (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (f : V ↪ W) (F : Finset (Sym2 W)) (d : Sym2 W → ℝ)
    (hsep : ∀ e : Sym2 V, Sym2.map f e ∉ F) (hd : ∀ e ∈ F, 0 ≤ d e)
    (project : X → W) (i : ℕ) (u : X) : copiedRequestMetric G c requests feasible f F d project i u u = 0 :=
  expandedRequestMetric_refl G c hc requests feasible f F d hsep hd i (project u)

theorem copiedRequestMetric_symm (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (f : V ↪ W) (F : Finset (Sym2 W)) (d : Sym2 W → ℝ)
    (project : X → W) (i : ℕ) (u v : X) : copiedRequestMetric G c requests feasible f F d project i u v =
      copiedRequestMetric G c requests feasible f F d project i v u :=
  expandedRequestMetric_symm G c requests feasible f F d i (project u) (project v)

theorem copiedRequestMetric_triangle (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (f : V ↪ W) (F : Finset (Sym2 W)) (d : Sym2 W → ℝ)
    (hsep : ∀ e : Sym2 V, Sym2.map f e ∉ F) (hd : ∀ e ∈ F, 0 ≤ d e)
    (project : X → W) (i : ℕ) (u v z : X) :
    copiedRequestMetric G c requests feasible f F d project i u z ≤
      copiedRequestMetric G c requests feasible f F d project i u v +
        copiedRequestMetric G c requests feasible f F d project i v z :=
  expandedRequestMetric_triangle G c hc requests feasible f F d hsep hd i (project u) (project v) (project z)

theorem copiedRequestMetric_reference (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (f : V ↪ W) (F : Finset (Sym2 W)) (d : Sym2 W → ℝ)
    (hsep : ∀ e : Sym2 V, Sym2.map f e ∉ F) (hd : ∀ e ∈ F, 0 ≤ d e)
    (project : X → W) (H : SimpleGraph X)
    (href : ∀ u v, H.Adj u v → project u ≠ project v ∧ s(project u, project v) ∈ F)
    (i : ℕ) {u v : X} (huv : H.Adj u v) :
    copiedRequestMetric G c requests feasible f F d project i u v ≤
      ENNReal.ofReal (copiedReferenceCost d project s(u, v)) := by
  have h := mixedResidualMetric_reference G c hc F d f hsep hd
    (boughtBefore G c requests feasible i) (href u v huv).1 (href u v huv).2
  exact h.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))

end OnlineSteinerForest.UpperBound
