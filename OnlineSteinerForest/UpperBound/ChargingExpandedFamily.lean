import OnlineSteinerForest.UpperBound.ChargingMixedMetric

/-! A global ENNReal metric family uses the actual original greedy prefix purchases. -/
namespace OnlineSteinerForest.UpperBound

universe uSelection
variable [OnlineSteinerForest.PathSelection.{uSelection}]

open scoped Classical
variable {V W : Type uSelection} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

noncomputable def expandedRequestMetric (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (f : V ↪ W) (F : Finset (Sym2 W)) (d : Sym2 W → ℝ) (i : ℕ) : W → W → ENNReal :=
  mixedResidualMetric G f F d c (boughtBefore G c requests feasible i)

theorem expandedRequestMetric_refl (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (f : V ↪ W) (F : Finset (Sym2 W)) (d : Sym2 W → ℝ)
    (hsep : ∀ e : Sym2 V, Sym2.map f e ∉ F) (hd : ∀ e ∈ F, 0 ≤ d e) (i : ℕ) (v : W) :
    expandedRequestMetric G c requests feasible f F d i v v = 0 :=
  residualEDistance_refl _ _ (mixedSubdivisionGraph_nonneg G f F d c hsep hd hc) _ v

theorem expandedRequestMetric_symm (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (f : V ↪ W) (F : Finset (Sym2 W)) (d : Sym2 W → ℝ) (i : ℕ) (u v : W) :
    expandedRequestMetric G c requests feasible f F d i u v =
      expandedRequestMetric G c requests feasible f F d i v u := residualEDistance_symm _ _ _ u v

theorem expandedRequestMetric_triangle (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (f : V ↪ W) (F : Finset (Sym2 W)) (d : Sym2 W → ℝ)
    (hsep : ∀ e : Sym2 V, Sym2.map f e ∉ F) (hd : ∀ e ∈ F, 0 ≤ d e) (i : ℕ) (u v z : W) :
    expandedRequestMetric G c requests feasible f F d i u z ≤
      expandedRequestMetric G c requests feasible f F d i u v +
        expandedRequestMetric G c requests feasible f F d i v z :=
  residualEDistance_triangle _ _ (mixedSubdivisionGraph_nonneg G f F d c hsep hd hc) _ u v z

end OnlineSteinerForest.UpperBound
