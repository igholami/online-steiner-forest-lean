import OnlineSteinerForest.UpperBound.GirthComponentMaps

/-! Component equivalences from mutually inverse maps up to reachability. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

noncomputable def componentEquivOfRetractions (f : V → W) (g : W → V)
    (hf : ∀ u v, G.Adj u v → H.Reachable (f u) (f v))
    (hg : ∀ u v, H.Adj u v → G.Reachable (g u) (g v))
    (hgf : ∀ v, G.Reachable (g (f v)) v) (hfg : ∀ w, H.Reachable (f (g w)) w) :
    G.ConnectedComponent ≃ H.ConnectedComponent where
  toFun := componentMap f hf
  invFun := componentMap g hg
  left_inv C := by
    induction C using SimpleGraph.ConnectedComponent.ind with
    | h v => exact SimpleGraph.ConnectedComponent.sound (hgf v)
  right_inv C := by
    induction C using SimpleGraph.ConnectedComponent.ind with
    | h w => exact SimpleGraph.ConnectedComponent.sound (hfg w)

end OnlineSteinerForest.UpperBound.Girth
