import OnlineSteinerForest.UpperBound.ZonesSubdivisionMixedCost

/-! The ambient graph contains reference segments and embedded original auxiliary paths. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]

def mixedSubdivisionGraph (G : SimpleGraph V) (f : V ↪ W) (F : Finset (Sym2 W)) : SimpleGraph W :=
  SimpleGraph.fromEdgeSet ((F ∪ G.edgeFinset.image (Sym2.map f) : Finset (Sym2 W)) : Set (Sym2 W))

def mixedOriginalHom (G : SimpleGraph V) (f : V ↪ W) (F : Finset (Sym2 W)) :
    G →g mixedSubdivisionGraph G f F where
  toFun := f
  map_rel' {u v} huv := ⟨Finset.mem_union_right _ (Finset.mem_image.mpr
    ⟨s(u, v), G.mem_edgeFinset.mpr huv, rfl⟩), f.injective.ne huv.ne⟩

theorem mixedOriginalWalk_cost (G : SimpleGraph V) (f : V ↪ W) (F : Finset (Sym2 W))
    (d : Sym2 W → ℝ) (c : Sym2 V → ℝ) (hsep : ∀ e : Sym2 V, Sym2.map f e ∉ F)
    {a b : V} (p : G.Walk a b) :
    walkCost (mixedSubdivisionCost f F d c) (p.map (mixedOriginalHom G f F)) = walkCost c p := by
  rw [walkCost_map]
  congr 1
  funext e
  exact mixedSubdivisionCost_original f F d c hsep e

theorem mixedSubdivisionGraph_nonneg (G : SimpleGraph V) (f : V ↪ W) (F : Finset (Sym2 W))
    (d : Sym2 W → ℝ) (c : Sym2 V → ℝ) (hsep : ∀ e : Sym2 V, Sym2.map f e ∉ F)
    (hd : ∀ e ∈ F, 0 ≤ d e) (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) :
    ∀ x ∈ (mixedSubdivisionGraph G f F).edgeSet, 0 ≤ mixedSubdivisionCost f F d c x := by
  intro x hx
  have hxset : x ∈ ((F ∪ G.edgeFinset.image (Sym2.map f) : Finset (Sym2 W)) : Set (Sym2 W)) \ Sym2.diagSet := by
    simpa only [mixedSubdivisionGraph, SimpleGraph.edgeSet_fromEdgeSet] using hx
  have hx' : x ∈ F ∪ G.edgeFinset.image (Sym2.map f) := hxset.1
  exact mixedSubdivisionCost_nonneg f F d c G.edgeFinset hsep hd
    (fun e he => hc e (G.mem_edgeFinset.mp he)) x hx'

end OnlineSteinerForest.UpperBound
