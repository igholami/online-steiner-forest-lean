import OnlineSteinerForest.Graph.Paths

/-! Extend a prescribed tie rule on one input graph to a global path selector. -/
namespace OnlineSteinerForest

universe u
variable {V : Type u} [fv : Fintype V] [dv : DecidableEq V]

noncomputable def overridePathChoice (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (p : ∀ B : Finset (Sym2 V), ∀ s t : V, G.Reachable s t → Finset (Sym2 V))
    {W : Type u} [fw : Fintype W] [dw : DecidableEq W]
    (H : SimpleGraph W) (d : Sym2 W → ℝ) (B : Finset (Sym2 W))
    (s t : W) (h : H.Reachable s t) : Finset (Sym2 W) := by
  classical
  by_cases hv : W = V
  · subst W
    by_cases hg : H = G
    · subst H
      by_cases hc : d = c
      · subst d
        exact p B s t h
      · exact canonicalPathSelection.choose G d B s t h
    · exact canonicalPathSelection.choose H d B s t h
  · exact canonicalPathSelection.choose H d B s t h

theorem overridePathChoice_spec (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (p : ∀ B : Finset (Sym2 V), ∀ s t : V, G.Reachable s t → Finset (Sym2 V))
    (hp : ∀ B s t h, IsPathEdges G s t (p B s t h) ∧
      ∀ F, IsPathEdges G s t F → residualCost c B (p B s t h) ≤ residualCost c B F)
    {W : Type u} [fw : Fintype W] [dw : DecidableEq W]
    (H : SimpleGraph W) (d : Sym2 W → ℝ) (B : Finset (Sym2 W))
    (s t : W) (h : H.Reachable s t) :
    IsPathEdges H s t (overridePathChoice G c p H d B s t h) ∧
      ∀ F, IsPathEdges H s t F →
        residualCost d B (overridePathChoice G c p H d B s t h) ≤ residualCost d B F := by
  classical
  by_cases hv : W = V
  · subst W
    have hd : dw = dv := Subsingleton.elim _ _
    cases hd
    by_cases hg : H = G
    · subst H
      by_cases hc : d = c
      · subst d
        simpa [overridePathChoice] using hp B s t h
      · simpa [overridePathChoice, hc] using canonicalPathSelection.spec G d B s t h
    · simpa [overridePathChoice, hg] using canonicalPathSelection.spec H d B s t h
  · simpa [overridePathChoice, hv] using canonicalPathSelection.spec H d B s t h

noncomputable def overridePathSelection (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (p : ∀ B : Finset (Sym2 V), ∀ s t : V, G.Reachable s t → Finset (Sym2 V))
    (hp : ∀ B s t h, IsPathEdges G s t (p B s t h) ∧
      ∀ F, IsPathEdges G s t F → residualCost c B (p B s t h) ≤ residualCost c B F) :
    PathSelection.{u} where
  choose := overridePathChoice G c p
  spec := overridePathChoice_spec G c p hp

@[simp] theorem overridePathSelection_choose (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (p : ∀ B : Finset (Sym2 V), ∀ s t : V, G.Reachable s t → Finset (Sym2 V))
    (hp : ∀ B s t h, IsPathEdges G s t (p B s t h) ∧
      ∀ F, IsPathEdges G s t F → residualCost c B (p B s t h) ≤ residualCost c B F)
    (B : Finset (Sym2 V)) (s t : V) (h : G.Reachable s t) :
    (overridePathSelection G c p hp).choose G c B s t h = p B s t h := by
  classical
  simp [overridePathSelection, overridePathChoice]

end OnlineSteinerForest
