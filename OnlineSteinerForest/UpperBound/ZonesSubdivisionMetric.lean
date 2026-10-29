import OnlineSteinerForest.UpperBound.ZonesSubdivisionResidual

/-! Embedded original vertices have exactly the original greedy residual distance. -/
namespace OnlineSteinerForest.UpperBound

universe uSelection
variable [OnlineSteinerForest.PathSelection.{uSelection}]

set_option backward.isDefEq.respectTransparency.types false

open scoped Classical
variable {V W : Type uSelection} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

theorem IsPathEdges.mixed {G : SimpleGraph V} {a b : V} {P : Finset (Sym2 V)}
    (hp : IsPathEdges G a b P) (f : V ↪ W) (F : Finset (Sym2 W)) :
    IsPathEdges (mixedSubdivisionGraph G f F) (f a) (f b) (P.image (Sym2.map f)) := by
  obtain ⟨p, hpath, rfl⟩ := hp
  refine ⟨p.map (mixedOriginalHom G f F), hpath.map f.injective, ?_⟩
  have he := p.edges_map (mixedOriginalHom G f F)
  apply (congrArg List.toFinset he).trans
  ext e
  simp [Finset.mem_image, List.mem_map, mixedOriginalHom]

theorem residualDistance_subdivision_le (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (F : Finset (Sym2 W)) (d : Sym2 W → ℝ) (f : V ↪ W)
    (hsep : ∀ e : Sym2 V, Sym2.map f e ∉ F) (B : Finset (Sym2 V)) (a b : V)
    (hab : G.Reachable a b) (hm : (mixedSubdivisionGraph G f F).Reachable (f a) (f b)) :
    residualDistance (mixedSubdivisionGraph G f F) (mixedSubdivisionCost f F d c)
      (B.image (Sym2.map f)) (f a) (f b) hm ≤ residualDistance G c B a b hab := by
  let P := shortestPathEdges G c B a b hab
  have hp := (shortestPathEdges_spec G c B a b hab).1
  calc
    _ ≤ residualCost (mixedSubdivisionCost f F d c) (B.image (Sym2.map f)) (P.image (Sym2.map f)) :=
      (shortestPathEdges_spec _ _ _ _ _ hm).2 _ (IsPathEdges.mixed hp f F)
    _ = _ := mixedSubdivision_residual_original f F d c hsep B P

theorem residualDistance_subdivision_eq (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (E : Finset (Sym2 V))
    (hE : ∀ e ∈ E, e ∈ G.edgeSet) (F : Finset (Sym2 W)) (d : Sym2 W → ℝ)
    (cert : ZoneSubdivisionCertificate E c F d)
    (hsep : ∀ e : Sym2 V, Sym2.map cert.vertices e ∉ F)
    (B : Finset (Sym2 V)) (a b : V) (hab : G.Reachable a b)
    (hm : (mixedSubdivisionGraph G cert.vertices F).Reachable (cert.vertices a) (cert.vertices b)) :
    residualDistance (mixedSubdivisionGraph G cert.vertices F) (mixedSubdivisionCost cert.vertices F d c)
      (B.image (Sym2.map cert.vertices)) (cert.vertices a) (cert.vertices b) hm =
      residualDistance G c B a b hab :=
  le_antisymm (residualDistance_subdivision_le G c F d cert.vertices hsep B a b hab hm)
    (residualDistance_le_subdivision G c hc E hE F d cert hsep B a b hab hm)

end OnlineSteinerForest.UpperBound
