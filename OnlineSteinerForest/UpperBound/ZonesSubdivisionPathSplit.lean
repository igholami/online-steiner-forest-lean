import OnlineSteinerForest.UpperBound.ZonesSubdivisionMixedGraph

/-! Every mixed ambient edge set separates into reference fragments and original edges. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]

noncomputable def mixedOriginalPart (G : SimpleGraph V) (f : V ↪ W)
    (P : Finset (Sym2 W)) : Finset (Sym2 V) := G.edgeFinset.filter (fun e => Sym2.map f e ∈ P)

theorem mixedOriginalPart_image (G : SimpleGraph V) (f : V ↪ W) (F P : Finset (Sym2 W))
    (hsep : ∀ e : Sym2 V, Sym2.map f e ∉ F)
    (hP : ∀ e ∈ P, e ∈ (mixedSubdivisionGraph G f F).edgeSet) :
    (mixedOriginalPart G f P).image (Sym2.map f) = P \ F := by
  ext x
  constructor
  · intro hx
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp he).2, hsep e⟩
  · intro hx
    obtain ⟨hxP, hxF⟩ := Finset.mem_sdiff.mp hx
    have hxset : x ∈ ((F ∪ G.edgeFinset.image (Sym2.map f) : Finset (Sym2 W)) : Set (Sym2 W)) \ Sym2.diagSet := by
      simpa only [mixedSubdivisionGraph, SimpleGraph.edgeSet_fromEdgeSet] using hP x hxP
    obtain ⟨e, he, heq⟩ := Finset.mem_image.mp ((Finset.mem_union.mp hxset.1).resolve_left hxF)
    exact Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨he, heq.symm ▸ hxP⟩, heq⟩

theorem mixed_path_split (G : SimpleGraph V) (f : V ↪ W) (F P : Finset (Sym2 W))
    (hsep : ∀ e : Sym2 V, Sym2.map f e ∉ F)
    (hP : ∀ e ∈ P, e ∈ (mixedSubdivisionGraph G f F).edgeSet) :
    P ∩ F ∪ (mixedOriginalPart G f P).image (Sym2.map f) = P := by
  rw [mixedOriginalPart_image G f F P hsep hP]
  ext x
  simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
  tauto

end OnlineSteinerForest.UpperBound
