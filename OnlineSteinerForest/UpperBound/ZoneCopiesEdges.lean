import OnlineSteinerForest.UpperBound.ZoneCopiesGraph
import OnlineSteinerForest.Graph.Cost

/-! The reference graph's edges are precisely the disjoint copied tree edges. -/
namespace OnlineSteinerForest.UpperBound

open scoped Classical
variable {Z : Type*} {A : Z → Type*} [Fintype Z] [∀ z, Fintype (A z)] [DecidableEq Z]
  [∀ z, DecidableEq (A z)]

noncomputable def zoneCopiedEdges (T : ∀ z, SimpleGraph (A z)) (z : Z) : Finset (Sym2 (Σ z, A z)) :=
  (T z).edgeFinset.image (Sym2.map (Sigma.mk z))

theorem zoneCopyGraph_edges (T : ∀ z, SimpleGraph (A z)) :
    (zoneCopyGraph T).edgeFinset = Finset.univ.biUnion (zoneCopiedEdges T) := by
  ext e
  constructor
  · refine Sym2.ind (fun x y he => ?_) e
    obtain ⟨z, u, v, huv, rfl, rfl⟩ := (zoneCopyGraph T).mem_edgeFinset.mp he
    exact Finset.mem_biUnion.mpr ⟨z, Finset.mem_univ _,
      Finset.mem_image.mpr ⟨s(u, v), (T z).mem_edgeFinset.mpr huv, rfl⟩⟩
  · intro he
    obtain ⟨z, hz, hez⟩ := Finset.mem_biUnion.mp he
    obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp hez
    rw [← hfe]
    exact (zoneCopyGraph T).mem_edgeFinset.mpr
      ((zoneCopyInclusion T z).map_mem_edgeSet_iff.mpr ((T z).mem_edgeFinset.mp hf))

end OnlineSteinerForest.UpperBound
