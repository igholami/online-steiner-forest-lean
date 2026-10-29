import OnlineSteinerForest.UpperBound.SmallReferenceCost

/-! Select the actual large ordinary connected components of a finite reference forest. -/
namespace OnlineSteinerForest.UpperBound

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def largeForestComponents (F : SimpleGraph V) (c : Sym2 V → ℝ) (M : ℝ) : Finset F.ConnectedComponent :=
  (referenceComponents F).filter (fun C => M ≤ edgeCost c (componentEdges F C))

noncomputable def largeForestEdges (F : SimpleGraph V) (c : Sym2 V → ℝ) (M : ℝ) : Finset (Sym2 V) :=
  (largeForestComponents F c M).biUnion (componentEdges F)

theorem largeForestEdges_subset (F : SimpleGraph V) (c : Sym2 V → ℝ) (M : ℝ) :
    largeForestEdges F c M ⊆ F.edgeFinset := by
  intro e he
  obtain ⟨C, hC, he⟩ := Finset.mem_biUnion.mp he
  exact componentEdges_subset F C he

theorem largeForestComponent_mem (F : SimpleGraph V) (c : Sym2 V → ℝ) (M : ℝ) (r : V)
    (hr : M ≤ edgeCost c (componentEdges F (F.connectedComponentMk r))) :
    F.connectedComponentMk r ∈ largeForestComponents F c M :=
  Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_univ r), hr⟩

end OnlineSteinerForest.UpperBound
