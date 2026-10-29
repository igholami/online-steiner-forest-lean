import OnlineSteinerForest.UpperBound.ZoneCopiesSupport

/-! Pruning a zone to its spanning tree never increases its original reference cost. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {W : Type*} [Fintype W] [DecidableEq W]

theorem zone_copy_tree_cost (F : Finset (Sym2 W)) (T : SimpleGraph (ZoneSupportVertex F))
    (hT : T ≤ zoneSupportGraph F) (c : Sym2 W → ℝ) (hc : ∀ e ∈ F, 0 ≤ c e) :
    edgeCost (fun e => c (Sym2.map Subtype.val e)) T.edgeFinset ≤ edgeCost c F := by
  let f : Sym2 (ZoneSupportVertex F) → Sym2 W := Sym2.map Subtype.val
  have hinj : Function.Injective f := Sym2.map.injective Subtype.val_injective
  have hsub : T.edgeFinset.image f ⊆ F := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
    have hmap : ∀ e : Sym2 (ZoneSupportVertex F), e ∈ T.edgeSet → f e ∈ F := by
      intro e
      refine Sym2.ind (fun a b hab => ?_) e
      exact (hT hab).1
    exact hmap e (T.mem_edgeFinset.mp he)
  calc
    _ = edgeCost c (T.edgeFinset.image f) :=
      (Finset.sum_image (fun _ _ _ _ h => hinj h)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun e he _ => hc e he)

end OnlineSteinerForest.UpperBound
