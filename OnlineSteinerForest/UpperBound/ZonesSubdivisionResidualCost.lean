import OnlineSteinerForest.UpperBound.ZonesSubdivisionMixedGraph
import OnlineSteinerForest.Graph.ResidualBounds

/-! Residual costs split exactly into reference fragments and embedded original edges. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V W : Type*} [DecidableEq V] [DecidableEq W]

theorem residualCost_union_eq (c : Sym2 W → ℝ) (B H K : Finset (Sym2 W)) (hHK : Disjoint H K) :
    residualCost c B (H ∪ K) = residualCost c B H + residualCost c B K := by
  simp only [residualCost, Finset.union_sdiff_distrib]
  exact Finset.sum_union (hHK.mono Finset.sdiff_subset Finset.sdiff_subset)

theorem mixedSubdivision_residual_original (f : V ↪ W) (F : Finset (Sym2 W))
    (d : Sym2 W → ℝ) (c : Sym2 V → ℝ) (hsep : ∀ e : Sym2 V, Sym2.map f e ∉ F)
    (B K : Finset (Sym2 V)) :
    residualCost (mixedSubdivisionCost f F d c) (B.image (Sym2.map f)) (K.image (Sym2.map f)) =
      residualCost c B K := by
  rw [residualCost, ← Finset.image_sdiff K B (Sym2.map.injective f.injective)]
  rw [Finset.sum_image (fun _ _ _ _ h => Sym2.map.injective f.injective h)]
  exact Finset.sum_congr rfl (fun _ _ => mixedSubdivisionCost_original f F d c hsep _)

theorem mixedSubdivision_residual_reference (f : V ↪ W) (F : Finset (Sym2 W))
    (d : Sym2 W → ℝ) (c : Sym2 V → ℝ) (hsep : ∀ e : Sym2 V, Sym2.map f e ∉ F)
    (B : Finset (Sym2 V)) (H : Finset (Sym2 W)) (hH : H ⊆ F) :
    residualCost (mixedSubdivisionCost f F d c) (B.image (Sym2.map f)) H = edgeCost d H := by
  have hd : Disjoint H (B.image (Sym2.map f)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hb
    obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hb
    exact hsep e (heq.symm ▸ hH hx)
  rw [residualCost, hd.sdiff_eq_left]
  exact mixedSubdivisionCost_reference_cost f F d c H hH

theorem mixedSubdivision_residual_split (f : V ↪ W) (F : Finset (Sym2 W))
    (d : Sym2 W → ℝ) (c : Sym2 V → ℝ) (hsep : ∀ e : Sym2 V, Sym2.map f e ∉ F)
    (B K : Finset (Sym2 V)) (H : Finset (Sym2 W)) (hH : H ⊆ F) :
    residualCost (mixedSubdivisionCost f F d c) (B.image (Sym2.map f))
      (H ∪ K.image (Sym2.map f)) = edgeCost d H + residualCost c B K := by
  have hd : Disjoint H (K.image (Sym2.map f)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hb
    obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hb
    exact hsep e (heq.symm ▸ hH hx)
  rw [residualCost_union_eq _ _ _ _ hd, mixedSubdivision_residual_reference f F d c hsep B H hH,
    mixedSubdivision_residual_original f F d c hsep B K]

end OnlineSteinerForest.UpperBound
