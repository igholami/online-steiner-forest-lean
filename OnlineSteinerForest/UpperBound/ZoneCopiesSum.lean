import OnlineSteinerForest.UpperBound.ZoneCopiesBudget
import OnlineSteinerForest.UpperBound.ZoneCopiesCost
import OnlineSteinerForest.UpperBound.ZonesAttachments

/-! The total copied reference cost is bounded by the sum of all individual original zone costs. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {Z W : Type*} [Fintype Z] [DecidableEq Z] [Fintype W] [DecidableEq W]

theorem zoneCopies_cost_le_sum (zones : Z → Finset (Sym2 W))
    (T : ∀ z, SimpleGraph (ZoneSupportVertex (zones z))) (hT : ∀ z, T z ≤ zoneSupportGraph (zones z))
    (c : Sym2 W → ℝ) (hc : ∀ z, ∀ e ∈ zones z, 0 ≤ c e) :
    edgeCost (fun e => c (Sym2.map (zoneCopyProjection zones) e)) (zoneCopyGraph T).edgeFinset ≤
      ∑ z : Z, edgeCost c (zones z) := by
  let d : Sym2 (Σ z, ZoneSupportVertex (zones z)) → ℝ := fun e => c (Sym2.map (zoneCopyProjection zones) e)
  have hcost (z : Z) : edgeCost d (zoneCopiedEdges T z) =
      edgeCost (fun e => c (Sym2.map Subtype.val e)) (T z).edgeFinset := by
    rw [edgeCost, zoneCopiedEdges, Finset.sum_image
      (fun _ _ _ _ h => Sym2.map.injective (by intro a b h; cases h; rfl) h)]
    apply Finset.sum_congr rfl
    intro e he
    simp [d, Sym2.map_map, zoneCopyProjection, Function.comp_def]
  have hnonneg (z : Z) : ∀ e ∈ zoneCopiedEdges T z, 0 ≤ d e := by
    intro e he
    obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp he
    rw [← hfe]
    have hsub : Sym2.map Subtype.val f ∈ zones z := by
      have hmap : ∀ f : Sym2 (ZoneSupportVertex (zones z)), f ∈ (T z).edgeSet →
          Sym2.map Subtype.val f ∈ zones z := by
        intro f
        refine Sym2.ind (fun u v huv => ?_) f
        exact (hT z huv).1
      exact hmap f ((T z).mem_edgeFinset.mp hf)
    simpa only [d, Sym2.map_map, Function.comp_def, zoneCopyProjection] using hc z _ hsub
  rw [zoneCopyGraph_edges]
  calc
    _ ≤ ∑ z : Z, edgeCost d (zoneCopiedEdges T z) :=
      attachment_union_cost_le d Finset.univ (zoneCopiedEdges T) (fun z _ => hnonneg z)
    _ ≤ _ := Finset.sum_le_sum (fun z _ => by
      rw [hcost]
      exact zone_copy_tree_cost (zones z) (T z) (hT z) c (hc z))

end OnlineSteinerForest.UpperBound
