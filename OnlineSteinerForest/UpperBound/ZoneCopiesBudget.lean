import OnlineSteinerForest.UpperBound.ZoneCopiesEdges
import OnlineSteinerForest.UpperBound.ZoneCopiesCost
import OnlineSteinerForest.UpperBound.ZonesAttachments

/-! The total copied reference cost is bounded by the sum of the original zone budgets. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {Z W : Type*} [Fintype Z] [DecidableEq Z] [Fintype W] [DecidableEq W]

def zoneCopyProjection (zones : Z → Finset (Sym2 W)) : (Σ z, ZoneSupportVertex (zones z)) → W :=
  fun x => x.2.val

theorem zoneCopies_budget (zones : Z → Finset (Sym2 W))
    (T : ∀ z, SimpleGraph (ZoneSupportVertex (zones z))) (hT : ∀ z, T z ≤ zoneSupportGraph (zones z))
    (c : Sym2 W → ℝ) (hc : ∀ z, ∀ e ∈ zones z, 0 ≤ c e) (B : ℝ)
    (hbudget : ∀ z, edgeCost c (zones z) ≤ B) :
    edgeCost (fun e => c (Sym2.map (zoneCopyProjection zones) e)) (zoneCopyGraph T).edgeFinset ≤
      (Fintype.card Z : ℝ) * B := by
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
  have hbudget' : ∀ z ∈ (Finset.univ : Finset Z), edgeCost d (zoneCopiedEdges T z) ≤ B := by
    intro z hz
    rw [hcost]
    exact (zone_copy_tree_cost (zones z) (T z) (hT z) c (hc z)).trans (hbudget z)
  rw [zoneCopyGraph_edges]
  simpa only [Finset.card_univ] using attachment_union_budget d Finset.univ (zoneCopiedEdges T) B
    (fun z _ => hnonneg z) hbudget'

end OnlineSteinerForest.UpperBound
