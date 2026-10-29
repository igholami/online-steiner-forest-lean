import OnlineSteinerForest.UpperBound.ZonesPartitionBoundary
import OnlineSteinerForest.UpperBound.AuxiliaryHelpful
import OnlineSteinerForest.UpperBound.SparseNeighbors
import OnlineSteinerForest.UpperBound.ZonesSubdivisionMetric
import OnlineSteinerForest.UpperBound.SparseParameters

/-! Every edge of the computed zone-neighbor core is realized by an actual short greedy auxiliary path. -/
namespace OnlineSteinerForest.UpperBound

universe uSelection
variable [OnlineSteinerForest.PathSelection.{uSelection}]

open scoped Classical
variable {V W Z : Type uSelection} {I : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype I] [DecidableEq I] [DecidableEq Z]

theorem helpful_core_realization (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (f : V ↪ W) (F : Finset (Sym2 W)) (d : Sym2 W → ℝ)
    (hsep : ∀ e : Sym2 V, Sym2.map f e ∉ F)
    (zones : Z → Finset (Sym2 W)) (left right : I → Z) (S : Finset Z)
    (time : I → Fin requests.length) (out : I → AuxiliaryOutput V) (scale : ℝ)
    (helpful : ∀ i, HelpfulAt G c requests feasible (time i) scale (out i))
    (hl : ∀ i, zoneSupport (zones (left i)) (f (out i).left))
    (hr : ∀ i, zoneSupport (zones (right i)) (f (out i).right)) :
    ∀ u v, (zoneNeighborGraph left right S).Adj u v →
      ∃ a b : W, ∃ P : Finset (Sym2 W),
        zoneSupport (zones u.val) a ∧ zoneSupport (zones v.val) b ∧
        IsPathEdges (mixedSubdivisionGraph G f F) a b P ∧
        edgeCost (mixedSubdivisionCost f F d c) P ≤
          (zoneMultiplier (cycleFactor requests.length) : ℝ) * scale / 256 := by
  intro u v huv
  obtain ⟨i, _, hpair⟩ := huv
  have hp := IsPathEdges.mixed (helpful i).path f F
  have hcost : edgeCost (mixedSubdivisionCost f F d c)
      ((out i).edges.image (Sym2.map f)) = edgeCost c (out i).edges := by
    rw [edgeCost, Finset.sum_image (fun _ _ _ _ h => Sym2.map.injective f.injective h)]
    exact Finset.sum_congr rfl (fun _ _ => mixedSubdivisionCost_original f F d c hsep _)
  have hb : edgeCost (mixedSubdivisionCost f F d c)
      ((out i).edges.image (Sym2.map f)) ≤
        (zoneMultiplier (cycleFactor requests.length) : ℝ) * scale / 256 := by
    rw [hcost]
    convert (helpful i).short using 1 <;> push_cast [zoneMultiplier] <;> ring
  rcases hpair with ⟨hli, hri⟩ | ⟨hli, hri⟩
  · exact ⟨f (out i).left, f (out i).right, _, hli ▸ hl i, hri ▸ hr i, hp, hb⟩
  · exact ⟨f (out i).right, f (out i).left, _, hri ▸ hr i, hli ▸ hl i, hp.reverse, hb⟩

end OnlineSteinerForest.UpperBound
