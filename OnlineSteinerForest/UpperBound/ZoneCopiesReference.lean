import OnlineSteinerForest.UpperBound.ZoneCopiesBudget
import OnlineSteinerForest.UpperBound.ZoneCopiesSum
import OnlineSteinerForest.UpperBound.ChargingCopiedMetric

/-! Copied tree edges project to real nonloop reference segments with their exact cost. -/
namespace OnlineSteinerForest.UpperBound

universe uSelection
variable [OnlineSteinerForest.PathSelection.{uSelection}]

open scoped Classical
variable {Z W : Type uSelection} [Fintype Z] [DecidableEq Z] [Fintype W] [DecidableEq W]

theorem zoneCopyGraph_project_edge (zones : Z → Finset (Sym2 W))
    (T : ∀ z, SimpleGraph (ZoneSupportVertex (zones z))) (hT : ∀ z, T z ≤ zoneSupportGraph (zones z))
    {x y : Σ z, ZoneSupportVertex (zones z)} (hxy : (zoneCopyGraph T).Adj x y) :
    zoneCopyProjection zones x ≠ zoneCopyProjection zones y ∧
      s(zoneCopyProjection zones x, zoneCopyProjection zones y) ∈ zones x.1 := by
  obtain ⟨z, u, v, huv, hx, hy⟩ := hxy
  subst x
  subst y
  have hz := hT z huv
  change (SimpleGraph.fromEdgeSet (zones z : Set (Sym2 W))).Adj u.val v.val at hz
  exact ⟨hz.ne, hz.1⟩

theorem zoneCopies_clipped_budget (zones : Z → Finset (Sym2 W))
    (T : ∀ z, SimpleGraph (ZoneSupportVertex (zones z))) (hT : ∀ z, T z ≤ zoneSupportGraph (zones z))
    (d : Sym2 W → ℝ) (hd : ∀ z, ∀ e ∈ zones z, 0 ≤ d e) (B : ℝ)
    (hbudget : ∀ z, edgeCost d (zones z) ≤ B) :
    edgeCost (copiedReferenceCost d (zoneCopyProjection zones)) (zoneCopyGraph T).edgeFinset ≤
      (Fintype.card Z : ℝ) * B := by
  have heq : edgeCost (copiedReferenceCost d (zoneCopyProjection zones)) (zoneCopyGraph T).edgeFinset =
      edgeCost (fun e => d (Sym2.map (zoneCopyProjection zones) e)) (zoneCopyGraph T).edgeFinset := by
    apply Finset.sum_congr rfl
    intro e he
    have hnonneg : 0 ≤ d (Sym2.map (zoneCopyProjection zones) e) := by
      refine Sym2.ind (fun x y he => ?_) e he
      have hxy := (zoneCopyGraph T).mem_edgeFinset.mp he
      exact hd x.1 _ (zoneCopyGraph_project_edge zones T hT hxy).2
    exact max_eq_left hnonneg
  rw [heq]
  exact zoneCopies_budget zones T hT d hd B hbudget

theorem zoneCopies_clipped_cost_le_sum (zones : Z → Finset (Sym2 W))
    (T : ∀ z, SimpleGraph (ZoneSupportVertex (zones z))) (hT : ∀ z, T z ≤ zoneSupportGraph (zones z))
    (d : Sym2 W → ℝ) (hd : ∀ z, ∀ e ∈ zones z, 0 ≤ d e) :
    edgeCost (copiedReferenceCost d (zoneCopyProjection zones)) (zoneCopyGraph T).edgeFinset ≤
      ∑ z : Z, edgeCost d (zones z) := by
  have heq : edgeCost (copiedReferenceCost d (zoneCopyProjection zones)) (zoneCopyGraph T).edgeFinset =
      edgeCost (fun e => d (Sym2.map (zoneCopyProjection zones) e)) (zoneCopyGraph T).edgeFinset := by
    apply Finset.sum_congr rfl
    intro e he
    have hnonneg : 0 ≤ d (Sym2.map (zoneCopyProjection zones) e) := by
      refine Sym2.ind (fun x y he => ?_) e he
      have hxy := (zoneCopyGraph T).mem_edgeFinset.mp he
      exact hd x.1 _ (zoneCopyGraph_project_edge zones T hT hxy).2
    exact max_eq_left hnonneg
  rw [heq]
  exact zoneCopies_cost_le_sum zones T hT d hd

end OnlineSteinerForest.UpperBound
