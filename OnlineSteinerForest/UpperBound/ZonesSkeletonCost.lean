import OnlineSteinerForest.UpperBound.ZonesSkeletonData
import OnlineSteinerForest.UpperBound.ZonesAttachments
import Mathlib.Tactic.Linarith

/-! The selected realizing paths and at most three center counts of zones form a cheap skeleton. -/
namespace OnlineSteinerForest.UpperBound.ZoneSkeletonData

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
  {G : SimpleGraph V} {centers : Finset V} {stars : StarContraction G centers}
  {f : InterstarForest stars} {ambient : SimpleGraph W} {zones : V → Finset (Sym2 W)}

theorem cost_le (d : ZoneSkeletonData f ambient zones) (c : Sym2 W → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hc : ∀ e ∈ ambient.edgeSet, 0 ≤ c e)
    (hinput : ∀ v, ∀ e ∈ zones v, e ∈ ambient.edgeSet)
    (hzone : ∀ v, edgeCost c (zones v) ≤ 3 * M)
    (hpath : ∀ i, edgeCost c (d.paths i) ≤ M / 256)
    (hcenters : (centers.card : ℝ) ≤ (Fintype.card V : ℝ) / 512) :
    edgeCost c d.edges ≤ (11 / 512 : ℝ) * M * Fintype.card V := by
  let full := f.retainedZones.biUnion zones
  let paths := Finset.univ.biUnion d.paths
  have hfull : edgeCost c full ≤ (f.retainedZones.card : ℝ) * (3 * M) :=
    attachment_union_budget c f.retainedZones zones (3 * M)
      (fun v _ e he => hc e (hinput v e he)) (fun v _ => hzone v)
  have hpaths : edgeCost c paths ≤ (Fintype.card f.Link : ℝ) * (M / 256) := by
    simpa only [Finset.card_univ] using attachment_union_budget c Finset.univ d.paths (M / 256)
      (fun i _ e he => hc e ((d.path i).subset_edgeSet e he)) (fun i _ => hpath i)
  have hsum : edgeCost c d.edges ≤ edgeCost c full + edgeCost c paths := by
    change edgeCost c (full ∪ paths) ≤ _
    rw [edgeCost_union]
    apply add_le_add le_rfl
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun e he _ => by
      obtain ⟨i, _, hei⟩ := Finset.mem_biUnion.mp he
      exact hc e ((d.path i).subset_edgeSet e hei))
  have hret : (f.retainedZones.card : ℝ) ≤ 3 * (centers.card : ℝ) := by
    exact_mod_cast f.retained_count_le
  have hlinks : (Fintype.card f.Link : ℝ) ≤ Fintype.card V := by exact_mod_cast f.link_count_le
  have hret' := mul_le_mul_of_nonneg_right hret (show 0 ≤ 3 * M by positivity)
  have hlinks' := mul_le_mul_of_nonneg_right hlinks (show 0 ≤ M / 256 by positivity)
  have hcenters' := mul_le_mul_of_nonneg_left hcenters (show 0 ≤ 9 * M by positivity)
  nlinarith

end OnlineSteinerForest.UpperBound.ZoneSkeletonData
