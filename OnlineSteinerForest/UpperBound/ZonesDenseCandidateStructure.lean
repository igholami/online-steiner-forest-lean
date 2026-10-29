import OnlineSteinerForest.UpperBound.ZonesCost
import OnlineSteinerForest.UpperBound.ZonesPartitionBoundary

/-! Literal removed core edges and kept original edges supply exact replacement accounting. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]

noncomputable def zoneCoreEdges (zones : V → Finset (Sym2 W)) : Finset (Sym2 W) :=
  Finset.univ.biUnion zones

theorem zoneCoreEdges_subset (zones : V → Finset (Sym2 W)) (old : Finset (Sym2 W))
    (hsub : ∀ v, zones v ⊆ old) : zoneCoreEdges zones ⊆ old := by
  intro e he
  obtain ⟨v, hv, he⟩ := Finset.mem_biUnion.mp he
  exact hsub v he

theorem zoneCoreEdges_cost_lower (zones : V → Finset (Sym2 W)) (c : Sym2 W → ℝ) (M : ℝ)
    (hdis : (↑(Finset.univ : Finset V) : Set V).PairwiseDisjoint zones) (hlower : ∀ v, M ≤ edgeCost c (zones v)) :
    M * Fintype.card V ≤ edgeCost c (zoneCoreEdges zones) := by
  calc
    _ = ∑ _v : V, M := by simp [mul_comm]
    _ ≤ ∑ v : V, edgeCost c (zones v) := Finset.sum_le_sum (fun v _ => hlower v)
    _ = _ := zone_cost_sum c Finset.univ zones hdis

theorem kept_add_core_cost (zones : V → Finset (Sym2 W)) (old : Finset (Sym2 W))
    (c : Sym2 W → ℝ) (hsub : ∀ v, zones v ⊆ old) :
    edgeCost c (old \ zoneCoreEdges zones) + edgeCost c (zoneCoreEdges zones) = edgeCost c old :=
  Finset.sum_sdiff (zoneCoreEdges_subset zones old hsub)

theorem old_covered_by_kept_zones (zones : V → Finset (Sym2 W)) (old : Finset (Sym2 W)) :
    ∀ u v, (SimpleGraph.fromEdgeSet (old : Set (Sym2 W))).Adj u v →
      s(u, v) ∈ old \ zoneCoreEdges zones ∨ ∃ i, zoneSupport (zones i) u ∧ zoneSupport (zones i) v := by
  intro u v huv
  by_cases he : s(u, v) ∈ zoneCoreEdges zones
  · obtain ⟨i, hi, he⟩ := Finset.mem_biUnion.mp he
    exact Or.inr ⟨i, ⟨s(u, v), he, by simp⟩, ⟨s(u, v), he, by simp⟩⟩
  · exact Or.inl (Finset.mem_sdiff.mpr ⟨huv.1, he⟩)

theorem zone_point_of_positive_cost (zones : V → Finset (Sym2 W)) (c : Sym2 W → ℝ)
    (M : ℝ) (hM : 0 < M) (hlower : ∀ v, M ≤ edgeCost c (zones v)) :
    ∀ v, ∃ w, zoneSupport (zones v) w := by
  intro v
  have hne : (zones v).Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    have hcost := hlower v
    simp only [he, edgeCost, Finset.sum_empty] at hcost
    linarith
  obtain ⟨e, he⟩ := hne
  induction e using Sym2.inductionOn with
  | _ u w => exact ⟨u, s(u, w), he, by simp⟩

end OnlineSteinerForest.UpperBound
