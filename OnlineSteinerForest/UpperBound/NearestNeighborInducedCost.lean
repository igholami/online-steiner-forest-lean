import OnlineSteinerForest.Graph.Cost
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic.Linarith

/-! Removing a vertex leaves enough cost budget to pay for a leaf excursion. -/
namespace OnlineSteinerForest.UpperBound

open scoped Classical

/-- Canonical finite edge cost, independent of data-valued `Fintype` instances. -/
noncomputable def graphCost {W : Type*} [Finite W] (H : SimpleGraph W) (d : Sym2 W → ℝ) : ℝ :=
  edgeCost d H.edgeSet.toFinite.toFinset

theorem graphCost_eq_edgeFinset {W : Type*} [Finite W] (H : SimpleGraph W)
    [Fintype H.edgeSet] (d : Sym2 W → ℝ) : graphCost H d = edgeCost d H.edgeFinset := by
  unfold graphCost
  congr 1
  ext e
  simp

theorem graphCost_nonneg {W : Type*} [Finite W] (H : SimpleGraph W) (d : Sym2 W → ℝ)
    (hd : ∀ e ∈ H.edgeSet, 0 ≤ d e) : 0 ≤ graphCost H d := by
  apply Finset.sum_nonneg
  intro e he
  exact hd e (by simpa using he)

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Induced-edge inclusion preserves the original edge costs. -/
theorem induced_cost_add_edge_le (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (S : Set V) (u v : V)
    (hv : v ∉ S) (huv : G.Adj u v) :
    graphCost (G.induce S) (fun e : Sym2 ↥S => c (Sym2.map Subtype.val e)) + c s(u, v) ≤
      graphCost G c := by
  classical
  rw [graphCost_eq_edgeFinset, graphCost_eq_edgeFinset]
  let f : Sym2 ↥S → Sym2 V := Sym2.map Subtype.val
  let E := (G.induce S).edgeFinset.image f
  have hinj : Function.Injective f := Sym2.map.injective Subtype.val_injective
  have hin (e : Sym2 ↥S) : e ∈ (G.induce S).edgeFinset → f e ∈ G.edgeFinset := by
    refine Sym2.ind (fun a b hab => ?_) e
    change s(a.val, b.val) ∈ G.edgeFinset
    exact G.mem_edgeFinset.mpr ((G.induce S).mem_edgeFinset.mp hab)
  have hsub : E ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    exact hin a ha
  have havoid (e : Sym2 ↥S) : f e ≠ s(u, v) := by
    refine Sym2.ind (fun a b he => ?_) e
    change s(a.val, b.val) = s(u, v) at he
    rcases Sym2.eq_iff.mp he with ⟨_, hb⟩ | ⟨ha, _⟩
    · exact hv (hb ▸ b.prop)
    · exact hv (ha ▸ a.prop)
  have hne : s(u, v) ∉ E := by
    intro he
    obtain ⟨e, _, heq⟩ := Finset.mem_image.mp he
    exact havoid e heq
  have hes : s(u, v) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr huv
  have hsub' : insert s(u, v) E ⊆ G.edgeFinset := Finset.insert_subset hes hsub
  have hsum : edgeCost c E =
      edgeCost (fun e : Sym2 ↥S => c (Sym2.map Subtype.val e)) (G.induce S).edgeFinset := by
    exact Finset.sum_image (fun _ _ _ _ he => hinj he)
  have hbound := Finset.sum_le_sum_of_subset_of_nonneg hsub'
    (fun e he _ => hc e (SimpleGraph.mem_edgeFinset.mp he))
  rw [Finset.sum_insert hne] at hbound
  change c s(u, v) + edgeCost c E ≤ edgeCost c G.edgeFinset at hbound
  rw [hsum] at hbound
  linarith

/-- Restricting to an induced subgraph cannot increase nonnegative original cost. -/
theorem induced_cost_le (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (S : Set V) :
    graphCost (G.induce S) (fun e : Sym2 ↥S => c (Sym2.map Subtype.val e)) ≤ graphCost G c := by
  classical
  rw [graphCost_eq_edgeFinset, graphCost_eq_edgeFinset]
  let f : Sym2 ↥S → Sym2 V := Sym2.map Subtype.val
  let E := (G.induce S).edgeFinset.image f
  have hinj : Function.Injective f := Sym2.map.injective Subtype.val_injective
  have hsub : E ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    refine Sym2.ind (fun u v huv => ?_) a ha
    exact G.mem_edgeFinset.mpr ((G.induce S).mem_edgeFinset.mp huv)
  have hsum : edgeCost c E =
      edgeCost (fun e : Sym2 ↥S => c (Sym2.map Subtype.val e)) (G.induce S).edgeFinset :=
    Finset.sum_image (fun _ _ _ _ he => hinj he)
  rw [← hsum]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun e he _ => hc e (G.mem_edgeFinset.mp he))

end OnlineSteinerForest.UpperBound
