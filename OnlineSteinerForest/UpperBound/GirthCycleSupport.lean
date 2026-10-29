import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! Extracting a standard mathlib cycle from colliding nonbacktracking walks. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V : Type*} {G : SimpleGraph V}

/-- Distinct walks without immediate backtracking force a cycle inside their combined support. -/
theorem cycle_in_two_walks {u v : V} (p q : G.Walk u v) (hne : p ≠ q)
    (hp : List.IsChain (· ≠ ·) p.edges) (hq : List.IsChain (· ≠ ·) q.edges) :
    ∃ z, ∃ c : G.Walk z z, c.IsCycle ∧ ∀ e ∈ c.edges, e ∈ p.edges ∨ e ∈ q.edges := by
  classical
  let H := SimpleGraph.fromEdgeSet (p.edgeSet ∪ q.edgeSet)
  have hHG : H ≤ G := by
    apply (SimpleGraph.fromEdgeSet_le G).mpr
    intro e he
    rcases he.1 with he | he
    · exact p.edges_subset_edgeSet he
    · exact q.edges_subset_edgeSet he
  have hpH : ∀ e ∈ p.edges, e ∈ H.edgeSet := by
    intro e he
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    exact ⟨Or.inl he, G.not_isDiag_of_mem_edgeSet (p.edges_subset_edgeSet he)⟩
  have hqH : ∀ e ∈ q.edges, e ∈ H.edgeSet := by
    intro e he
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    exact ⟨Or.inr he, G.not_isDiag_of_mem_edgeSet (q.edges_subset_edgeSet he)⟩
  have hnacyclic : ¬ H.IsAcyclic := by
    intro ha
    have hp' := (ha.isPath_iff_isChain (p.transfer H hpH)).mpr (by simpa using hp)
    have hq' := (ha.isPath_iff_isChain (q.transfer H hqH)).mpr (by simpa using hq)
    have heq : p.transfer H hpH = q.transfer H hqH :=
      congrArg Subtype.val ((ha.subsingleton_path u v).elim ⟨_, hp'⟩ ⟨_, hq'⟩)
    apply hne
    apply SimpleGraph.Walk.ext_support
    simpa using congrArg SimpleGraph.Walk.support heq
  unfold SimpleGraph.IsAcyclic at hnacyclic
  push_neg at hnacyclic
  obtain ⟨z, c, hc⟩ := hnacyclic
  refine ⟨z, c.mapLe hHG, hc.mapLe hHG, ?_⟩
  intro e he
  have hmem : e ∈ H.edgeSet := c.edges_subset_edgeSet (by simpa using he)
  rw [SimpleGraph.edgeSet_fromEdgeSet] at hmem
  exact hmem.1

end OnlineSteinerForest.UpperBound.Girth
