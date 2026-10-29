import OnlineSteinerForest.UpperBound.GirthCycleSupport

/-! Every cycle over a reference forest has a latest labelled auxiliary edge. -/
namespace OnlineSteinerForest.UpperBound

variable {V : Type*} {G : SimpleGraph V}

theorem cycle_has_auxiliary {z : V} (c : G.Walk z z) (hc : c.IsCycle)
    (label : Sym2 V → Option ℕ)
    (href : (G.deleteEdges {e | label e ≠ none}).IsAcyclic) :
    ∃ e ∈ c.edges, ∃ i, label e = some i := by
  classical
  by_contra! hn
  have hnone : ∀ e ∈ c.edges, label e = none := by
    intro e he
    cases hl : label e with
    | none => rfl
    | some i => exact (hn e he i hl).elim
  have hmem : ∀ e ∈ c.edges, e ∈ (G.deleteEdges {e | label e ≠ none}).edgeSet := by
    intro e he
    rw [SimpleGraph.edgeSet_deleteEdges]
    exact ⟨c.edges_subset_edgeSet he, by simpa [hnone e he]⟩
  exact href (c.transfer _ hmem) (hc.transfer _)

theorem exists_latest_cycle_edge {z : V} (c : G.Walk z z) (hc : c.IsCycle)
    (label : Sym2 V → Option ℕ)
    (href : (G.deleteEdges {e | label e ≠ none}).IsAcyclic) :
    ∃ u v i, G.Adj u v ∧ s(u, v) ∈ c.edges ∧ label s(u, v) = some i ∧
      ∀ e ∈ c.edges, ∀ j, label e = some j → j ≤ i := by
  classical
  let T := (c.edges.filterMap label).toFinset
  obtain ⟨e, he, i, hi⟩ := cycle_has_auxiliary c hc label href
  have hT : T.Nonempty := ⟨i, List.mem_toFinset.mpr (List.mem_filterMap.mpr ⟨e, he, hi⟩)⟩
  have hmax := T.max'_mem hT
  obtain ⟨e, he, hl⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp hmax)
  induction e using Sym2.inductionOn with
  | _ u v =>
    refine ⟨u, v, T.max' hT, c.adj_of_mem_edges he, he, hl, ?_⟩
    intro e he j hj
    exact Finset.le_max' T j (List.mem_toFinset.mpr (List.mem_filterMap.mpr ⟨e, he, hj⟩))

end OnlineSteinerForest.UpperBound
