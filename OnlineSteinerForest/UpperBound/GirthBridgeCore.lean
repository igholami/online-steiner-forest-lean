import OnlineSteinerForest.UpperBound.GirthCycleCost

/-! Removing all bridges preserves every cycle, and leaves no bridges. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V : Type*}

noncomputable def bridgeCore (G : SimpleGraph V) : SimpleGraph V :=
  G.deleteEdges {e | G.IsBridge e}

theorem bridgeCore_le (G : SimpleGraph V) : bridgeCore G ≤ G := SimpleGraph.deleteEdges_le _

theorem cycle_edges_mem_bridgeCore {G : SimpleGraph V} {v : V} (p : G.Walk v v)
    (hp : p.IsCycle) : ∀ e ∈ p.edges, e ∈ (bridgeCore G).edgeSet := by
  intro e he
  have hG := p.edges_subset_edgeSet he
  have hn : ¬ G.IsBridge e := fun hb => hb.notMem_edges_of_isCycle hp he
  simpa [bridgeCore, SimpleGraph.edgeSet_deleteEdges] using (show e ∈ G.edgeSet \ {e | G.IsBridge e} from ⟨hG, hn⟩)

theorem bridgeCore_no_bridges (G : SimpleGraph V) (e : Sym2 V)
    (hmem : e ∈ (bridgeCore G).edgeSet) :
    ¬ (bridgeCore G).IsBridge e := by
  intro hb
  have hG : e ∈ G.edgeSet := SimpleGraph.edgeSet_mono (bridgeCore_le G) hmem
  have hn : ¬ G.IsBridge e := by
    have hh : e ∈ G.edgeSet \ {e | G.IsBridge e} := by
      simpa [bridgeCore, SimpleGraph.edgeSet_deleteEdges] using hmem
    exact hh.2
  have hw : ∃ v, ∃ p : G.Walk v v, p.IsCycle ∧ e ∈ p.edges := by
    by_contra! h
    exact hn ((G.isBridge_iff_forall_cycle_notMem hG).mpr (by intro v p hp he; exact h v p hp he))
  obtain ⟨v, p, hp, he⟩ := hw
  let q := p.transfer (bridgeCore G) (cycle_edges_mem_bridgeCore p hp)
  have hq : q.IsCycle := hp.transfer _
  exact hb.notMem_edges_of_isCycle hq (by simpa [q] using he)

end OnlineSteinerForest.UpperBound.Girth
