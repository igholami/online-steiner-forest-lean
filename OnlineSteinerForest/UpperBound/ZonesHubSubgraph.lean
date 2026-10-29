import OnlineSteinerForest.UpperBound.ZonesHubTree

/-! Terminal-spanning trees viewed as subgraphs on the ambient hub vertex type. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical BigOperators

/-- Construct a subgraph connecting the required vertices with a controlled
number of incidences at those vertices. Unused ambient vertices are isolated. -/
theorem exists_terminal_subgraph {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.Connected) (terminals : Finset V)
    (hne : terminals.Nonempty) :
    ∃ H : SimpleGraph V, H ≤ G ∧
      (∀ u ∈ terminals, ∀ v ∈ terminals, H.Reachable u v) ∧
      (∑ v ∈ terminals, H.degree v) + 2 ≤ 2 * terminals.card := by
  obtain ⟨S, T, hTS, hTG, hT, hbound⟩ := exists_terminal_subtree G hG terminals hne
  let e : (S : Set V) ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  let H := T.map e
  have hHG : H ≤ G := by
    intro u v huv
    obtain ⟨_, a, b, hab, rfl, rfl⟩ := (SimpleGraph.map_adj' e T u v).mp huv
    exact hTG hab
  have hsum : (∑ w ∈ Finset.univ.filter (fun w : (S : Set V) => w.val ∈ terminals),
      T.degree w) = ∑ v ∈ terminals, H.degree v := by
    apply Finset.sum_bij (fun w _ => w.val)
    · intro w hw
      exact (Finset.mem_filter.mp hw).2
    · intro a _ b _ hab
      exact Subtype.ext hab
    · intro v hv
      exact ⟨⟨v, hTS hv⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩
    · intro w _
      exact (T.degree_map_apply e w).symm
  refine ⟨H, hHG, ?_, ?_⟩
  · intro u hu v hv
    exact (hT.connected ⟨u, hTS hu⟩ ⟨v, hTS hv⟩).map
      (SimpleGraph.Embedding.map e T).toHom
  · simp only [← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] at hsum hbound ⊢
    rw [← hsum]
    exact hbound

end OnlineSteinerForest.UpperBound
