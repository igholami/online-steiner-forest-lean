import OnlineSteinerForest.UpperBound.ZonesHubSubgraph
import OnlineSteinerForest.UpperBound.ZonesComponentCounts

/-! A terminal-spanning subgraph in one ordinary connected component of the hub graph. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_component_terminal_subgraph (G : SimpleGraph V) (terminals : Finset V)
    (C : G.ConnectedComponent) (hC : C ∈ terminals.image G.connectedComponentMk) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.support ⊆ C.supp ∧
      (∀ u ∈ terminals, ∀ v ∈ terminals, u ∈ C.supp → v ∈ C.supp → H.Reachable u v) ∧
      (∑ v ∈ terminals, H.degree v) ≤ 2 * (componentTerminals G terminals C).card := by
  obtain ⟨t, ht, htc⟩ := Finset.mem_image.mp hC
  have hne : (componentTerminals G terminals C).Nonempty := by
    exact ⟨⟨t, (C.mem_supp_iff t).mpr htc⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩⟩
  obtain ⟨T, hTG, hreach, hbound⟩ := exists_terminal_subgraph C.toSimpleGraph
    C.connected_toSimpleGraph (componentTerminals G terminals C) hne
  let e : C ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  let H := T.map e
  have hsupp : H.support ⊆ C.supp := by
    intro v hv
    obtain ⟨w, _, rfl⟩ := (show v ∈ e '' T.support by
      simpa only [H, SimpleGraph.support_map] using hv)
    exact w.property
  have hzero (v : V) (hv : v ∉ C.supp) : H.degree v = 0 :=
    (SimpleGraph.degree_eq_zero_iff_notMem_support H v).mpr (fun h => hv (hsupp h))
  have hsum : (∑ w ∈ componentTerminals G terminals C, T.degree w) =
      ∑ v ∈ terminals.filter (fun v => v ∈ C.supp), H.degree v := by
    apply Finset.sum_bij (fun w _ => w.val)
    · intro w hw
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).2, w.property⟩
    · intro a _ b _ hab
      exact Subtype.ext hab
    · intro v hv
      obtain ⟨hvT, hvC⟩ := Finset.mem_filter.mp hv
      exact ⟨⟨v, hvC⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvT⟩, rfl⟩
    · intro w _
      exact (T.degree_map_apply e w).symm
  have hfull : (∑ v ∈ terminals.filter (fun v => v ∈ C.supp), H.degree v) =
      ∑ v ∈ terminals, H.degree v := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro v hv hnot
    apply hzero v
    intro hvC
    exact hnot (Finset.mem_filter.mpr ⟨hv, hvC⟩)
  refine ⟨H, ?_, hsupp, ?_, ?_⟩
  · intro u v huv
    obtain ⟨_, a, b, hab, rfl, rfl⟩ := (SimpleGraph.map_adj' e T u v).mp huv
    exact hTG hab
  · intro u hu v hv huC hvC
    exact (hreach ⟨u, huC⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩)
      ⟨v, hvC⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩)).map
        (SimpleGraph.Embedding.map e T).toHom
  · simp only [← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] at hsum hfull hbound ⊢
    rw [← hfull, ← hsum]
    omega

end OnlineSteinerForest.UpperBound
