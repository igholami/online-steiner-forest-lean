import OnlineSteinerForest.UpperBound.ZonesHubForest

/-! Required hub vertices and original marks give the manuscript's attachment count. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical BigOperators

variable {V C : Type*} [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C]

/-- All marks can be required, including those inside zones: their spoke
incidences automatically account for their attachment paths. -/
theorem exists_marked_hub_subgraph (G : SimpleGraph (V ⊕ C)) (marks : Finset V) :
    ∃ H : SimpleGraph (V ⊕ C), H ≤ G ∧
      (∀ u ∈ marks, ∀ v ∈ marks, G.Reachable (.inl u) (.inl v) →
        H.Reachable (.inl u) (.inl v)) ∧
      (∑ q : C, H.degree (.inr q)) ≤ 2 * (Fintype.card C + marks.card) := by
  let hubs : Finset (V ⊕ C) := Finset.univ.image Sum.inr
  let required := hubs ∪ marks.image Sum.inl
  obtain ⟨H, hHG, hreach, hbound⟩ := exists_terminal_spanning_subgraph G required
  have hcard : required.card ≤ Fintype.card C + marks.card := by
    calc
      required.card ≤ hubs.card + (marks.image Sum.inl).card := Finset.card_union_le _ _
      _ ≤ Fintype.card C + marks.card := by
        apply add_le_add
        · exact (Finset.card_image_le).trans_eq Finset.card_univ
        · exact Finset.card_image_le
  have hsum : (∑ q : C, H.degree (.inr q)) = ∑ v ∈ hubs, H.degree v := by
    change (∑ q : C, H.degree (.inr q)) =
      ∑ v ∈ (Finset.univ : Finset C).image Sum.inr, H.degree v
    symm
    exact Finset.sum_image (by intro a _ b _ h; exact Sum.inr_injective h)
  refine ⟨H, hHG, ?_, ?_⟩
  · intro u hu v hv huv
    exact hreach (.inl u) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hu))
      (.inl v) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hv)) huv
  · rw [hsum]
    exact (Finset.sum_le_sum_of_subset (f := fun v => H.degree v)
      Finset.subset_union_left).trans (hbound.trans (Nat.mul_le_mul_left _ hcard))

end OnlineSteinerForest.UpperBound
