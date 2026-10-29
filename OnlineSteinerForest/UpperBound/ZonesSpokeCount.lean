import OnlineSteinerForest.UpperBound.ZonesIncidences

/-! Counting the concrete original-vertex/hub pairs that require attachments. -/
namespace OnlineSteinerForest.UpperBound

open scoped Classical BigOperators

variable {V C : Type*} [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C]

noncomputable def hubSpokes (H : SimpleGraph (V ⊕ C)) : Finset (V × C) :=
  Finset.univ.filter fun p => H.Adj (.inl p.1) (.inr p.2)

theorem hubSpokes_card_le (H : SimpleGraph (V ⊕ C)) :
    (hubSpokes H).card ≤ ∑ q : C, H.degree (.inr q) := by
  let hubs : Finset (V ⊕ C) := Finset.univ.image Sum.inr
  let f : V × C → Sym2 (V ⊕ C) := fun p => s(Sum.inl p.1, Sum.inr p.2)
  have hf : Function.Injective f := by
    intro p q hpq
    have hpq' : p.1 = q.1 ∧ p.2 = q.2 := by
      simpa only [f, Sym2.eq_iff, Sum.inl.injEq, Sum.inr.injEq,
        Sum.inl_ne_inr, Sum.inr_ne_inl, and_false, or_false] using hpq
    exact Prod.ext hpq'.1 hpq'.2
  have hsub : (hubSpokes H).image f ⊆ hubs.biUnion (fun v => H.incidenceFinset v) := by
    intro e he
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    have hadj := (Finset.mem_filter.mp hp).2
    apply Finset.mem_biUnion.mpr
    refine ⟨Sum.inr p.2, Finset.mem_image.mpr ⟨p.2, Finset.mem_univ _, rfl⟩, ?_⟩
    rw [SimpleGraph.incidenceFinset_eq_filter]
    exact Finset.mem_filter.mpr ⟨SimpleGraph.mem_edgeFinset.mpr hadj, by simp [f]⟩
  calc
    (hubSpokes H).card = ((hubSpokes H).image f).card :=
      (Finset.card_image_of_injective _ hf).symm
    _ ≤ (hubs.biUnion (fun v => H.incidenceFinset v)).card := Finset.card_le_card hsub
    _ ≤ ∑ v ∈ hubs, H.degree v := hub_incident_edge_count H hubs
    _ = ∑ q : C, H.degree (.inr q) := by
      exact Finset.sum_image (by intro a _ b _ h; exact Sum.inr_injective h)

end OnlineSteinerForest.UpperBound
