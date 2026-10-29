import OnlineSteinerForest.Graph.Feasibility

/-! A concrete boundary-hub graph with one hub for each assigned core component. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

variable {V I C : Type*}

/-- Outside edges keep their endpoints. Each vertex of a core zone is joined
to its component hub. Interior spokes will disappear when unrequired leaves
are pruned; retaining them makes the original-connection map explicit. -/
def boundaryHubGraph (outside : Set (Sym2 V)) (zoneVertices : I → Set V)
    (component : I → C) : SimpleGraph (V ⊕ C) :=
  SimpleGraph.fromEdgeSet {e |
    (∃ u v : V, s(u, v) ∈ outside ∧ e = s(Sum.inl u, Sum.inl v)) ∨
    ∃ (i : I) (v : V), v ∈ zoneVertices i ∧ e = s(Sum.inl v, Sum.inr (component i))}

theorem hub_outside_adj (outside : Set (Sym2 V)) (zoneVertices : I → Set V)
    (component : I → C) {u v : V} (h : s(u, v) ∈ outside) (hne : u ≠ v) :
    (boundaryHubGraph outside zoneVertices component).Adj (.inl u) (.inl v) := by
  exact ⟨Or.inl ⟨u, v, h, rfl⟩, by simpa using hne⟩

theorem hub_spoke_adj (outside : Set (Sym2 V)) (zoneVertices : I → Set V)
    (component : I → C) (i : I) {v : V} (hv : v ∈ zoneVertices i) :
    (boundaryHubGraph outside zoneVertices component).Adj (.inl v) (.inr (component i)) := by
  exact ⟨Or.inr ⟨i, v, hv, rfl⟩, by simp⟩

/-- Each spoke records a concrete incident zone in the indicated component. -/
theorem hub_spoke_iff (outside : Set (Sym2 V)) (zoneVertices : I → Set V)
    (component : I → C) (v : V) (c : C) :
    (boundaryHubGraph outside zoneVertices component).Adj (.inl v) (.inr c) ↔
      ∃ i, v ∈ zoneVertices i ∧ component i = c := by
  constructor
  · intro h
    rcases h.1 with ⟨u, w, _, heq⟩ | ⟨i, w, hw, heq⟩
    · rcases Sym2.eq_iff.mp heq with h | h <;> simp_all
    · simp only [Sym2.eq_iff, Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr,
        Sum.inr_ne_inl, and_false, false_and, or_false] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact ⟨i, hw, rfl⟩
  · rintro ⟨i, hv, rfl⟩
    exact hub_spoke_adj outside zoneVertices component i hv

/-- Every removed zone edge is reconnected through its assigned hub. -/
theorem hub_zone_reachable (outside : Set (Sym2 V)) (zoneVertices : I → Set V)
    (component : I → C) (i : I) {u v : V}
    (hu : u ∈ zoneVertices i) (hv : v ∈ zoneVertices i) :
    (boundaryHubGraph outside zoneVertices component).Reachable (.inl u) (.inl v) :=
  (hub_spoke_adj outside zoneVertices component i hu).reachable.trans
    (hub_spoke_adj outside zoneVertices component i hv).symm.reachable

/-- Replacing core zones by hubs preserves every original connection. -/
theorem boundaryHub_preserves_reachable (F : SimpleGraph V)
    (outside : Set (Sym2 V)) (zoneVertices : I → Set V) (component : I → C)
    (hcover : ∀ u v, F.Adj u v → s(u, v) ∈ outside ∨
      ∃ i, u ∈ zoneVertices i ∧ v ∈ zoneVertices i)
    {u v : V} (h : F.Reachable u v) :
    (boundaryHubGraph outside zoneVertices component).Reachable (.inl u) (.inl v) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact .refl _
  | @cons u v z huv p ih =>
    apply SimpleGraph.Reachable.trans _ ih
    rcases hcover u v huv with hout | ⟨i, hui, hvi⟩
    · exact (hub_outside_adj outside zoneVertices component hout huv.ne).reachable
    · exact hub_zone_reachable outside zoneVertices component i hui hvi

end OnlineSteinerForest.UpperBound
