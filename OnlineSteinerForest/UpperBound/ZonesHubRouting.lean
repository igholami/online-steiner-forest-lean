import OnlineSteinerForest.UpperBound.ZonesHubGraph

/-! Routing actual boundary-hub paths back through the retained skeleton and attachments. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

variable {V I C : Type*}

/-- A hub is represented by one point of the replacement skeleton. -/
def hubAnchor (root : C → V) : V ⊕ C → V
  | .inl v => v
  | .inr c => root c

/-- Edgewise reachable routes lift a whole hub walk, including repeated hubs. -/
theorem route_hub_reachable (H : SimpleGraph (V ⊕ C)) (R : SimpleGraph V)
    (root : C → V)
    (hedges : ∀ u v, H.Adj u v → R.Reachable (hubAnchor root u) (hubAnchor root v))
    {u v : V ⊕ C} (h : H.Reachable u v) :
    R.Reachable (hubAnchor root u) (hubAnchor root v) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact .refl _
  | @cons u v z huv p ih => exact (hedges u v huv).trans ih

/-- Outside edges and restored spoke connections suffice to lift every connection
of a selected boundary-hub subtree. -/
theorem boundaryHub_route (outside : Set (Sym2 V)) (zoneVertices : I → Set V)
    (component : I → C) (H : SimpleGraph (V ⊕ C))
    (hH : H ≤ boundaryHubGraph outside zoneVertices component)
    (R : SimpleGraph V) (root : C → V)
    (hout : ∀ u v, s(u, v) ∈ outside → u ≠ v → R.Reachable u v)
    (hspoke : ∀ (v : V) (c : C), H.Adj (.inl v) (.inr c) → R.Reachable v (root c))
    {u v : V} (h : H.Reachable (.inl u) (.inl v)) : R.Reachable u v := by
  apply route_hub_reachable H R root ?_ h
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      rcases (hH hab).1 with ⟨u, v, huv, heq⟩ | ⟨i, v, _, heq⟩
      · have he : s(a, b) = s(u, v) := by
          exact Sym2.map.injective Sum.inl_injective heq
        rcases Sym2.eq_iff.mp he with h | h
        · obtain ⟨rfl, rfl⟩ := h
          exact hout a b huv (by intro h; exact hab.ne (congrArg Sum.inl h))
        · obtain ⟨rfl, rfl⟩ := h
          exact (hout b a huv (by intro h; exact hab.ne (congrArg Sum.inl h.symm))).symm
      · rcases Sym2.eq_iff.mp heq with h | h <;> simp_all
    | inr b => exact hspoke a b hab
  | inr a =>
    cases b with
    | inl b => exact (hspoke b a hab.symm).symm
    | inr b =>
      rcases (hH hab).1 with ⟨u, v, _, heq⟩ | ⟨i, v, _, heq⟩
      · rcases Sym2.eq_iff.mp heq with h | h <;> simp_all
      · rcases Sym2.eq_iff.mp heq with h | h <;> simp_all

end OnlineSteinerForest.UpperBound
