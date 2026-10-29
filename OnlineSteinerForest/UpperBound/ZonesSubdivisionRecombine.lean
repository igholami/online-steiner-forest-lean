import OnlineSteinerForest.UpperBound.ZonesSubdivisionIncidence

/-! Pruning partial chains preserves connectivity between original marked vertices. -/
namespace OnlineSteinerForest.UpperBound

open scoped Classical
variable {V : Type*} [DecidableEq V]

theorem zoneRecombine_reachable {E : Finset (Sym2 V)}
    {F : Finset (Sym2 (ZoneSubdivisionVertex V))} (hF : F ⊆ E.biUnion zoneSplitEdges)
    {a b : V}
    (hab : (SimpleGraph.fromEdgeSet (F : Set (Sym2 (ZoneSubdivisionVertex V)))).Reachable
      (Sum.inl a) (Sum.inl b)) :
    (SimpleGraph.fromEdgeSet (zoneRecombine E F : Set (Sym2 V))).Reachable a b := by
  let H := SimpleGraph.fromEdgeSet (zoneRecombine E F : Set (Sym2 V))
  let A : ZoneSubdivisionVertex V → Prop
    | .inl v => H.Reachable a v
    | .inr e => ∀ v : V, s(Sum.inl v, Sum.inr e) ∈ F → H.Reachable a v
  have hclosed : ∀ x y, (SimpleGraph.fromEdgeSet
      (F : Set (Sym2 (ZoneSubdivisionVertex V)))).Adj x y → A x → A y := by
    intro x y hxy hx
    cases x with
    | inl u =>
      cases y with
      | inl v => exact False.elim (not_mem_split_old E u v (hF hxy.1))
      | inr e =>
        intro v hv
        by_cases huv : u = v
        · subst v; exact hx
        · exact hx.trans (zoneRecombine_adj hF hxy.1 hv huv).reachable
    | inr e =>
      cases y with
      | inl v =>
        apply hx v
        have he : s(Sum.inr e, Sum.inl v) ∈ F := hxy.1
        simpa only [Sym2.eq_swap] using he
      | inr f => exact False.elim (not_mem_split_private E e f (hF hxy.1))
  have hprop : ∀ {x y : ZoneSubdivisionVertex V},
      (SimpleGraph.fromEdgeSet (F : Set (Sym2 (ZoneSubdivisionVertex V)))).Walk x y → A x → A y := by
    intro x y p
    induction p with
    | nil => exact id
    | cons hxy p ih => exact fun hx => ih (hclosed _ _ hxy hx)
  obtain ⟨p⟩ := hab
  exact hprop p (SimpleGraph.Reachable.refl a)

end OnlineSteinerForest.UpperBound
