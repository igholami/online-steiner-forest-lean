import OnlineSteinerForest.UpperBound.ZonesPartitionBoundary

/-! The root-leftover boundary lemma needs connectivity only on the tree support. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [DecidableEq V]

theorem exists_zone_shared_vertex_rooted (E : Finset (Sym2 V)) (r : V)
    (hroot : ZoneRooted r E) (L : Finset (Sym2 V)) (Z : List (Finset (Sym2 V)))
    (hcover : zoneUnion Z ∪ L = E) (hL : L.Nonempty) (hZ : ∃ F ∈ Z, F.Nonempty) :
    ∃ F ∈ Z, ∃ v, zoneSupport L v ∧ zoneSupport F v := by
  by_contra hn
  have hnot : ∀ F ∈ Z, ∀ v, zoneSupport L v → ¬ zoneSupport F v := by
    intro F hF v hv hFv
    exact hn ⟨F, hF, v, hv, hFv⟩
  have hclosed : ∀ u v, (SimpleGraph.fromEdgeSet (E : Set (Sym2 V))).Adj u v →
      zoneSupport L u → zoneSupport L v := by
    intro u v huv hu
    have he : s(u, v) ∈ zoneUnion Z ∪ L := hcover.symm ▸ huv.1
    rcases Finset.mem_union.mp he with hz | hl
    · obtain ⟨F, hF, heF⟩ := (mem_zoneUnion _ Z).mp hz
      exact False.elim (hnot F hF u hu ⟨s(u, v), heF, Sym2.mem_mk_left _ _⟩)
    · exact ⟨s(u, v), hl, Sym2.mem_mk_right _ _⟩
  obtain ⟨e, he⟩ := hL
  obtain ⟨u, hue⟩ : ∃ u : V, u ∈ e := Sym2.ind (fun a b => ⟨a, Sym2.mem_mk_left _ _⟩) e
  obtain ⟨F, hF, f, hf⟩ := hZ
  obtain ⟨v, hvf⟩ : ∃ v : V, v ∈ f := Sym2.ind (fun a b => ⟨a, Sym2.mem_mk_left _ _⟩) f
  have heE : e ∈ E := hcover ▸ Finset.mem_union_right _ he
  have hfE : f ∈ E := hcover ▸ Finset.mem_union_left _ ((mem_zoneUnion _ Z).mpr ⟨F, hF, hf⟩)
  have hpath := (hroot e heE u hue).symm.trans (hroot f hfE v hvf)
  obtain ⟨p⟩ := hpath
  have hv : zoneSupport L v := by
    have hprop : ∀ {a b : V}, (SimpleGraph.fromEdgeSet (E : Set (Sym2 V))).Walk a b →
        zoneSupport L a → zoneSupport L b := by
      intro a b p
      induction p with
      | nil => exact id
      | cons huv p ih => exact fun ha => ih (hclosed _ _ huv ha)
    exact hprop p ⟨e, he, hue⟩
  exact hnot F hF v hv ⟨f, hf, hvf⟩

end OnlineSteinerForest.UpperBound
