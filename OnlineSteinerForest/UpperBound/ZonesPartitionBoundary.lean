import OnlineSteinerForest.UpperBound.ZonesPartitionState

/-! Connected edge partitions meet across the boundary of every nonempty proper part. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [DecidableEq V] [Fintype V]

def zoneSupport (F : Finset (Sym2 V)) (v : V) : Prop := ∃ e ∈ F, v ∈ e

theorem ZoneConnected.root_at {F : Finset (Sym2 V)} (hF : ZoneConnected F)
    {v : V} (hv : zoneSupport F v) : ZoneRooted v F := by
  obtain ⟨r, hr⟩ := hF
  obtain ⟨e, he, hv⟩ := hv
  intro f hf w hw
  exact (hr e he v hv).symm.trans (hr f hf w hw)

theorem ZoneConnected.union_shared {F H : Finset (Sym2 V)}
    (hF : ZoneConnected F) (hH : ZoneConnected H) {v : V}
    (hvF : zoneSupport F v) (hvH : zoneSupport H v) : ZoneConnected (F ∪ H) :=
  ((hF.root_at hvF).union (hH.root_at hvH)).connected

private theorem closed_of_reachable {G : SimpleGraph V} (A : V → Prop)
    (hclosed : ∀ u v, G.Adj u v → A u → A v) {u v : V}
    (h : G.Reachable u v) (hu : A u) : A v := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact hu
  | cons huv p ih => exact ih (hclosed _ _ huv hu)

/-- Some output zone touches the support of any nonempty leftover. -/
theorem exists_zone_shared_vertex (G : SimpleGraph V) (hG : G.Connected)
    (L : Finset (Sym2 V)) (Z : List (Finset (Sym2 V)))
    (hcover : zoneUnion Z ∪ L = G.edgeFinset)
    (hL : L.Nonempty) (hZ : ∃ F ∈ Z, F.Nonempty) :
    ∃ F ∈ Z, ∃ v, zoneSupport L v ∧ zoneSupport F v := by
  by_contra hn
  have hnot : ∀ F ∈ Z, ∀ v, zoneSupport L v → ¬ zoneSupport F v := by
    intro F hF v hv hFv
    exact hn ⟨F, hF, v, hv, hFv⟩
  have hclosed : ∀ u v, G.Adj u v → zoneSupport L u → zoneSupport L v := by
    intro u v huv hu
    have he : s(u, v) ∈ zoneUnion Z ∪ L := hcover.symm ▸ G.mem_edgeFinset.mpr huv
    rcases Finset.mem_union.mp he with hz | hl
    · obtain ⟨F, hF, heF⟩ := (mem_zoneUnion _ Z).mp hz
      exact False.elim (hnot F hF u hu ⟨s(u, v), heF, Sym2.mem_mk_left _ _⟩)
    · exact ⟨s(u, v), hl, Sym2.mem_mk_right _ _⟩
  obtain ⟨e, he⟩ := hL
  obtain ⟨u, hue⟩ : ∃ u : V, u ∈ e := Sym2.ind (fun a b => ⟨a, Sym2.mem_mk_left _ _⟩) e
  obtain ⟨F, hF, f, hf⟩ := hZ
  obtain ⟨v, hvf⟩ : ∃ v : V, v ∈ f := Sym2.ind (fun a b => ⟨a, Sym2.mem_mk_left _ _⟩) f
  have hv : zoneSupport L v := closed_of_reachable _ hclosed (hG.preconnected u v) ⟨e, he, hue⟩
  exact hnot F hF v hv ⟨f, hf, hvf⟩

end OnlineSteinerForest.UpperBound
