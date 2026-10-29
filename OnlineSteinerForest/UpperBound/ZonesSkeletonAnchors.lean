import OnlineSteinerForest.UpperBound.ZonesSkeletonData

/-! Every noncenter anchor is an endpoint of its own selected assignment path. -/
namespace OnlineSteinerForest.UpperBound.ZoneSkeletonData

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  {G : SimpleGraph V} {centers : Finset V} {stars : StarContraction G centers}
  {f : InterstarForest stars} {ambient : SimpleGraph W} {zones : V → Finset (Sym2 W)}

noncomputable def anchor (d : ZoneSkeletonData f ambient zones) (centerAnchor : ↥centers → W) (v : V) : W :=
  if h : v ∈ centers then centerAnchor ⟨v, h⟩ else d.left (.inl ⟨v, h⟩)

theorem anchor_mem (d : ZoneSkeletonData f ambient zones) (a : ↥centers → W)
    (ha : ∀ v, zoneSupport (zones v.val) (a v)) (v : V) : zoneSupport (zones v) (d.anchor a v) := by
  unfold anchor
  split_ifs with h
  · exact ha ⟨v, h⟩
  · exact d.left_mem (.inl ⟨v, h⟩)

theorem within_retained_zone (d : ZoneSkeletonData f ambient zones)
    (hconn : ∀ v, ZoneConnected (zones v)) {v : V} (hv : v ∈ f.retainedZones)
    {a b : W} (ha : zoneSupport (zones v) a) (hb : zoneSupport (zones v) b) :
    (SimpleGraph.fromEdgeSet (d.edges : Set (Sym2 W))).Reachable a b := by
  obtain ⟨e, he, hbe⟩ := hb
  exact (((hconn v).root_at ha) e he b hbe).mono (fromEdges_mono (d.zone_subset v hv))

theorem anchor_to_center (d : ZoneSkeletonData f ambient zones) (a : ↥centers → W)
    (ha : ∀ v, zoneSupport (zones v.val) (a v)) (hconn : ∀ v, ZoneConnected (zones v)) (v : V) :
    (SimpleGraph.fromEdgeSet (d.edges : Set (Sym2 W))).Reachable (d.anchor a v) (a (stars.assign v)) := by
  by_cases hv : v ∈ centers
  · have heq : stars.assign v = ⟨v, hv⟩ := stars.fixes ⟨v, hv⟩
    simp only [anchor, dif_pos hv, heq]
    exact .refl _
  · simp only [anchor, dif_neg hv]
    change (SimpleGraph.fromEdgeSet (d.edges : Set (Sym2 W))).Reachable
      (d.left (.inl ⟨v, hv⟩)) (a (stars.assign v))
    exact (d.path_reachable (.inl ⟨v, hv⟩)).trans
      (d.within_retained_zone hconn (f.center_retained (stars.assign v).property)
        (d.right_mem (.inl ⟨v, hv⟩)) (ha (stars.assign v)))

end OnlineSteinerForest.UpperBound.ZoneSkeletonData
