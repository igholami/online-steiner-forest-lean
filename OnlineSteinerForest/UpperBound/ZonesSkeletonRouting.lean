import OnlineSteinerForest.UpperBound.ZonesSkeletonAnchors
import OnlineSteinerForest.UpperBound.ZonesInterstarRouting

/-! The actual replacement skeleton connects all zone anchors in every core component. -/
namespace OnlineSteinerForest.UpperBound.ZoneSkeletonData

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  {G : SimpleGraph V} {centers : Finset V} {stars : StarContraction G centers}
  {f : InterstarForest stars} {ambient : SimpleGraph W} {zones : V → Finset (Sym2 W)}

theorem interstar_anchor_links (d : ZoneSkeletonData f ambient zones) (a : ↥centers → W)
    (ha : ∀ v, zoneSupport (zones v.val) (a v)) (hconn : ∀ v, ZoneConnected (zones v))
    (e : ↥f.graph.edgeFinset) :
    (SimpleGraph.fromEdgeSet (d.edges : Set (Sym2 W))).Reachable
      (a (stars.assign (f.left e))) (a (stars.assign (f.right e))) := by
  have hleft := d.within_retained_zone hconn (f.left_retained e)
    (d.anchor_mem a ha (f.left e)) (d.left_mem (.inr e))
  have hright := d.within_retained_zone hconn (f.right_retained e)
    (d.right_mem (.inr e)) (d.anchor_mem a ha (f.right e))
  exact (d.anchor_to_center a ha hconn (f.left e)).symm.trans
    (hleft.trans ((d.path_reachable (.inr e)).trans
      (hright.trans (d.anchor_to_center a ha hconn (f.right e)))))

theorem anchors_connected (d : ZoneSkeletonData f ambient zones) (a : ↥centers → W)
    (ha : ∀ v, zoneSupport (zones v.val) (a v)) (hconn : ∀ v, ZoneConnected (zones v))
    {u v : V} (huv : G.Reachable u v) :
    (SimpleGraph.fromEdgeSet (d.edges : Set (Sym2 W))).Reachable (d.anchor a u) (d.anchor a v) := by
  have hcenters := f.route_core_connections (SimpleGraph.fromEdgeSet (d.edges : Set (Sym2 W))) a
    (d.interstar_anchor_links a ha hconn) huv
  exact (d.anchor_to_center a ha hconn u).trans
    (hcenters.trans (d.anchor_to_center a ha hconn v).symm)

end OnlineSteinerForest.UpperBound.ZoneSkeletonData
