import OnlineSteinerForest.UpperBound.ZonesSubdivisionIncidence
import OnlineSteinerForest.UpperBound.NearestNeighborWalkCost

/-! Every original walk has a cost-preserving realization through the inserted midpoints. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [DecidableEq V]

def zoneSplitGraph (E : Finset (Sym2 V)) : SimpleGraph (ZoneSubdivisionVertex V) :=
  SimpleGraph.fromEdgeSet (E.biUnion zoneSplitEdges : Set (Sym2 (ZoneSubdivisionVertex V)))

theorem zoneSplitAdj (E : Finset (Sym2 V)) (e : Sym2 V) (he : e ∈ E) (v : V) (hv : v ∈ e) :
    (zoneSplitGraph E).Adj (Sum.inl v) (Sum.inr e) :=
  ⟨(mem_split_incidence E v e).mpr ⟨he, hv⟩, by simp⟩

def zoneExpandWalk (E : Finset (Sym2 V)) {a b : V}
    (p : (SimpleGraph.fromEdgeSet (E : Set (Sym2 V))).Walk a b) :
    (zoneSplitGraph E).Walk (Sum.inl a) (Sum.inl b) :=
  match p with
  | .nil => .nil
  | @SimpleGraph.Walk.cons _ _ u v w huv p =>
    .cons (zoneSplitAdj E s(u, v) huv.1 u (Sym2.mem_mk_left _ _))
      (.cons (zoneSplitAdj E s(u, v) huv.1 v (Sym2.mem_mk_right _ _)).symm (zoneExpandWalk E p))

theorem zoneExpandWalk_cost (E : Finset (Sym2 V)) (c : Sym2 V → ℝ) {a b : V}
    (p : (SimpleGraph.fromEdgeSet (E : Set (Sym2 V))).Walk a b) :
    walkCost (zoneHalfCost c) (zoneExpandWalk E p) = walkCost c p := by
  induction p with
  | nil => rfl
  | cons huv p ih =>
    simp only [zoneExpandWalk, walkCost_cons, zoneHalfCost_left, zoneHalfCost_right, ih]
    ring

end OnlineSteinerForest.UpperBound
