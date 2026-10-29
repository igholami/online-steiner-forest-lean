import OnlineSteinerForest.UpperBound.SmallReferenceCost
import OnlineSteinerForest.Graph.Feasibility

/-! Restrict selected actual requests to their ordinary reference component. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def componentPairs (F : Finset (Sym2 V)) (requests : List (V × V))
    (selected : Finset (Fin requests.length))
    (C : (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).ConnectedComponent) : Finset (Fin requests.length) :=
  selected.filter fun i => (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).connectedComponentMk
    requests[i.val].1 = C

theorem componentEdges_connect_pair (F : Finset (Sym2 V)) (u v : V)
    (C : (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).ConnectedComponent)
    (hu : (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).connectedComponentMk u = C)
    (hF : (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).Reachable u v) :
    (SimpleGraph.fromEdgeSet ((componentEdges (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))) C :
      Finset (Sym2 V)) : Set (Sym2 V))).Reachable u v := by
  let H := SimpleGraph.fromEdgeSet (F : Set (Sym2 V))
  have huC : u ∈ C.supp := (C.mem_supp_iff u).mpr hu
  have hvC : v ∈ C.supp := (C.mem_supp_iff v).mpr
    ((SimpleGraph.ConnectedComponent.sound hF).symm.trans hu)
  let f : C.toSimpleGraph →g SimpleGraph.fromEdgeSet
      ((componentEdges H C : Finset (Sym2 V)) : Set (Sym2 V)) :=
    { toFun := Subtype.val
      map_rel' := fun {a b} hab =>
        ⟨(mem_componentEdges H C a.val b.val).mpr
          ⟨hab, (C.mem_supp_iff a.val).mp a.property⟩,
          (show H.Adj a.val b.val from hab).ne⟩ }
  exact (C.connected_toSimpleGraph ⟨u, huC⟩ ⟨v, hvC⟩).map f

theorem componentPairs_connected (F : Finset (Sym2 V)) (requests : List (V × V))
    (selected : Finset (Fin requests.length))
    (hF : ∀ i ∈ selected, (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).Reachable
      requests[i.val].1 requests[i.val].2)
    (C : (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).ConnectedComponent)
    (i : Fin requests.length) (hi : i ∈ componentPairs F requests selected C) :
    (SimpleGraph.fromEdgeSet ((componentEdges (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))) C :
      Finset (Sym2 V)) : Set (Sym2 V))).Reachable requests[i.val].1 requests[i.val].2 :=
  componentEdges_connect_pair F _ _ C (Finset.mem_filter.mp hi).2
    (hF i (Finset.mem_filter.mp hi).1)

end OnlineSteinerForest.UpperBound
