import OnlineSteinerForest.UpperBound.NearestNeighborInducedCost
import OnlineSteinerForest.UpperBound.FinalParameters
import OnlineSteinerForest.Graph.Cost

/-! Compute the small/large split using ordinary reference-forest connected components. -/
namespace OnlineSteinerForest.UpperBound

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def referenceTreeCost (F : Finset (Sym2 V)) (c : Sym2 V → ℝ) (root : V) : ℝ :=
  let H := SimpleGraph.fromEdgeSet (F : Set (Sym2 V))
  let C := H.connectedComponentMk root
  graphCost C.toSimpleGraph (fun e => c (Sym2.map Subtype.val e))

theorem referenceTreeCost_eq_of_reachable (F : Finset (Sym2 V)) (c : Sym2 V → ℝ) (u v : V)
    (h : (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).Reachable u v) :
    referenceTreeCost F c u = referenceTreeCost F c v := by
  exact congrArg (fun C : (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).ConnectedComponent =>
    graphCost C.toSimpleGraph (fun e => c (Sym2.map Subtype.val e))) (SimpleGraph.ConnectedComponent.sound h)

noncomputable def smallReferencePairs (c : Sym2 V → ℝ) (requests : List (V × V))
    (F : Finset (Sym2 V)) (batch : Finset (Fin requests.length)) (scale : ℝ) : Finset (Fin requests.length) :=
  batch.filter (fun i => referenceTreeCost F c requests[i.val].1 <
    65536 * (cycleFactor requests.length : ℝ) ^ 3 * scale)

noncomputable def largeReferencePairs (c : Sym2 V → ℝ) (requests : List (V × V))
    (F : Finset (Sym2 V)) (batch : Finset (Fin requests.length)) (scale : ℝ) : Finset (Fin requests.length) :=
  batch \ smallReferencePairs c requests F batch scale

theorem largeReferencePairs_subset (c : Sym2 V → ℝ) (requests : List (V × V))
    (F : Finset (Sym2 V)) (batch : Finset (Fin requests.length)) (scale : ℝ) :
    largeReferencePairs c requests F batch scale ⊆ batch := Finset.sdiff_subset

theorem largeReferencePairs_endpoints (c : Sym2 V → ℝ) (requests : List (V × V))
    (F : Finset (Sym2 V)) (batch : Finset (Fin requests.length)) (scale : ℝ)
    (hF : ∀ i ∈ batch, (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).Reachable requests[i.val].1 requests[i.val].2)
    (i : Fin requests.length) (hi : i ∈ largeReferencePairs c requests F batch scale) :
    65536 * (cycleFactor requests.length : ℝ) ^ 3 * scale ≤ referenceTreeCost F c requests[i.val].1 ∧
    65536 * (cycleFactor requests.length : ℝ) ^ 3 * scale ≤ referenceTreeCost F c requests[i.val].2 := by
  obtain ⟨hib, hin⟩ := Finset.mem_sdiff.mp hi
  have hleft : 65536 * (cycleFactor requests.length : ℝ) ^ 3 * scale ≤ referenceTreeCost F c requests[i.val].1 := by
    by_contra h
    exact hin (Finset.mem_filter.mpr ⟨hib, lt_of_not_ge h⟩)
  exact ⟨hleft, hleft.trans_eq (referenceTreeCost_eq_of_reachable F c _ _ (hF i hib))⟩

end OnlineSteinerForest.UpperBound
