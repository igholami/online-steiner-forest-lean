import OnlineSteinerForest.UpperBound.AuxiliaryLargeEndpoints
import OnlineSteinerForest.UpperBound.BatchSeparation

/-! Canonical original-index retained outputs for a reference forest and an actual computed bucket. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def retainedReferenceRequests (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (F : Finset (Sym2 V)) (b : Fin (requests.length.log2 + 1)) : Finset (Fin requests.length) :=
  retainedAuxRequests G c hc requests feasible fallback
    (largeReferencePairs c requests F (costBatch G c requests feasible b) (batchScale G c requests feasible b.val))
    (batchScale G c requests feasible b.val)

theorem retainedReferenceRequests_subset (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (F : Finset (Sym2 V)) (b : Fin (requests.length.log2 + 1)) :
    retainedReferenceRequests G c hc requests feasible fallback F b ⊆ costBatch G c requests feasible b :=
  (Finset.filter_subset _ _).trans (largeReferencePairs_subset c requests F _ _)

noncomputable def retainedReferenceOutput (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (F : Finset (Sym2 V)) (b : Fin (requests.length.log2 + 1)) (i : Fin requests.length)
    (hi : i ∈ retainedReferenceRequests G c hc requests feasible fallback F b) : AuxiliaryOutput V :=
  retainedAuxOutput G c hc requests feasible fallback
    (largeReferencePairs c requests F (costBatch G c requests feasible b) (batchScale G c requests feasible b.val))
    (batchScale G c requests feasible b.val) i hi

theorem retainedReferenceOutput_helpful (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (hk : 0 < requests.length) (ho : 0 < optimum G c requests feasible)
    (F : Finset (Sym2 V)) (b : Fin (requests.length.log2 + 1)) (i : Fin requests.length)
    (hi : i ∈ retainedReferenceRequests G c hc requests feasible fallback F b) :
    HelpfulAt G c requests feasible i (batchScale G c requests feasible b.val)
      (retainedReferenceOutput G c hc requests feasible fallback F b i hi) := by
  apply retainedAuxOutput_helpful G c hc requests feasible fallback _ _
    (le_of_lt (batchScale_pos G c requests feasible hk ho b.val)) _ i hi
  intro j hj
  have hband := costBatch_band G c requests feasible hk ho b j
    (largeReferencePairs_subset c requests F _ _ hj)
  exact ⟨hband.1, le_of_lt hband.2⟩

theorem retainedReferenceOutput_large (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (F : Finset (Sym2 V)) (b : Fin (requests.length.log2 + 1))
    (hF : ∀ j ∈ costBatch G c requests feasible b,
      (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).Reachable requests[j.val].1 requests[j.val].2)
    (i : Fin requests.length) (hi : i ∈ retainedReferenceRequests G c hc requests feasible fallback F b) :
    let out := retainedReferenceOutput G c hc requests feasible fallback F b i hi
    65536 * (cycleFactor requests.length : ℝ) ^ 3 * batchScale G c requests feasible b.val ≤ referenceTreeCost F c out.left ∧
      65536 * (cycleFactor requests.length : ℝ) ^ 3 * batchScale G c requests feasible b.val ≤ referenceTreeCost F c out.right :=
  retained_large_endpoints G c hc requests feasible fallback F _ _ hF i hi

end OnlineSteinerForest.UpperBound
