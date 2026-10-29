import OnlineSteinerForest.UpperBound.NearestNeighborCoordinates
import OnlineSteinerForest.UpperBound.NearestNeighborCyclicPacking
import OnlineSteinerForest.UpperBound.NearestNeighborTour

/-! Pairwise-separated tree vertices consume at least half their total separation in edge cost. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical

variable {V : Type*} {G : SimpleGraph V}

noncomputable def visitPosition {r : V} (p : G.Walk r r) (hcover : ∀ v, v ∈ p.support) (v : V) : ℕ :=
  Classical.choose (SimpleGraph.Walk.mem_support_iff_exists_getVert.mp (hcover v))

theorem visitPosition_vertex {r : V} (p : G.Walk r r) (hcover : ∀ v, v ∈ p.support) (v : V) :
    p.getVert (visitPosition p hcover v) = v :=
  (Classical.choose_spec (SimpleGraph.Walk.mem_support_iff_exists_getVert.mp (hcover v))).1

theorem visitPosition_injective {r : V} (p : G.Walk r r) (hcover : ∀ v, v ∈ p.support) :
    Function.Injective (visitPosition p hcover) := by
  intro u v huv
  calc
    u = p.getVert (visitPosition p hcover u) := (visitPosition_vertex p hcover u).symm
    _ = p.getVert (visitPosition p hcover v) := congrArg p.getVert huv
    _ = v := visitPosition_vertex p hcover v

variable [Fintype V] [DecidableEq V]

theorem walk_packing (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (hconn : G.Preconnected)
    (K : Finset V) (hcard : 2 ≤ K.card) (δ : ℝ)
    (hsep : ∀ u ∈ K, ∀ v ∈ K, u ≠ v → δ ≤ residualDistance G c ∅ u v (hconn u v))
    (r : V) (p : G.Walk r r) (hcover : ∀ v, v ∈ p.support) :
    (K.card : ℝ) * δ ≤ walkCost c p := by
  let I := K.image (visitPosition p hcover)
  have hcardI : I.card = K.card := Finset.card_image_of_injective K (visitPosition_injective p hcover)
  have hpoint : ∀ i ∈ I, p.getVert i ∈ K := by
    intro i hi
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
    simpa only [visitPosition_vertex] using hv
  have hinverse : ∀ i ∈ I, visitPosition p hcover (p.getVert i) = i := by
    intro i hi
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hi
    rw [visitPosition_vertex]
  have hdistinct : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → p.getVert i ≠ p.getVert j := by
    intro i hi j hj hij heq
    exact hij ((hinverse i hi).symm.trans ((congrArg (visitPosition p hcover) heq).trans (hinverse j hj)))
  have hpacking := finite_cyclic_packing I (prefixCost c p) δ (walkCost c p)
    (by rw [hcardI]; exact hcard)
    (fun i hi j hj hij => (hsep _ (hpoint i hi) _ (hpoint j hj)
      (hdistinct i hi j hj (ne_of_lt hij))).trans
      (distance_le_prefix_difference c hc p i j hij.le (hconn _ _)))
    (fun i hi j hj hij => (hsep _ (hpoint j hj) _ (hpoint i hi)
      (hdistinct j hj i hi hij.symm)).trans
      (distance_le_wrap_difference c hc p i j (hconn _ _)))
  rwa [hcardI] at hpacking

/-- The Euler-tour packing estimate appearing in the nearest-neighbor lemma. -/
theorem tree_packing (G : SimpleGraph V) (hG : G.IsTree) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (K : Finset V) (hcard : 2 ≤ K.card) (δ : ℝ)
    (hsep : ∀ u ∈ K, ∀ v ∈ K, u ≠ v →
      δ ≤ residualDistance G c ∅ u v (hG.connected.preconnected u v)) :
    (K.card : ℝ) * δ ≤ 2 * edgeCost c G.edgeFinset := by
  obtain ⟨r, p, hcover, hcost⟩ := exists_tree_tour G hG c hc
  exact (walk_packing G c hc hG.connected.preconnected K hcard δ hsep r p hcover).trans hcost

end OnlineSteinerForest.UpperBound
