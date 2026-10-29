import OnlineSteinerForest.UpperBound.NearestNeighborDistances

/-! Prefix lengths on a closed walk give coordinates for the packing argument. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

omit [Fintype V] [DecidableEq V] in
@[simp] theorem walkCost_copy (c : Sym2 V → ℝ) {s t u v : V} (p : G.Walk s t)
    (hs : s = u) (ht : t = v) : walkCost c (p.copy hs ht) = walkCost c p := by
  simp [walkCost]

noncomputable def prefixCost (c : Sym2 V → ℝ) {s t : V} (p : G.Walk s t) (i : ℕ) : ℝ :=
  walkCost c (p.take i)

omit [Fintype V] [DecidableEq V] in
theorem prefixCost_add (c : Sym2 V → ℝ) {s t : V} (p : G.Walk s t) (i j : ℕ) :
    prefixCost c p (i + j) = prefixCost c p i + walkCost c ((p.drop i).take j) := by
  rw [prefixCost, p.take_add_eq, walkCost_copy, walkCost_append]
  rfl

def walkSegment {s t : V} (p : G.Walk s t) (i j : ℕ) (hij : i ≤ j) :
    G.Walk (p.getVert i) (p.getVert j) :=
  ((p.drop i).take (j - i)).copy rfl (by rw [SimpleGraph.Walk.drop_getVert, Nat.add_sub_of_le hij])

omit [Fintype V] [DecidableEq V] in
theorem walkSegment_cost (c : Sym2 V → ℝ) {s t : V} (p : G.Walk s t)
    (i j : ℕ) (hij : i ≤ j) :
    walkCost c (walkSegment p i j hij) = prefixCost c p j - prefixCost c p i := by
  have heq := prefixCost_add c p i (j - i)
  rw [Nat.add_sub_of_le hij] at heq
  simp only [walkSegment, walkCost_copy]
  linarith

theorem distance_le_prefix_difference (c : Sym2 V → ℝ) (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e)
    {s t : V} (p : G.Walk s t) (i j : ℕ) (hij : i ≤ j)
    (hconn : G.Reachable (p.getVert i) (p.getVert j)) :
    residualDistance G c ∅ (p.getVert i) (p.getVert j) hconn ≤ prefixCost c p j - prefixCost c p i := by
  have hh := residualDistance_le_walkCost G c hc _ _ hconn (walkSegment p i j hij)
  rwa [walkSegment_cost] at hh

theorem distance_le_wrap_difference (c : Sym2 V → ℝ) (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e)
    {r : V} (p : G.Walk r r) (i j : ℕ)
    (hconn : G.Reachable (p.getVert j) (p.getVert i)) :
    residualDistance G c ∅ (p.getVert j) (p.getVert i) hconn ≤
      walkCost c p - prefixCost c p j + prefixCost c p i := by
  have hsplit := congrArg (walkCost c) (p.append_take_drop_eq j)
  rw [walkCost_append] at hsplit
  have hh := residualDistance_le_walkCost G c hc _ _ hconn ((p.drop j).append (p.take i))
  rw [walkCost_append] at hh
  change walkCost c (p.take j) + walkCost c (p.drop j) = walkCost c p at hsplit
  change residualDistance G c ∅ _ _ hconn ≤ walkCost c p - walkCost c (p.take j) + walkCost c (p.take i)
  linarith

end OnlineSteinerForest.UpperBound
