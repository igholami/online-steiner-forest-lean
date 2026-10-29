import OnlineSteinerForest.UpperBound.GirthWeightedRank
import OnlineSteinerForest.UpperBound.GirthSimpleTraceChain

/-! The weighted cycle-rank bound returns a cycle directly in the given standard simple graph. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

theorem weighted_simple_cycle_rank_bound (G : SimpleGraph V) (left right : I → V)
    (ha : ∀ i, G.Adj (left i) (right i))
    (hinj : Function.Injective (fun i => s(left i, right i)))
    (c : Sym2 V → ℝ) (hc : ∀ e, 0 ≤ c e) (hr : 1 ≤ cycleRank left right) :
    ∃ z, ∃ p : G.Walk z z, p.IsCycle ∧ (p.edges.map c).sum ≤
      4 * cycleFactor (cycleRank left right) * (∑ i, c s(left i, right i)) / cycleRank left right := by
  obtain ⟨p, hp⟩ := weighted_collision_rank_bound left right (fun i => c s(left i, right i)) (fun i => hc _) hr
  let P := simpleTraceWalk left right ha p.firstTrace p.firstValid
  let Q := simpleTraceWalk left right ha p.secondTrace p.secondValid
  have hPQ : P ≠ Q := by
    intro h
    apply p.distinct
    apply simpleTrace_edge_lists_injective left right ha hinj _ _ p.firstValid p.secondValid
    have hh := congrArg SimpleGraph.Walk.edges h
    simpa only [P, Q, simpleTraceWalk_edges] using hh
  obtain ⟨z, C, hC, hcost⟩ := cycle_cost_in_two_walks P Q hPQ
    (simpleTraceWalk_chain left right ha hinj p.firstTrace p.firstValid p.firstNonbacktracking)
    (simpleTraceWalk_chain left right ha hinj p.secondTrace p.secondValid p.secondNonbacktracking) c hc
  refine ⟨z, C, hC, hcost.trans ?_⟩
  simpa only [P, Q, simpleTraceWalk_cost, Collision.cost] using hp

end OnlineSteinerForest.UpperBound.Girth
