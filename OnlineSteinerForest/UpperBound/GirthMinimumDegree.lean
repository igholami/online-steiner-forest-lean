import OnlineSteinerForest.UpperBound.GirthShortWalks
import OnlineSteinerForest.UpperBound.GirthSubdivisionChain
import OnlineSteinerForest.UpperBound.GirthSubdivisionTrace
import OnlineSteinerForest.UpperBound.GirthSubdivisionCost

/-! The weighted short-cycle theorem for minimum-degree-three labelled multigraphs. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*} [Fintype V] [Fintype I] [DecidableEq I] [DecidableEq V] [Nonempty I]

theorem minimum_degree_short_cycle (left right : I → V)
    (hdegree : ∀ v, 3 ≤ degree left right v) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hC : 0 < ∑ i, w i) (n : ℕ)
    (hn : 2 * (Fintype.card V : ℝ) < (2 : ℝ) ^ n) :
    ∃ z, ∃ c : (edgeSubdivision left right).Walk z z, c.IsCycle ∧
      (c.edges.map (subdivisionCost w)).sum ≤
        4 * (n + 1 : ℕ) * (∑ i, w i) / Fintype.card I := by
  obtain ⟨p, q, hne, hp, hq, hf, hl, hcost⟩ :=
    two_short_nonbacktracking_walks left right hdegree w hw hC n hn
  let P := subdividedWalk left right n p hp
  let Q := (subdividedWalk left right n q hq).copy
    (congrArg Sum.inl (congrArg (tail left right) hf).symm) (congrArg Sum.inl hl.symm)
  have hPQ : P ≠ Q := by
    intro heq
    apply hne
    apply subdividedWalk_support_injective left right n p q hp hq
    have hh := congrArg SimpleGraph.Walk.support heq
    simpa [P, Q] using hh
  have hP : List.IsChain (· ≠ ·) P.edges := subdividedWalk_chain left right n p hp
  have hQ : List.IsChain (· ≠ ·) Q.edges := by
    simpa [Q] using subdividedWalk_chain left right n q hq
  obtain ⟨z, c, hc, hcc⟩ := cycle_cost_in_two_walks P Q hPQ hP hQ
    (subdivisionCost w) (subdivisionCost_nonneg w hw)
  refine ⟨z, c, hc, hcc.trans ?_⟩
  simpa [P, Q, subdividedWalk_cost] using hcost

end OnlineSteinerForest.UpperBound.Girth
