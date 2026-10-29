import OnlineSteinerForest.Graph.Residual

/-! Greedy executions with independently chosen minimizing paths at every arrival. -/
namespace OnlineSteinerForest

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Each arrival may choose any minimizing simple path, independently of earlier ties. -/
structure GreedyExecution (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) where
  state : ℕ → Finset (Sym2 V)
  path : Fin requests.length → Finset (Sym2 V)
  initial : state 0 = ∅
  valid : ∀ i, IsPathEdges G requests[i.val].1 requests[i.val].2 (path i)
  minimal : ∀ i F, IsPathEdges G requests[i.val].1 requests[i.val].2 F →
    residualCost c (state i.val) (path i) ≤ residualCost c (state i.val) F
  step : ∀ i, state (i.val + 1) = state i.val ∪ path i

namespace GreedyExecution

variable {G : SimpleGraph V} {c : Sym2 V → ℝ} {requests : List (V × V)}

/-- States only increase during the actual finite execution. -/
theorem state_mono (E : GreedyExecution G c requests) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ requests.length) : E.state i ⊆ E.state j := by
  induction j, hij using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ j hij ih =>
    have hj' : j < requests.length := by omega
    exact (ih (by omega)).trans (by
      rw [E.step ⟨j, hj'⟩]
      exact Finset.subset_union_left)

/-- Strictly positive unpurchased edges cannot belong to a zero-payment path. -/
theorem path_subset_of_cost_le_zero (E : GreedyExecution G c requests)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (i : Fin requests.length)
    (h : residualCost c (E.state i.val) (E.path i) ≤ 0) :
    E.path i ⊆ E.state i.val := by
  intro e he
  by_contra hn
  have hem : e ∈ E.path i \ E.state i.val := Finset.mem_sdiff.mpr ⟨he, hn⟩
  have hpos : 0 < residualCost c (E.state i.val) (E.path i) := by
    apply Finset.sum_pos'
    · intro x hx
      exact le_of_lt (hc x (IsPathEdges.subset_edgeSet.{u} (E.valid i) x (Finset.mem_sdiff.mp hx).1))
    · exact ⟨e, hem, hc e (IsPathEdges.subset_edgeSet.{u} (E.valid i) e he)⟩
  exact (not_lt_of_ge h) hpos

/-- A repeated state and request have the same successor, whatever minimizing paths were used. -/
theorem same_query_successor (E : GreedyExecution G c requests)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (i j : Fin requests.length)
    (hstate : E.state i.val = E.state j.val) (hpair : requests[i.val] = requests[j.val]) :
    E.state i.val ∪ E.path i = E.state j.val ∪ E.path j := by
  suffices ∀ a b : Fin requests.length, a.val < b.val →
      E.state a.val = E.state b.val → requests[a.val] = requests[b.val] →
      E.state a.val ∪ E.path a = E.state b.val ∪ E.path b by
    rcases lt_trichotomy i.val j.val with hij | hij | hij
    · exact this i j hij hstate hpair
    · have : i = j := Fin.ext hij
      subst j
      rfl
    · exact (this j i hij hstate.symm hpair.symm).symm
  intro a b hab hs hp
  have hsub : E.path a ⊆ E.state b.val := by
    apply Finset.Subset.trans Finset.subset_union_right
    rw [← E.step a]
    exact E.state_mono (by omega) (by omega)
  have hzero : residualCost c (E.state b.val) (E.path a) = 0 :=
    residualCost_eq_zero_of_subset.{u, 0} c _ _ hsub
  have hvalid : IsPathEdges G requests[b.val].1 requests[b.val].2 (E.path a) := by
    rw [← hp]
    exact E.valid a
  have hb := E.path_subset_of_cost_le_zero hc b (by
    have hm := E.minimal b _ hvalid
    rwa [hzero] at hm)
  rw [Finset.union_eq_left.mpr hb, hs, Finset.union_eq_left.mpr hsub]

end GreedyExecution
end OnlineSteinerForest
