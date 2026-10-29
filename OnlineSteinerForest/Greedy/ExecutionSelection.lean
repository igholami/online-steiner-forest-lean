import OnlineSteinerForest.Greedy.Execution

/-! A state-based tie rule reproducing an independently tied finite execution. -/
namespace OnlineSteinerForest.GreedyExecution

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {c : Sym2 V → ℝ} {requests : List (V × V)}

/-- The finite execution's query table. -/
def Matches (E : GreedyExecution G c requests) (B : Finset (Sym2 V)) (s t : V)
    (i : Fin requests.length) : Prop := E.state i.val = B ∧ requests[i.val] = (s, t)

/-- Use an observed minimizing path when available, with canonical minimization elsewhere. -/
noncomputable def select (E : GreedyExecution G c requests) (B : Finset (Sym2 V))
    (s t : V) (h : G.Reachable s t) : Finset (Sym2 V) := by
  classical
  exact if hm : ∃ i, E.Matches B s t i then E.path hm.choose
    else @shortestPathEdges _ _ _ canonicalPathSelection G c B s t h

theorem select_spec (E : GreedyExecution G c requests) (B : Finset (Sym2 V))
    (s t : V) (h : G.Reachable s t) :
    IsPathEdges G s t (E.select B s t h) ∧
      ∀ F, IsPathEdges G s t F →
        residualCost c B (E.select B s t h) ≤ residualCost c B F := by
  classical
  unfold select
  split
  next hm =>
    obtain ⟨hs, hp⟩ := hm.choose_spec
    have hv := E.valid hm.choose
    have hmin := E.minimal hm.choose
    simp only [hp, Prod.fst, Prod.snd] at hv hmin
    rw [hs] at hmin
    exact ⟨hv, hmin⟩
  next hm => exact @shortestPathEdges_spec _ _ _ canonicalPathSelection G c B s t h

/-- The table can select a different zero-cost path, but purchases exactly the observed successor. -/
theorem select_successor (E : GreedyExecution G c requests)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (i : Fin requests.length)
    (h : G.Reachable requests[i.val].1 requests[i.val].2) :
    E.state i.val ∪ E.select (E.state i.val) requests[i.val].1 requests[i.val].2 h =
      E.state (i.val + 1) := by
  classical
  have hm : ∃ j, E.Matches (E.state i.val) requests[i.val].1 requests[i.val].2 j :=
    ⟨i, rfl, by simp⟩
  unfold select
  rw [dif_pos hm, E.step i]
  obtain ⟨hs, hp⟩ := hm.choose_spec
  have hp' : requests[hm.choose.val] = requests[i.val] := by simpa using hp
  have heq := E.same_query_successor hc hm.choose i hs hp'
  simpa only [hs] using heq

end OnlineSteinerForest.GreedyExecution
