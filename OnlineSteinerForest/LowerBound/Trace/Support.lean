import OnlineSteinerForest.LowerBound.Trace.Basic

/-! Simple routes visit distinct original vertices and distinct shortcut ranks. -/
namespace OnlineSteinerForest.LowerBound.Trace

variable {m : ℕ}

def originalVertex : Vertex m → Option (Fin (2 * m))
  | .inl u => some u
  | .inr _ => none

def privateVertex : Vertex m → Option (Fin m)
  | .inl _ => none
  | .inr i => some i

namespace Route

variable {σ : Equiv.Perm (Fin (2 * m))} {R : Finset (Fin m)} {u v : Fin (2 * m)}

theorem realize_support_original (p : Route σ R u v) :
    p.realize.support.filterMap originalVertex = p.support := by
  induction p with
  | nil => rfl
  | @base a b z h p ih =>
    change (Sum.inl a :: p.realize.support).filterMap originalVertex = a :: p.support
    simp only [List.filterMap_cons, originalVertex, ih]
  | @shortcut a b z i hi ho p ih =>
    change (Sum.inl a :: Sum.inr i :: p.realize.support).filterMap originalVertex = a :: p.support
    simp only [List.filterMap_cons, originalVertex, ih]

theorem realize_support_private (p : Route σ R u v) :
    p.realize.support.filterMap privateVertex = p.ranks := by
  induction p with
  | nil => rfl
  | @base a b z h p ih =>
    change (Sum.inl a :: p.realize.support).filterMap privateVertex = p.ranks
    simp only [List.filterMap_cons, privateVertex, ih]
  | @shortcut a b z i hi ho p ih =>
    change (Sum.inl a :: Sum.inr i :: p.realize.support).filterMap privateVertex = i :: p.ranks
    simp only [List.filterMap_cons, privateVertex, ih]

theorem support_nodup (p : Route σ R u v) (hp : p.realize.IsPath) : p.support.Nodup := by
  rw [← p.realize_support_original]
  apply List.Nodup.filterMap _ hp.support_nodup
  intro a b c ha hb
  cases a <;> cases b <;> simp_all [originalVertex]

theorem ranks_nodup (p : Route σ R u v) (hp : p.realize.IsPath) : p.ranks.Nodup := by
  rw [← p.realize_support_private]
  apply List.Nodup.filterMap _ hp.support_nodup
  intro a b c ha hb
  cases a <;> cases b <;> simp_all [privateVertex]

theorem rank_mem (p : Route σ R u v) (i : Fin m) (hi : i ∈ p.ranks) : i ∈ R := by
  induction p with
  | nil => simp [ranks] at hi
  | base h p ih => exact ih hi
  | shortcut j hj ho p ih =>
    simp only [ranks, List.mem_cons] at hi
    rcases hi with rfl | hi
    · exact hj
    · exact ih hi

theorem start_mem_support (p : Route σ R u v) : u ∈ p.support := by
  cases p <;> simp [support]

theorem end_mem_support (p : Route σ R u v) : v ∈ p.support := by
  induction p <;> simp [support, *]

theorem edgeCost_realize (w : Fin m → ℝ) (p : Route σ R u v) (hp : p.realize.IsPath) :
    edgeCost (constructionCost w) p.realize.edges.toFinset = p.cost w := by
  exact (List.sum_toFinset _ hp.isTrail.edges_nodup).trans (realize_cost w p)

theorem baseSteps_le_cost (w : Fin m → ℝ) (hw : ∀ i ∈ R, 0 ≤ w i) (p : Route σ R u v) :
    (p.baseSteps : ℝ) ≤ p.cost w := by
  rw [cost_eq_base_plus_ranks]
  apply le_add_of_nonneg_right
  apply List.sum_nonneg
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  exact hw i (p.rank_mem i hi)

end Route
end OnlineSteinerForest.LowerBound.Trace
