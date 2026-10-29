import Mathlib.Combinatorics.SimpleGraph.Finite

/-! Actual assignment of every noncenter to a neighboring dominating center. -/
namespace OnlineSteinerForest.UpperBound

open scoped Classical

/-- The assignment fixes centers and uses an actual graph edge elsewhere. -/
theorem exists_star_assignment {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (centers : Finset V)
    (hdom : ∀ v, v ∈ centers ∨ ∃ u ∈ centers, G.Adj v u) :
    ∃ assign : V → V, (∀ v, assign v ∈ centers) ∧
      (∀ v ∈ centers, assign v = v) ∧
      (∀ v ∉ centers, G.Adj v (assign v)) := by
  have hex : ∀ v, ∃ u, u ∈ centers ∧ (v ∈ centers → u = v) ∧
      (v ∉ centers → G.Adj v u) := by
    intro v
    by_cases hv : v ∈ centers
    · exact ⟨v, hv, fun _ => rfl, fun h => False.elim (h hv)⟩
    · obtain ⟨u, hu, hadj⟩ := (hdom v).resolve_left hv
      exact ⟨u, hu, fun h => False.elim (hv h), fun _ => hadj⟩
  choose assign hcenter hfix hadj using hex
  exact ⟨assign, hcenter, hfix, hadj⟩

end OnlineSteinerForest.UpperBound
