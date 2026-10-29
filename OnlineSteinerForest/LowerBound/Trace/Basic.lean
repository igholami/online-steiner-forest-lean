import OnlineSteinerForest.LowerBound.EdgeStructure
import OnlineSteinerForest.LowerBound.Connectivity
import Mathlib.Tactic.Ring

/-! A lower-bound route records unit path steps and complete matching traversals. -/
namespace OnlineSteinerForest.LowerBound.Trace

variable {m : ℕ}

/-- A route on original vertices. Matching traversals are labeled by their rank. -/
inductive Route (σ : Equiv.Perm (Fin (2 * m))) (R : Finset (Fin m)) :
    Fin (2 * m) → Fin (2 * m) → Type
  | nil (u) : Route σ R u u
  | base {u v z} (h : (SimpleGraph.pathGraph (2 * m)).Adj u v)
      (p : Route σ R v z) : Route σ R u z
  | shortcut {u v z} (i : Fin m) (hi : i ∈ R)
      (orientation : (u = leftEndpoint σ i ∧ v = rightEndpoint σ i) ∨
        (u = rightEndpoint σ i ∧ v = leftEndpoint σ i))
      (p : Route σ R v z) : Route σ R u z

namespace Route

variable {σ : Equiv.Perm (Fin (2 * m))} {R : Finset (Fin m)} {u v : Fin (2 * m)}

/-- Realize every matching traversal through its private degree-two vertex. -/
def realize : {u v : Fin (2 * m)} → Route σ R u v →
    (constructionGraph σ R).Walk (Sum.inl u) (Sum.inl v)
  | _, _, .nil _ => .nil
  | _, _, .base h p => .cons ((comparisonHom σ R).map_rel h) p.realize
  | a, b, .shortcut i hi ho p => .cons
      (by apply SimpleGraph.Adj.symm; apply (subdivision_adj σ R i _).mpr
          exact ⟨hi, by rcases ho with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp⟩)
      (.cons (by apply (subdivision_adj σ R i _).mpr
                 exact ⟨hi, by rcases ho with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp⟩) p.realize)

def support : {u v : Fin (2 * m)} → Route σ R u v → List (Fin (2 * m))
  | _, _, .nil a => [a]
  | a, _, .base _ p => a :: p.support
  | a, _, .shortcut _ _ _ p => a :: p.support

def ranks : {u v : Fin (2 * m)} → Route σ R u v → List (Fin m)
  | _, _, .nil _ => []
  | _, _, .base _ p => p.ranks
  | _, _, .shortcut i _ _ p => i :: p.ranks

def baseSteps : {u v : Fin (2 * m)} → Route σ R u v → ℕ
  | _, _, .nil _ => 0
  | _, _, .base _ p => p.baseSteps + 1
  | _, _, .shortcut _ _ _ p => p.baseSteps

noncomputable def cost (w : Fin m → ℝ) : {u v : Fin (2 * m)} → Route σ R u v → ℝ
  | _, _, .nil _ => 0
  | _, _, .base _ p => 1 + p.cost w
  | _, _, .shortcut i _ _ p => w i + p.cost w

theorem realize_cost (w : Fin m → ℝ) (p : Route σ R u v) :
    (p.realize.edges.map (constructionCost w)).sum = p.cost w := by
  induction p with
  | nil => simp [realize, cost]
  | base h p ih =>
    change 1 + (p.realize.edges.map (constructionCost w)).sum = 1 + p.cost w
    rw [ih]
  | shortcut i hi ho p ih =>
    simp only [realize, SimpleGraph.Walk.edges_cons, List.map_cons, List.sum_cons,
      constructionCost_left, constructionCost_right, ih, cost]
    ring

theorem cost_eq_base_plus_ranks (w : Fin m → ℝ) (p : Route σ R u v) :
    p.cost w = p.baseSteps + (p.ranks.map w).sum := by
  induction p with
  | nil => simp [cost, baseSteps, ranks]
  | base h p ih => simp [cost, baseSteps, ranks, ih]; ring
  | shortcut i hi ho p ih => simp [cost, baseSteps, ranks, ih]; ring

end Route
end OnlineSteinerForest.LowerBound.Trace
