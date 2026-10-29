import OnlineSteinerForest.Greedy.Algorithm
import OnlineSteinerForest.Graph.Optimum
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
The manuscript's two main claims, in a single short file.

These specifications do not assume accounting or matching-existence claims.
UpperBound/Main.lean and LowerBound/Main.lean prove these exact propositions.
Main.lean presents both explicit main theorem statements together.
-/
namespace OnlineSteinerForest

variable [OnlineSteinerForest.PathSelection]

/-- Theorem 1 (upper bound): one absolute constant works for every finite graph,
positive edge-cost assignment, and feasible nonempty request sequence. -/
def UpperBoundStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (c : Sym2 (Fin n) → ℝ)
      (requests : List (Fin n × Fin n))
      (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2),
      (∀ e ∈ G.edgeSet, 0 < c e) → 1 ≤ requests.length →
      greedyCost G c requests feasible ≤
        C * optimum G c requests feasible *
          Real.log (2 * requests.length) * Real.log (Real.log (4 * requests.length))

/-- Theorem 2 (lower bound): one positive constant and instances with arbitrarily
many requests. `OPT > 0` prevents a vacuous zero-cost lower bound. -/
def LowerBoundStatement : Prop :=
  ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ K : ℕ,
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (c : Sym2 (Fin n) → ℝ)
      (requests : List (Fin n × Fin n))
      (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2),
      (∀ e ∈ G.edgeSet, 0 < c e) ∧
      max K 3 ≤ requests.length ∧ 0 < optimum G c requests feasible ∧
      c₀ * optimum G c requests feasible *
          Real.log requests.length * Real.log (Real.log requests.length) ≤
        greedyCost G c requests feasible

end OnlineSteinerForest
