# Statements and their project-defined dependencies

This is the recursive **statement/definition dependency closure** of the two main bounds, ordered so each project-defined dependency appears before its use. Mathlib definitions are left unexpanded. Helper theorems needed to construct definitions retain their complete proofs; **only the two main theorem proofs are replaced by `by sorry`** in this document.

The upper/lower proof dependency trees are not reproduced: those contain the analysis proving the bounds, rather than definitions needed to understand their statements. The `.lean` source files contain complete proofs; the two placeholders appear only in this document.

Concatenating the Lean blocks gives a standalone statement-review file importing only mathlib. All displayed declarations keep their project names under `OnlineSteinerForest`.

## Mathlib imports and namespace

```lean
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace OnlineSteinerForest
universe u
```

## Edge costs

The original cost sums all selected edge costs. Residual cost charges only edges not already purchased.

Source: [Graph/Cost.lean](OnlineSteinerForest/Graph/Cost.lean).

```lean
section
variable {V : Type*} [DecidableEq V]

def edgeCost (c : Sym2 V → ℝ) (F : Finset (Sym2 V)) : ℝ :=
  ∑ e ∈ F, c e

def residualCost (c : Sym2 V → ℝ) (B F : Finset (Sym2 V)) : ℝ :=
  ∑ e ∈ F \ B, c e

end
```

## Paths and shortest-path selection

Candidates are edge sets of actual mathlib simple paths. The two helper theorems below are included because the definition of shortestPathEdges depends on their proofs. Classical choice selects a minimum residual-cost candidate.

Source: [Graph/Paths.lean](OnlineSteinerForest/Graph/Paths.lean).

```lean
section
variable {V : Type*} [Fintype V] [DecidableEq V]

def IsPathEdges (G : SimpleGraph V) (s t : V) (F : Finset (Sym2 V)) : Prop :=
  ∃ p : G.Walk s t, p.IsPath ∧ p.edges.toFinset = F

noncomputable def pathCandidates (G : SimpleGraph V) (s t : V) :
    Finset (Finset (Sym2 V)) := by
  classical
  exact Finset.univ.filter (IsPathEdges G s t)

@[simp] theorem mem_pathCandidates (G : SimpleGraph V) (s t : V)
    (F : Finset (Sym2 V)) : F ∈ pathCandidates G s t ↔ IsPathEdges G s t F := by
  classical
  simp [pathCandidates]

theorem pathCandidates_nonempty (G : SimpleGraph V) {s t : V}
    (h : G.Reachable s t) : (pathCandidates G s t).Nonempty := by
  classical
  obtain ⟨p⟩ := h
  exact ⟨p.toPath.val.edges.toFinset, mem_pathCandidates _ _ _ _ |>.2
    ⟨p.toPath.val, p.toPath.property, rfl⟩⟩

end
```

## Arbitrary shortest-path selection

A valid selector must choose an actual minimum residual-cost path. This specification assumes no competitive bound. The canonical selector proves such selectors exist.

Source: [Graph/Paths.lean](OnlineSteinerForest/Graph/Paths.lean).

```lean
section
variable {V : Type*} [Fintype V] [DecidableEq V]

class PathSelection where
  choose : ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (c : Sym2 V → ℝ) (B : Finset (Sym2 V))
    (s t : V), G.Reachable s t → Finset (Sym2 V)
  spec : ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (c : Sym2 V → ℝ) (B : Finset (Sym2 V))
    (s t : V) (h : G.Reachable s t),
    IsPathEdges G s t (choose G c B s t h) ∧
      ∀ F, IsPathEdges G s t F → residualCost c B (choose G c B s t h) ≤ residualCost c B F

noncomputable instance (priority := 100) canonicalPathSelection : PathSelection where
  choose G c B s t h := Classical.choose ((pathCandidates G s t).exists_min_image
    (residualCost c B) (pathCandidates_nonempty G h))
  spec G c B s t h := by
    classical
    obtain ⟨hm, hmin⟩ := Classical.choose_spec ((pathCandidates G s t).exists_min_image
      (residualCost c B) (pathCandidates_nonempty G h))
    exact ⟨(mem_pathCandidates _ _ _ _).1 hm,
      fun F hF => hmin F ((mem_pathCandidates _ _ _ _).2 hF)⟩

variable [PathSelection]

end
```

## Selected path

The selected minimum path is supplied by the arbitrary selector.

Source: [Graph/Paths.lean](OnlineSteinerForest/Graph/Paths.lean).

```lean
section
variable {V : Type*} [Fintype V] [DecidableEq V] [PathSelection]

noncomputable def shortestPathEdges (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (B : Finset (Sym2 V)) (s t : V) (h : G.Reachable s t) : Finset (Sym2 V) :=
  PathSelection.choose G c B s t h

end
```

## Offline feasibility

A candidate must contain only input edges and connect every requested pair using ordinary graph reachability.

Source: [Graph/Feasibility.lean](OnlineSteinerForest/Graph/Feasibility.lean).

```lean
section
variable {V : Type*} [DecidableEq V]

def FeasibleEdges (G : SimpleGraph V) (requests : List (V × V))
    (F : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ F, e ∈ G.edgeSet) ∧
    ∀ q ∈ requests, (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).Reachable q.1 q.2

end
```

## Offline optimum

All feasible edge sets are searched. The helper theorems establish that this finite search is nonempty. The chosen minimum defines OPT independently of greedy.

Source: [Graph/Optimum.lean](OnlineSteinerForest/Graph/Optimum.lean).

```lean
section
variable {V : Type*} [Fintype V]

noncomputable def offlineCandidates (G : SimpleGraph V) (requests : List (V × V)) :
    Finset (Finset (Sym2 V)) := by
  classical
  exact Finset.univ.filter (FeasibleEdges G requests)

@[simp] theorem mem_offlineCandidates (G : SimpleGraph V) (requests : List (V × V))
    (F : Finset (Sym2 V)) :
    F ∈ offlineCandidates G requests ↔ FeasibleEdges G requests F := by
  classical
  simp [offlineCandidates]

theorem offlineCandidates_nonempty (G : SimpleGraph V) (requests : List (V × V))
    (h : ∀ q ∈ requests, G.Reachable q.1 q.2) :
    (offlineCandidates G requests).Nonempty := by
  classical
  refine ⟨G.edgeFinset, (mem_offlineCandidates _ _ _).2 ⟨?_, ?_⟩⟩
  · intro e he
    exact G.mem_edgeFinset.mp he
  · intro q hq
    simpa only [SimpleGraph.coe_edgeFinset, SimpleGraph.fromEdgeSet_edgeSet] using h q hq

noncomputable def optimalEdges (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (h : ∀ q ∈ requests, G.Reachable q.1 q.2) :
    Finset (Sym2 V) :=
  Classical.choose ((offlineCandidates G requests).exists_min_image
    (edgeCost c) (offlineCandidates_nonempty G requests h))

noncomputable def optimum (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (h : ∀ q ∈ requests, G.Reachable q.1 q.2) : ℝ :=
  edgeCost c (optimalEdges G c requests h)

end
```

## The online greedy algorithm

One step adds a minimum residual-cost path. The recursion processes requests in arrival order, starting with the empty purchased set. greedyCost sums the original costs of the final purchased edges.

Source: [Greedy/Algorithm.lean](OnlineSteinerForest/Greedy/Algorithm.lean).

```lean
section
variable [PathSelection] {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def greedyStep (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (B : Finset (Sym2 V)) (s t : V) (h : G.Reachable s t) : Finset (Sym2 V) :=
  B ∪ shortestPathEdges G c B s t h

noncomputable def greedy (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (initial : Finset (Sym2 V) := ∅) : Finset (Sym2 V) :=
  match requests with
  | [] => initial
  | q :: qs => greedy G c qs (fun r hr => feasible r (by simp [hr]))
      (greedyStep G c initial q.1 q.2 (feasible q (by simp)))

noncomputable def greedyCost (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) : ℝ :=
  edgeCost c (greedy G c requests feasible)

end
```

## Upper bound

Source: [`upper_bound`](OnlineSteinerForest/Main.lean).

```lean
theorem upper_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ selection : PathSelection.{0},
    letI : PathSelection.{0} := selection
    ∀ (n : ℕ) (G : SimpleGraph (Fin n))
      (c : Sym2 (Fin n) → ℝ) (requests : List (Fin n × Fin n))
      (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2),
      (∀ e ∈ G.edgeSet, 0 < c e) → 1 ≤ requests.length →
      greedyCost G c requests feasible ≤
        C * optimum G c requests feasible * Real.log (2 * requests.length) *
          Real.log (Real.log (4 * requests.length)) := by sorry
```

## Lower bound

Source: [`lower_bound`](OnlineSteinerForest/Main.lean).

```lean
theorem lower_bound :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ K : ℕ,
      ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (c : Sym2 (Fin n) → ℝ)
        (requests : List (Fin n × Fin n))
        (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2),
        (∀ e ∈ G.edgeSet, 0 < c e) ∧ max K 3 ≤ requests.length ∧
        0 < optimum G c requests feasible ∧
        ∀ selection : PathSelection.{0},
          letI : PathSelection.{0} := selection
          c₀ * optimum G c requests feasible * Real.log requests.length *
            Real.log (Real.log requests.length) ≤ greedyCost G c requests feasible := by sorry
```

```lean
end OnlineSteinerForest
```
