import OnlineSteinerForest.Graph.ResidualMetric
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Original-cost walk lengths and the leaf excursion used to build tree tours. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- Original length counts edge occurrences, including repetitions in a tree tour. -/
noncomputable def walkCost (c : Sym2 V → ℝ) {s t : V} (p : G.Walk s t) : ℝ :=
  (p.edges.map c).sum

@[simp] theorem walkCost_nil (c : Sym2 V → ℝ) (s : V) :
    walkCost c (SimpleGraph.Walk.nil : G.Walk s s) = 0 := rfl

@[simp] theorem walkCost_cons (c : Sym2 V → ℝ) {s t u : V} (h : G.Adj s t) (p : G.Walk t u) :
    walkCost c (SimpleGraph.Walk.cons h p) = c s(s, t) + walkCost c p := rfl

@[simp] theorem walkCost_append (c : Sym2 V → ℝ) {s t u : V} (p : G.Walk s t) (q : G.Walk t u) :
    walkCost c (p.append q) = walkCost c p + walkCost c q := by
  simp [walkCost, SimpleGraph.Walk.edges_append, List.map_append]

@[simp] theorem walkCost_map (c : Sym2 W → ℝ) (f : G →g H) {s t : V} (p : G.Walk s t) :
    walkCost c (p.map f) = walkCost (fun e => c (Sym2.map f e)) p := by
  simp [walkCost, SimpleGraph.Walk.edges_map, List.map_map, Function.comp_def]

variable [DecidableEq V]

/-- Insert the excursion `u-v-u` at the first occurrence of `u`. -/
def leafExcursion {r u v : V} (p : G.Walk r r) (hu : u ∈ p.support) (h : G.Adj u v) : G.Walk r r :=
  (p.takeUntil u hu).append
    (h.toWalk.append (h.symm.toWalk.append (p.dropUntil u hu)))

@[simp] theorem walkCost_leafExcursion (c : Sym2 V → ℝ) {r u v : V}
    (p : G.Walk r r) (hu : u ∈ p.support) (h : G.Adj u v) :
    walkCost c (leafExcursion p hu h) = walkCost c p + 2 * c s(u, v) := by
  have hsplit := congrArg (walkCost c) (p.take_spec hu)
  rw [walkCost_append] at hsplit
  simp only [leafExcursion, walkCost_append, SimpleGraph.Adj.toWalk, walkCost_cons,
    walkCost_nil, add_zero]
  rw [Sym2.eq_swap (a := v) (b := u)]
  linarith

theorem mem_leafExcursion_support {r u v x : V}
    (p : G.Walk r r) (hu : u ∈ p.support) (h : G.Adj u v) (hx : x ∈ p.support) :
    x ∈ (leafExcursion p hu h).support := by
  have hs := congrArg (fun q : G.Walk r r => x ∈ q.support) (p.take_spec hu)
  rw [SimpleGraph.Walk.mem_support_append_iff] at hs
  rw [leafExcursion, SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.mem_support_append_iff]
  rcases hs.mpr hx with hx | hx
  · exact Or.inl hx
  · exact Or.inr (Or.inr (Or.inr hx))

theorem leaf_mem_leafExcursion_support {r u v : V}
    (p : G.Walk r r) (hu : u ∈ p.support) (h : G.Adj u v) :
    v ∈ (leafExcursion p hu h).support := by
  simp [leafExcursion, SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Adj.toWalk]

end OnlineSteinerForest.UpperBound
