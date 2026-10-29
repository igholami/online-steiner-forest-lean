import OnlineSteinerForest.LowerBound.Trace.Support
import OnlineSteinerForest.LowerBound.Trace.LinePaths

/-! Group consecutive original-path steps into runs separated by matching traversals. -/
namespace OnlineSteinerForest.LowerBound.Trace

variable {m : ℕ} {σ : Equiv.Perm (Fin (2 * m))} {R : Finset (Fin m)}

namespace Route

def prependRun : {u a v : Fin (2 * m)} → (SimpleGraph.pathGraph (2 * m)).Walk u a →
    Route σ R a v → Route σ R u v
  | _, _, _, .nil, p => p
  | _, _, _, .cons h w, p => .base h (prependRun w p)

theorem realize_prependRun {u a v : Fin (2 * m)}
    (w : (SimpleGraph.pathGraph (2 * m)).Walk u a) (p : Route σ R a v) :
    (prependRun w p).realize = (w.map (comparisonHom σ R)).append p.realize := by
  induction w with
  | nil => rfl
  | cons h w ih =>
    change SimpleGraph.Walk.cons _ (prependRun w p).realize = SimpleGraph.Walk.cons _ _
    rw [ih] <;> rfl

theorem ranks_prependRun {u a v : Fin (2 * m)}
    (w : (SimpleGraph.pathGraph (2 * m)).Walk u a) (p : Route σ R a v) :
    (prependRun w p).ranks = p.ranks := by
  induction w <;> simp [prependRun, ranks, *]

theorem baseSteps_prependRun {u a v : Fin (2 * m)}
    (w : (SimpleGraph.pathGraph (2 * m)).Walk u a) (p : Route σ R a v) :
    (prependRun w p).baseSteps = w.length + p.baseSteps := by
  induction w <;> simp [prependRun, baseSteps, *] <;> omega

end Route

inductive Grouped (σ : Equiv.Perm (Fin (2 * m))) (R : Finset (Fin m)) :
    Fin (2 * m) → Fin (2 * m) → Type
  | last {u v} (run : (SimpleGraph.pathGraph (2 * m)).Walk u v) : Grouped σ R u v
  | next {u a b v} (run : (SimpleGraph.pathGraph (2 * m)).Walk u a)
      (i : Fin m) (hi : i ∈ R)
      (orientation : (a = leftEndpoint σ i ∧ b = rightEndpoint σ i) ∨
        (a = rightEndpoint σ i ∧ b = leftEndpoint σ i))
      (tail : Grouped σ R b v) : Grouped σ R u v

namespace Grouped

def toRoute : {u v : Fin (2 * m)} → Grouped σ R u v → Route σ R u v
  | _, v, .last w => Route.prependRun w (.nil v)
  | _, _, .next w i hi ho tail => Route.prependRun w (.shortcut i hi ho tail.toRoute)

def prependBase {u a v : Fin (2 * m)} (h : (SimpleGraph.pathGraph (2 * m)).Adj u a) :
    Grouped σ R a v → Grouped σ R u v
  | .last w => .last (.cons h w)
  | .next w i hi ho tail => .next (.cons h w) i hi ho tail

theorem toRoute_prependBase {u a v : Fin (2 * m)}
    (h : (SimpleGraph.pathGraph (2 * m)).Adj u a) (p : Grouped σ R a v) :
    (prependBase h p).toRoute = .base h p.toRoute := by cases p <;> rfl

def lengths : {u v : Fin (2 * m)} → Grouped σ R u v → List ℕ
  | _, _, .last w => [w.length]
  | _, _, .next w _ _ _ tail => w.length :: tail.lengths

def ranks : {u v : Fin (2 * m)} → Grouped σ R u v → List (Fin m)
  | _, _, .last _ => []
  | _, _, .next _ i _ _ tail => i :: tail.ranks

theorem ranks_toRoute {u v : Fin (2 * m)} (p : Grouped σ R u v) : p.toRoute.ranks = p.ranks := by
  induction p <;> simp [toRoute, Route.ranks_prependRun, Route.ranks, ranks, *]

theorem lengths_length {u v : Fin (2 * m)} (p : Grouped σ R u v) :
    p.lengths.length = p.ranks.length + 1 := by
  induction p <;> simp [lengths, ranks, *]

theorem sum_lengths {u v : Fin (2 * m)} (p : Grouped σ R u v) :
    p.lengths.sum = p.toRoute.baseSteps := by
  induction p <;> simp [lengths, toRoute, Route.baseSteps_prependRun, Route.baseSteps, *]

end Grouped

namespace Route

def group : {u v : Fin (2 * m)} → Route σ R u v → Grouped σ R u v
  | _, _, .nil _ => .last .nil
  | _, _, .base h p => Grouped.prependBase h p.group
  | _, _, .shortcut i hi ho p => .next .nil i hi ho p.group

theorem group_toRoute {u v : Fin (2 * m)} (p : Route σ R u v) : p.group.toRoute = p := by
  induction p with
  | nil => rfl
  | base h p ih => rw [group, Grouped.toRoute_prependBase, ih]
  | shortcut i hi ho p ih =>
    simpa only [group, Grouped.toRoute, prependRun] using congrArg (Route.shortcut i hi ho) ih

end Route
end OnlineSteinerForest.LowerBound.Trace
