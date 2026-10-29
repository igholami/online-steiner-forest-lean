import OnlineSteinerForest.LowerBound.Trace.GroupedSimple
import OnlineSteinerForest.LowerBound.Trace.BoundaryVertices

/-! Forget walks to positive run lengths, direction bits, and shortcut destinations. -/
namespace OnlineSteinerForest.LowerBound.Trace

variable {m : ℕ} {σ : Equiv.Perm (Fin (2 * m))} {R : Finset (Fin m)}

def lineData {u v : Fin (2 * m)} (w : (SimpleGraph.pathGraph (2 * m)).Walk u v) : ℕ × Bool :=
  (w.length, decide (v.val < u.val))

namespace Route

theorem shortcutVertices_prependRun {u a v : Fin (2 * m)}
    (w : (SimpleGraph.pathGraph (2 * m)).Walk u a) (p : Route σ R a v) :
    (prependRun w p).shortcutVertices = p.shortcutVertices := by
  induction w <;> simp [prependRun, shortcutVertices, *]

end Route

namespace Grouped

variable {u v : Fin (2 * m)}

def runData : {u v : Fin (2 * m)} → Grouped σ R u v → List (ℕ × Bool)
  | _, _, .last w => [lineData w]
  | _, _, .next w _ _ _ tail => lineData w :: tail.runData

def destinations : {u v : Fin (2 * m)} → Grouped σ R u v → List (Fin (2 * m))
  | _, _, .last _ => []
  | _, _, .next (b := b) _ _ _ _ tail => b :: tail.destinations

def boundaries : {u v : Fin (2 * m)} → Grouped σ R u v → List (Fin (2 * m))
  | a, b, .last _ => [a, b]
  | a, _, .next (a := c) _ _ _ _ tail => a :: c :: tail.boundaries

theorem runData_fst (p : Grouped σ R u v) : p.runData.map Prod.fst = p.lengths := by
  induction p <;> simp [runData, lengths, lineData, *]

theorem runData_length (p : Grouped σ R u v) : p.runData.length = p.ranks.length + 1 := by
  simpa only [List.length_map, lengths_length] using congrArg List.length p.runData_fst

theorem destinations_length (p : Grouped σ R u v) : p.destinations.length = p.ranks.length := by
  induction p <;> simp [destinations, ranks, *]

theorem runData_positive (p : Grouped σ R u v) (hp : p.RunsPositive) :
    ∀ d ∈ p.runData, 0 < d.1 := by
  induction p with
  | last w =>
    intro d hd
    have he : d = lineData w := List.mem_singleton.mp hd
    subst d
    exact hp
  | next w i hi ho tail ih =>
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact hp.1
    · exact ih hp.2 d hd

theorem boundaries_toRoute (p : Grouped σ R u v) : p.toRoute.boundaries = p.boundaries := by
  induction p with
  | last w => simp [toRoute, Route.boundaries, Route.shortcutVertices_prependRun,
      Route.shortcutVertices, boundaries]
  | @next u a b v w i hi ho tail ih =>
    simpa only [toRoute, Route.boundaries, Route.shortcutVertices_prependRun,
      Route.shortcutVertices, List.cons_append, boundaries] using
      congrArg (fun xs => u :: a :: xs) ih

end Grouped
end OnlineSteinerForest.LowerBound.Trace
