import OnlineSteinerForest.UpperBound.ZonesStarAssignment
import OnlineSteinerForest.Graph.ContractionReachability

/-! Contracting the assigned center stars preserves the actual core connections. -/
namespace OnlineSteinerForest.UpperBound

open scoped Classical

variable {V : Type*} [DecidableEq V]

structure StarContraction (G : SimpleGraph V) (centers : Finset V) where
  assign : V → ↥centers
  fixes : ∀ v : ↥centers, assign v.val = v
  adjacent : ∀ v ∉ centers, G.Adj v (assign v).val

theorem exists_star_contraction (G : SimpleGraph V) (centers : Finset V)
    (hdom : ∀ v, v ∈ centers ∨ ∃ u ∈ centers, G.Adj v u) :
    Nonempty (StarContraction G centers) := by
  obtain ⟨f, hcenter, hfix, hadj⟩ := exists_star_assignment G centers hdom
  exact ⟨⟨fun v => ⟨f v, hcenter v⟩,
    fun v => Subtype.ext (hfix v.val v.property), hadj⟩⟩

namespace StarContraction

variable {G : SimpleGraph V} {centers : Finset V}

theorem assigned_reachable (s : StarContraction G centers) (v : V) :
    G.Reachable v (s.assign v).val := by
  by_cases hv : v ∈ centers
  · have h := congrArg Subtype.val (s.fixes ⟨v, hv⟩)
    rw [h]
  · exact (s.adjacent v hv).reachable

theorem quotient_reachable_iff (s : StarContraction G centers) (u v : V) :
    (G.map s.assign).Reachable (s.assign u) (s.assign v) ↔ G.Reachable u v :=
  contraction_reachable_iff G s.assign Subtype.val s.assigned_reachable u v

end StarContraction
end OnlineSteinerForest.UpperBound
