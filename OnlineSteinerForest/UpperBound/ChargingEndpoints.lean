import OnlineSteinerForest.UpperBound.ChargingEdges
import OnlineSteinerForest.UpperBound.GirthEndpointGraph

/-! The physical labelled edges represent exactly the actual simple charging graph. -/
namespace OnlineSteinerForest.UpperBound.Charging

open scoped Classical
variable {W J : Type*} [Fintype W] [Fintype J] [DecidableEq W] [DecidableEq J]

theorem physical_exhaustive (H : SimpleGraph W) (left right : J → W) {x y : W ⊕ J}
    (hxy : (graph H left right).Adj x y) : ∃ e : PhysicalEdge H J, physical H left right e = s(x, y) := by
  cases x with
  | inl u =>
    cases y with
    | inl v => exact ⟨.inl ⟨s(u, v), H.mem_edgeFinset.mpr hxy⟩, rfl⟩
    | inr j =>
      rcases hxy with h | h
      · exact ⟨.inr (j, false), by simp [physical, first, h]⟩
      · exact ⟨.inr (j, true), by simp [physical, middle, h, Sym2.eq_swap]⟩
  | inr j =>
    cases y with
    | inl v =>
      rcases hxy with h | h
      · exact ⟨.inr (j, false), by simp [physical, first, h, Sym2.eq_swap]⟩
      · exact ⟨.inr (j, true), by simp [physical, middle, h]⟩
    | inr k => exact hxy.elim

theorem endpoint_reachable_of_adj (H : SimpleGraph W) (left right : J → W) {x y : W ⊕ J}
    (hxy : (graph H left right).Adj x y) :
    (Girth.endpointGraph (physicalLeft H left right) (physicalRight H left right)).Reachable x y := by
  obtain ⟨e, he⟩ := physical_exhaustive H left right hxy
  have hp := (physical_pair H left right e).trans he
  rcases Sym2.eq_iff.mp hp with ⟨hx, hy⟩ | ⟨hy, hx⟩
  · have hr := Girth.dart_endpoint_reachable (physicalLeft H left right) (physicalRight H left right) (e, false)
    simpa only [Girth.tail, Girth.head, Bool.false_eq_true, ↓reduceIte, hx, hy] using hr
  · have hr := Girth.dart_endpoint_reachable (physicalLeft H left right) (physicalRight H left right) (e, true)
    simpa only [Girth.tail, Girth.head, ↓reduceIte, hx, hy] using hr

theorem graph_reachable_of_endpoint_adj (H : SimpleGraph W) (left right : J → W) {x y : W ⊕ J}
    (hxy : (Girth.endpointGraph (physicalLeft H left right) (physicalRight H left right)).Adj x y) :
    (graph H left right).Reachable x y := by
  obtain ⟨_, ⟨e, b⟩, hx, hy⟩ := hxy
  have hr := (physical_adjacent H left right e).reachable
  cases b
  · simpa only [Girth.tail, Girth.head, Bool.false_eq_true, ↓reduceIte] using hx ▸ hy ▸ hr
  · simpa only [Girth.tail, Girth.head, ↓reduceIte] using hx ▸ hy ▸ hr.symm

noncomputable def endpointComponentEquiv (H : SimpleGraph W) (left right : J → W) :
    (Girth.endpointGraph (physicalLeft H left right) (physicalRight H left right)).ConnectedComponent ≃
      (graph H left right).ConnectedComponent :=
  Girth.componentEquivOfRetractions id id
    (fun _ _ h => graph_reachable_of_endpoint_adj H left right h)
    (fun _ _ h => endpoint_reachable_of_adj H left right h) (fun _ => .refl _) (fun _ => .refl _)

end OnlineSteinerForest.UpperBound.Charging
