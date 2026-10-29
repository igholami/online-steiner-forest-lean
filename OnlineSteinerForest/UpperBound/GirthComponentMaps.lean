import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.SetTheory.Cardinal.Finite

/-! Component equivalences induced by replacing edges with connecting walks. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

theorem reachable_map_of_adj_reachable (f : V → W)
    (h : ∀ u v, G.Adj u v → H.Reachable (f u) (f v)) {u v : V} (huv : G.Reachable u v) :
    H.Reachable (f u) (f v) := by
  obtain ⟨p⟩ := huv
  induction p with
  | nil => exact .refl _
  | @cons a b c hab p ih => exact (h a b hab).trans ih

noncomputable def componentMap (f : V → W)
    (h : ∀ u v, G.Adj u v → H.Reachable (f u) (f v)) :
    G.ConnectedComponent → H.ConnectedComponent :=
  SimpleGraph.ConnectedComponent.lift (fun v => H.connectedComponentMk (f v))
    (by
      intro u v p _
      exact SimpleGraph.ConnectedComponent.sound
        (reachable_map_of_adj_reachable f h p.reachable))

@[simp] theorem componentMap_mk (f : V → W)
    (h : ∀ u v, G.Adj u v → H.Reachable (f u) (f v)) (v : V) :
    componentMap f h (G.connectedComponentMk v) = H.connectedComponentMk (f v) := rfl

noncomputable def componentEquivOfReachability (f : V → W) (hsurj : Function.Surjective f)
    (h : ∀ u v, G.Reachable u v ↔ H.Reachable (f u) (f v)) :
    G.ConnectedComponent ≃ H.ConnectedComponent :=
  Equiv.ofBijective (componentMap f (fun u v huv => (h u v).mp huv.reachable)) ⟨
    by
      intro C D heq
      induction C using SimpleGraph.ConnectedComponent.ind with
      | h u =>
        induction D using SimpleGraph.ConnectedComponent.ind with
        | h v =>
          apply SimpleGraph.ConnectedComponent.sound
          apply (h u v).mpr
          exact SimpleGraph.ConnectedComponent.exact heq,
    by
      intro C
      induction C using SimpleGraph.ConnectedComponent.ind with
      | h w =>
        obtain ⟨v, rfl⟩ := hsurj w
        exact ⟨G.connectedComponentMk v, rfl⟩⟩

theorem card_components_eq_of_reachability [Finite V] [Finite W] (f : V → W)
    (hsurj : Function.Surjective f) (h : ∀ u v, G.Reachable u v ↔ H.Reachable (f u) (f v)) :
    Nat.card G.ConnectedComponent = Nat.card H.ConnectedComponent :=
  Nat.card_congr (componentEquivOfReachability f hsurj h)

end OnlineSteinerForest.UpperBound.Girth
