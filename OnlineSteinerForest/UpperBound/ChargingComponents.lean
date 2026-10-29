import OnlineSteinerForest.UpperBound.ChargingGraph
import OnlineSteinerForest.UpperBound.GirthComponentRetractions

/-! Auxiliary pairs already connected in the base graph do not change its components. -/
namespace OnlineSteinerForest.UpperBound.Charging

variable {W J : Type*}

def projection (left : J → W) : W ⊕ J → W
  | .inl w => w
  | .inr j => left j

theorem projection_reachable (H : SimpleGraph W) (left right : J → W)
    (hpairs : ∀ j, H.Reachable (left j) (right j)) (x y : W ⊕ J)
    (hxy : (graph H left right).Adj x y) : H.Reachable (projection left x) (projection left y) := by
  cases x with
  | inl u =>
    cases y with
    | inl v =>
      change H.Adj u v at hxy
      exact hxy.reachable
    | inr j =>
      rcases hxy with h | h
      · simpa only [projection, h] using (SimpleGraph.Reachable.refl (left j) : H.Reachable _ _)
      · simpa only [projection, h] using (hpairs j).symm
  | inr j =>
    cases y with
    | inl v =>
      rcases hxy with h | h
      · simpa only [projection, h] using (SimpleGraph.Reachable.refl (left j) : H.Reachable _ _)
      · simpa only [projection, h] using hpairs j
    | inr k => exact hxy.elim

noncomputable def baseComponentEquiv (H : SimpleGraph W) (left right : J → W)
    (hpairs : ∀ j, H.Reachable (left j) (right j)) :
    (graph H left right).ConnectedComponent ≃ H.ConnectedComponent :=
  Girth.componentEquivOfRetractions (projection left) Sum.inl
    (projection_reachable H left right hpairs)
    (fun u v h => (show (graph H left right).Adj (Sum.inl u) (Sum.inl v) from h).reachable)
    (by
      intro x
      cases x with
      | inl w => exact .refl _
      | inr j => exact (show (graph H left right).Adj (.inl (left j)) (.inr j) from Or.inl rfl).reachable)
    (fun _ => .refl _)

theorem base_componentCount_le [Finite W] [Finite J] (H : SimpleGraph W) (left right : J → W) :
    Nat.card (graph H left right).ConnectedComponent ≤ Nat.card H.ConnectedComponent := by
  let f : H.ConnectedComponent → (graph H left right).ConnectedComponent :=
    Girth.componentMap Sum.inl (fun u v h =>
      (show (graph H left right).Adj (Sum.inl u) (Sum.inl v) from h).reachable)
  have hs : Function.Surjective f := by
    intro C
    induction C using SimpleGraph.ConnectedComponent.ind with
    | h x =>
      cases x with
      | inl w => exact ⟨H.connectedComponentMk w, rfl⟩
      | inr j =>
        refine ⟨H.connectedComponentMk (left j), ?_⟩
        exact SimpleGraph.ConnectedComponent.sound
          (show (graph H left right).Adj (Sum.inl (left j)) (Sum.inr j) from Or.inl rfl).reachable
  exact Nat.card_le_card_of_surjective f hs

end OnlineSteinerForest.UpperBound.Charging
