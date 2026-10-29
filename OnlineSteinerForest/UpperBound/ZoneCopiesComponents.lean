import OnlineSteinerForest.UpperBound.ZoneCopiesGraph
import Mathlib.SetTheory.Cardinal.Finite

/-! Every connected copied zone is exactly one reference component. -/
namespace OnlineSteinerForest.UpperBound

open scoped Classical
variable {Z : Type*} {A : Z → Type*}

noncomputable def zoneCopyComponentEquiv (T : ∀ z, SimpleGraph (A z)) (hT : ∀ z, (T z).Connected) :
    Z ≃ (zoneCopyGraph T).ConnectedComponent := by
  let root : ∀ z, A z := fun z => Classical.choice (hT z).nonempty
  let f : Z → (zoneCopyGraph T).ConnectedComponent := fun z =>
    (zoneCopyGraph T).connectedComponentMk ⟨z, root z⟩
  apply Equiv.ofBijective f
  constructor
  · intro z w hzw
    obtain ⟨p⟩ := SimpleGraph.ConnectedComponent.exact hzw
    have hconst : ∀ x y, (zoneCopyGraph T).Adj x y → x.1 = y.1 := by
      rintro x y ⟨k, u, v, huv, rfl, rfl⟩
      rfl
    have he := walk_support_fiber Sigma.fst hconst p _ p.end_mem_support
    exact he.symm
  · intro C
    induction C using SimpleGraph.ConnectedComponent.ind with
    | h x =>
      rcases x with ⟨z, a⟩
      refine ⟨z, ?_⟩
      exact SimpleGraph.ConnectedComponent.sound (((hT z) (root z) a).map (zoneCopyInclusion T z).toHom)

theorem zoneCopy_component_count (T : ∀ z, SimpleGraph (A z)) (hT : ∀ z, (T z).Connected) :
    Nat.card (zoneCopyGraph T).ConnectedComponent = Nat.card Z :=
  Nat.card_congr (zoneCopyComponentEquiv T hT).symm

end OnlineSteinerForest.UpperBound
