import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Summing required vertices across boundary-hub connected components. -/
namespace OnlineSteinerForest.UpperBound

open scoped Classical BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Required vertices regarded as vertices of one ordinary connected component. -/
noncomputable def componentTerminals (G : SimpleGraph V) (terminals : Finset V)
    (C : G.ConnectedComponent) : Finset C :=
  Finset.univ.filter fun v => v.val ∈ terminals

theorem componentTerminals_card (G : SimpleGraph V) (terminals : Finset V)
    (C : G.ConnectedComponent) :
    (componentTerminals G terminals C).card =
      (terminals.filter fun v => G.connectedComponentMk v = C).card := by
  apply Finset.card_bij (fun v _ => v.val)
  · intro v hv
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hv).2,
      (C.mem_supp_iff v.val).mp v.property⟩
  · intro a _ b _ hab
    exact Subtype.ext hab
  · intro v hv
    obtain ⟨hvT, hvC⟩ := Finset.mem_filter.mp hv
    exact ⟨⟨v, (C.mem_supp_iff v).mpr hvC⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvT⟩, rfl⟩

/-- No marked vertex is counted in two components. -/
theorem sum_componentTerminals (G : SimpleGraph V) (terminals : Finset V) :
    (∑ C ∈ terminals.image G.connectedComponentMk, (componentTerminals G terminals C).card) =
      terminals.card := by
  simp_rw [componentTerminals_card]
  exact (Finset.card_eq_sum_card_fiberwise
    (f := G.connectedComponentMk) (s := terminals)
    (t := terminals.image G.connectedComponentMk)
    (fun v hv => Finset.mem_image_of_mem _ hv)).symm

end OnlineSteinerForest.UpperBound
