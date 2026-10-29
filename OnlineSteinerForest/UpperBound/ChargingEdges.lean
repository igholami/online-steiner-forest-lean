import OnlineSteinerForest.UpperBound.ChargingGraph

/-! Every physical tree edge and both auxiliary spokes have distinct finite labels. -/
namespace OnlineSteinerForest.UpperBound.Charging

open scoped Classical
variable {W J : Type*} [Fintype W] [Fintype J] [DecidableEq W] [DecidableEq J]

abbrev PhysicalEdge (H : SimpleGraph W) (J : Type*) := ↥H.edgeFinset ⊕ (J × Bool)

def physical (H : SimpleGraph W) (left right : J → W) : PhysicalEdge H J → Sym2 (W ⊕ J)
  | .inl e => Sym2.map Sum.inl e.val
  | .inr (j, false) => first left j
  | .inr (j, true) => middle right j

noncomputable def physicalLeft (H : SimpleGraph W) (left right : J → W) (e : PhysicalEdge H J) : W ⊕ J :=
  (physical H left right e).out.1

noncomputable def physicalRight (H : SimpleGraph W) (left right : J → W) (e : PhysicalEdge H J) : W ⊕ J :=
  (physical H left right e).out.2

theorem physical_pair (H : SimpleGraph W) (left right : J → W) (e : PhysicalEdge H J) :
    s(physicalLeft H left right e, physicalRight H left right e) = physical H left right e :=
  Quot.out_eq _

theorem physical_mem (H : SimpleGraph W) (left right : J → W) (e : PhysicalEdge H J) :
    physical H left right e ∈ (graph H left right).edgeSet := by
  cases e with
  | inl e =>
    have hmap : ∀ e : Sym2 W, e ∈ H.edgeSet → Sym2.map (Sum.inl : W → W ⊕ J) e ∈
        (graph H left right).edgeSet := by
      intro e
      refine Sym2.ind (fun u v huv => ?_) e
      exact huv
    exact hmap e.val (H.mem_edgeFinset.mp e.property)
  | inr e =>
    rcases e with ⟨j, b⟩
    cases b
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem physical_adjacent (H : SimpleGraph W) (left right : J → W) (e : PhysicalEdge H J) :
    (graph H left right).Adj (physicalLeft H left right e) (physicalRight H left right e) := by
  have he := physical_mem H left right e
  rw [← physical_pair H left right e] at he
  exact he

theorem physical_reference_aux_ne (H : SimpleGraph W) (left right : J → W)
    (e : ↥H.edgeFinset) (j : J) (b : Bool) :
    physical H left right (.inl e) ≠ physical H left right (.inr (j, b)) := by
  have hgeneric : ∀ e : Sym2 W, Sym2.map (Sum.inl : W → W ⊕ J) e ≠
      physical H left right (.inr (j, b)) := by
    intro e
    refine Sym2.ind (fun u v => ?_) e
    cases b <;> simp [physical, first, middle, Sym2.eq_iff]
  exact hgeneric e.val

theorem physical_injective (H : SimpleGraph W) (left right : J → W) (hne : ∀ j, left j ≠ right j) :
    Function.Injective (physical H left right) := by
  intro e f hef
  cases e with
  | inl e =>
    cases f with
    | inl f => exact congrArg Sum.inl (Subtype.ext (Sym2.map.injective Sum.inl_injective hef))
    | inr f => exact False.elim (physical_reference_aux_ne H left right e f.1 f.2 hef)
  | inr e =>
    cases f with
    | inl f => exact False.elim (physical_reference_aux_ne H left right f e.1 e.2 hef.symm)
    | inr f =>
      rcases e with ⟨i, b⟩
      rcases f with ⟨j, d⟩
      cases b <;> cases d <;> simp [physical, first, middle, Sym2.eq_iff] at hef ⊢
      all_goals grind

end OnlineSteinerForest.UpperBound.Charging
