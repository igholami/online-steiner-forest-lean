import OnlineSteinerForest.UpperBound.GirthSubdivision
import OnlineSteinerForest.UpperBound.GirthCycleCost

/-! Cost transport places each original edge weight on its middle subdivided edge. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*} [DecidableEq I]

noncomputable def subdivisionCost (w : I → ℝ) : Sym2 (V ⊕ Dart I) → ℝ :=
  Sym2.lift ⟨fun a b => match a, b with
    | .inr d, .inr e => if d.1 = e.1 then w d.1 else 0
    | _, _ => 0, by
      intro a b
      cases a with
      | inl v => cases b <;> rfl
      | inr d =>
        cases b with
        | inl v => rfl
        | inr e =>
          by_cases h : d.1 = e.1
          · simp [h]
          · simp [h, Ne.symm h]⟩

theorem subdivisionCost_nonneg (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (e : Sym2 (V ⊕ Dart I)) :
    0 ≤ subdivisionCost w e := by
  induction e using Sym2.inductionOn with
  | _ a b =>
    cases a <;> cases b <;> simp only [subdivisionCost, Sym2.lift_mk]
    all_goals first | positivity | split_ifs <;> first | positivity | exact hw _

theorem dartWalk_cost (left right : I → V) (w : I → ℝ) (d : Dart I) :
    ((dartWalk left right d).edges.map (subdivisionCost w)).sum = w d.1 := by
  rw [dartWalk_edges]
  simp [subdivisionCost, reverse]

variable [Fintype I] [DecidableEq V]

theorem subdividedWalk_cost (left right : I → V) (w : I → ℝ) (n : ℕ)
    (p : Paths (Dart I) n) (hp : Nonbacktracking left right n p) :
    ((subdividedWalk left right n p hp).edges.map (subdivisionCost w)).sum = walkCost w n p := by
  induction n with
  | zero => exact dartWalk_cost left right w p
  | succ n ih =>
    change (((subdividedWalk left right n p.1 hp.1).append
      ((dartWalk left right p.2).copy _ _)).edges.map (subdivisionCost w)).sum = _
    rw [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_copy, List.map_append,
      List.sum_append, ih, dartWalk_cost]
    rfl

end OnlineSteinerForest.UpperBound.Girth
