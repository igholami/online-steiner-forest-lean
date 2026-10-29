import OnlineSteinerForest.UpperBound.GirthCycleSupport
import OnlineSteinerForest.Graph.Cost
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Linarith

/-! A cycle extracted inside walk support costs no more than the supplying walks. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {A : Type*}

theorem sum_map_le_of_sublist (w : A → ℝ) (hw : ∀ a, 0 ≤ w a)
    {l₁ l₂ : List A} (h : l₁.Sublist l₂) : (l₁.map w).sum ≤ (l₂.map w).sum := by
  induction h with
  | slnil => simp
  | cons a h ih =>
    simp only [List.map_cons, List.sum_cons]
    linarith [hw a]
  | cons_cons a h ih =>
    simpa only [List.map_cons, List.sum_cons] using add_le_add (le_refl (w a)) ih

theorem nodup_sum_map_le_of_subset (w : A → ℝ) (hw : ∀ a, 0 ≤ w a)
    {l₁ l₂ : List A} (h₁ : l₁.Nodup) (hsub : l₁ ⊆ l₂) :
    (l₁.map w).sum ≤ (l₂.map w).sum := by
  obtain ⟨l, hperm, hsl⟩ := h₁.subperm hsub
  rw [← (hperm.map w).sum_eq]
  exact sum_map_le_of_sublist w hw hsl

variable {V : Type*} {G : SimpleGraph V}

theorem cycle_cost_in_two_walks {u v : V} (p q : G.Walk u v) (hne : p ≠ q)
    (hp : List.IsChain (· ≠ ·) p.edges) (hq : List.IsChain (· ≠ ·) q.edges)
    (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e) :
    ∃ z, ∃ c : G.Walk z z, c.IsCycle ∧
      (c.edges.map w).sum ≤ (p.edges.map w).sum + (q.edges.map w).sum := by
  obtain ⟨z, c, hc, hsupport⟩ := cycle_in_two_walks p q hne hp hq
  refine ⟨z, c, hc, ?_⟩
  have hh := nodup_sum_map_le_of_subset w hw hc.isTrail.edges_nodup
    (show c.edges ⊆ p.edges ++ q.edges by intro e he; exact List.mem_append.mpr (hsupport e he))
  simpa only [List.map_append, List.sum_append] using hh

end OnlineSteinerForest.UpperBound.Girth
