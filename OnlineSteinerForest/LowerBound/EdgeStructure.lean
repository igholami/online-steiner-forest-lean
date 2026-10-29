import OnlineSteinerForest.LowerBound.Construction
import Mathlib.Tactic.Linarith

/-! Disjoint private matching routes and their exact original costs. -/
namespace OnlineSteinerForest.LowerBound

variable {m : ℕ} (σ : Equiv.Perm (Fin (2 * m)))

theorem matchingEdges_disjoint {i j : Fin m} (hij : i ≠ j) :
    Disjoint (matchingEdges σ i) (matchingEdges σ j) := by
  apply Finset.disjoint_left.mpr
  intro e hei hej
  simp only [matchingEdges, Finset.mem_insert, Finset.mem_singleton] at hei
  rcases hei with rfl | rfl <;>
    simp [matchingEdges, hij] at hej

theorem comparison_matching_disjoint (i : Fin m) :
    Disjoint (comparisonEdges m) (matchingEdges σ i) := by
  apply Finset.disjoint_left.mpr
  intro e he hm
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp he
  simp [matchingEdges] at hm

theorem matchingEdges_card (i : Fin m) : (matchingEdges σ i).card = 2 := by
  have hne : s(Sum.inl (leftEndpoint σ i), Sum.inr i) ≠
      s(Sum.inr i, Sum.inl (rightEndpoint σ i)) := by
    simp [endpoints_ne σ i]
  simp [matchingEdges, hne]

theorem matchingEdges_cost (w : Fin m → ℝ) (i : Fin m) :
    edgeCost (constructionCost w) (matchingEdges σ i) = w i := by
  have hne : s(Sum.inl (leftEndpoint σ i), Sum.inr i) ≠
      s(Sum.inr i, Sum.inl (rightEndpoint σ i)) := by
    simp [endpoints_ne σ i]
  simp [edgeCost, matchingEdges, hne]

theorem subdivision_adj (R : Finset (Fin m)) (i : Fin m) (z : Vertex m) :
    (constructionGraph σ R).Adj (Sum.inr i) z ↔
      i ∈ R ∧ (z = Sum.inl (leftEndpoint σ i) ∨ z = Sum.inl (rightEndpoint σ i)) := by
  cases z with
  | inl v =>
    simp [constructionGraph, constructionEdges, comparisonEdges, matchingEdges, eq_comm]
    aesop
  | inr j => simp [constructionGraph, constructionEdges, comparisonEdges, matchingEdges]

end OnlineSteinerForest.LowerBound
