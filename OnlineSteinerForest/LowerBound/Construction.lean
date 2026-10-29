import OnlineSteinerForest.LowerBound.OrderedMatching
import OnlineSteinerForest.Graph.Cost
import Mathlib.Combinatorics.SimpleGraph.Hasse

/-! The unit comparison path and privately subdivided matching edges of Section 5. -/
namespace OnlineSteinerForest.LowerBound

/-- Edges of the unit-cost path, on the original vertices only. -/
def comparisonEdges (m : ℕ) : Finset (Sym2 (Vertex m)) :=
  (Finset.univ.filter (fun p : Fin (2 * m) × Fin (2 * m) =>
    p.1.val + 1 = p.2.val ∨ p.2.val + 1 = p.1.val)).image
      (fun p => s(Sum.inl p.1, Sum.inl p.2))

/-- Two edges through rank `i`'s private subdivision vertex. -/
def matchingEdges {m : ℕ} (σ : Equiv.Perm (Fin (2 * m))) (i : Fin m) :
    Finset (Sym2 (Vertex m)) :=
  {s(Sum.inl (leftEndpoint σ i), Sum.inr i),
    s(Sum.inr i, Sum.inl (rightEndpoint σ i))}

/-- Keep the comparison path and exactly the specified matching ranks. -/
def constructionEdges {m : ℕ} (σ : Equiv.Perm (Fin (2 * m))) (R : Finset (Fin m)) :
    Finset (Sym2 (Vertex m)) := comparisonEdges m ∪ R.biUnion (matchingEdges σ)

/-- A standard mathlib simple graph; private vertices avoid parallel edges. -/
def constructionGraph {m : ℕ} (σ : Equiv.Perm (Fin (2 * m))) (R : Finset (Fin m)) :
    SimpleGraph (Vertex m) := SimpleGraph.fromEdgeSet (constructionEdges σ R : Set _)

private noncomputable def endpointCost {m : ℕ} (w : Fin m → ℝ) : Vertex m → Vertex m → ℝ
  | .inl _, .inl _ => 1
  | .inl _, .inr i => w i / 2
  | .inr i, .inl _ => w i / 2
  | .inr _, .inr _ => 0

/-- Original path edges cost one; each matching edge costs half its rank's price. -/
noncomputable def constructionCost {m : ℕ} (w : Fin m → ℝ) : Sym2 (Vertex m) → ℝ :=
  Sym2.lift ⟨endpointCost w, by intro u v; cases u <;> cases v <;> rfl⟩

@[simp] theorem constructionCost_base {m : ℕ} (w : Fin m → ℝ) (u v : Fin (2 * m)) :
    constructionCost w s(Sum.inl u, Sum.inl v) = 1 := rfl

@[simp] theorem constructionCost_left {m : ℕ} (w : Fin m → ℝ)
    (u : Fin (2 * m)) (i : Fin m) :
    constructionCost w s(Sum.inl u, Sum.inr i) = w i / 2 := rfl

@[simp] theorem constructionCost_right {m : ℕ} (w : Fin m → ℝ)
    (u : Fin (2 * m)) (i : Fin m) :
    constructionCost w s(Sum.inr i, Sum.inl u) = w i / 2 := rfl

@[simp] theorem constructionCost_private {m : ℕ} (w : Fin m → ℝ) (i j : Fin m) :
    constructionCost w s(Sum.inr i, Sum.inr j) = 0 := rfl

theorem constructionCost_pos {m : ℕ} (σ : Equiv.Perm (Fin (2 * m)))
    (R : Finset (Fin m)) (w : Fin m → ℝ) (hw : ∀ i ∈ R, 0 < w i) :
    ∀ e ∈ (constructionGraph σ R).edgeSet, 0 < constructionCost w e := by
  intro e he
  have he' : e ∈ constructionEdges σ R :=
    (show e ∈ (constructionEdges σ R : Set _) \ Sym2.diagSet by
      simpa only [constructionGraph, SimpleGraph.edgeSet_fromEdgeSet] using he).1
  rcases Finset.mem_union.mp he' with he' | he'
  · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp he'
    simp
  · obtain ⟨i, hi, he⟩ := Finset.mem_biUnion.mp he'
    simp only [matchingEdges, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl <;> simp <;> exact hw i hi

end OnlineSteinerForest.LowerBound
