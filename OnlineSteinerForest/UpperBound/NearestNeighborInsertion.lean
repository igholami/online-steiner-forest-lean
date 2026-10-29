import OnlineSteinerForest.UpperBound.NearestNeighborPacking

/-! Exact nearest-earlier distances for a vertex sequence in a tree. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

variable {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}

/-- Original sequence index of the `(i+1)`st insertion after the initial point. -/
def newIndex (i : Fin n) : Fin (n + 1) := ⟨i.val + 1, by omega⟩

def previousIndex (i : Fin n) (j : Fin (i.val + 1)) : Fin (n + 1) := ⟨j.val, by omega⟩

noncomputable def nearestEarlier (G : SimpleGraph V) (c : Sym2 V → ℝ) (hconn : G.Preconnected)
    (x : Fin (n + 1) → V) (i : Fin n) : Fin (i.val + 1) :=
  Classical.choose ((Finset.univ : Finset (Fin (i.val + 1))).exists_min_image
    (fun j => residualDistance G c ∅ (x (newIndex i)) (x (previousIndex i j)) (hconn _ _))
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩)

noncomputable def insertionDistance (G : SimpleGraph V) (c : Sym2 V → ℝ) (hconn : G.Preconnected)
    (x : Fin (n + 1) → V) (i : Fin n) : ℝ :=
  residualDistance G c ∅ (x (newIndex i)) (x (previousIndex i (nearestEarlier G c hconn x i))) (hconn _ _)

theorem insertionDistance_le_earlier (G : SimpleGraph V) (c : Sym2 V → ℝ) (hconn : G.Preconnected)
    (x : Fin (n + 1) → V) (i : Fin n) (j : Fin (n + 1)) (hj : j.val ≤ i.val) :
    insertionDistance G c hconn x i ≤ residualDistance G c ∅ (x (newIndex i)) (x j) (hconn _ _) := by
  have hmin := (Classical.choose_spec ((Finset.univ : Finset (Fin (i.val + 1))).exists_min_image
    (fun j => residualDistance G c ∅ (x (newIndex i)) (x (previousIndex i j)) (hconn _ _))
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩)).2 ⟨j.val, by omega⟩ (Finset.mem_univ _)
  exact hmin

theorem insertionDistance_nonneg (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (hconn : G.Preconnected)
    (x : Fin (n + 1) → V) (i : Fin n) : 0 ≤ insertionDistance G c hconn x i :=
  residualDistance_nonneg G c hc ∅ _ _ _

theorem originalDistance_eq_zero_of_eq (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (hconn : G.Preconnected) (u v : V) (heq : u = v) :
    residualDistance G c ∅ u v (hconn _ _) = 0 := by
  subst v
  exact residualDistance_eq_zero_of_bought G c hc ∅ (by simp) u u (hconn _ _) (by simp)

end OnlineSteinerForest.UpperBound
