import OnlineSteinerForest.LowerBound.Connectivity
import OnlineSteinerForest.LowerBound.Parameters
import OnlineSteinerForest.Graph.Residual

/-! Rank tests include ALL later matching edges, as required by Section 5.1.
Existence of a matching retaining half the total price remains to be proved. -/
namespace OnlineSteinerForest.LowerBound

variable [OnlineSteinerForest.PathSelection]

/-- Real-valued version of the exact rational rank prices. -/
noncomputable def rankPrice (h : ℕ) (i : Fin (matchingSize h)) : ℝ := price h (i.val + 1)

/-- Earlier auxiliary matching ranks are free; all later prices remain present. -/
noncomputable def testPrice (h : ℕ) (i j : Fin (matchingSize h)) : ℝ :=
  if j < i then 0 else rankPrice h j

/-- The rank being tested is removed; every other rank, including future ones, remains. -/
def testRanks (h : ℕ) (i : Fin (matchingSize h)) : Finset (Fin (matchingSize h)) :=
  Finset.univ.erase i

/-- A good positive rank has no alternate route of cost at most its own price. -/
noncomputable def GoodRank (h : ℕ)
    (σ : Equiv.Perm (Fin (2 * matchingSize h))) (i : Fin (matchingSize h)) : Prop :=
  rankPrice h i < residualDistance (constructionGraph σ (testRanks h i))
    (constructionCost (testPrice h i)) ∅
    (Sum.inl (leftEndpoint σ i)) (Sum.inl (rightEndpoint σ i))
    (base_reachable σ (testRanks h i) _ _)

/-- Actual input excludes all prefix ranks and all bad ranks. -/
noncomputable def retainedRanks (h : ℕ)
    (σ : Equiv.Perm (Fin (2 * matchingSize h))) : Finset (Fin (matchingSize h)) := by
  classical
  exact Finset.univ.filter (fun i => firstRank h ≤ i.val + 1 ∧ GoodRank h σ i)

/-- Sum of all positive auxiliary prices, before bad ranks are removed. -/
noncomputable def totalPrice (h : ℕ) : ℝ := ∑ i : Fin (matchingSize h), rankPrice h i

/-- The finite matching search must produce a permutation with this property. -/
noncomputable def RetainsHalf (h : ℕ)
    (σ : Equiv.Perm (Fin (2 * matchingSize h))) : Prop :=
  totalPrice h / 2 ≤ ∑ i ∈ retainedRanks h σ, rankPrice h i

end OnlineSteinerForest.LowerBound
