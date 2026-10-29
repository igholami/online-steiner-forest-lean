import Mathlib.Data.Rat.Floor
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Positivity

/-! Exact parameters of the deterministic lower-bound construction (Section 5.1). -/
namespace OnlineSteinerForest.LowerBound

/-- The manuscript's `L = 2^h`. -/
def logSize (h : ℕ) : ℕ := 2 ^ h

/-- The number of vertices of the unit-cost comparison path. -/
def vertexCount (h : ℕ) : ℕ := 2 ^ logSize h

/-- The number of ranks of an ordered perfect matching. -/
def matchingSize (h : ℕ) : ℕ := vertexCount h / 2

/-- Exact rational prefix fraction. -/
def prefixFraction (h : ℕ) : ℚ := 2 ^ 8 * h / logSize h

/-- First positive rank. Natural ceiling implements the manuscript's prescription. -/
def firstRank (h : ℕ) : ℕ := ⌈prefixFraction h * matchingSize h⌉₊

/-- Auxiliary prices; rank numbering starts at one. -/
def price (h i : ℕ) : ℚ :=
  if i < firstRank h then 0 else (logSize h : ℚ) * matchingSize h / (2 ^ 10 * i)

theorem vertexCount_pos (h : ℕ) : 0 < vertexCount h := by
  unfold vertexCount
  positivity

theorem logSize_pos (h : ℕ) : 0 < logSize h := by
  unfold logSize
  positivity

@[simp] theorem price_of_lt (h i : ℕ) (hi : i < firstRank h) : price h i = 0 := by
  simp [price, hi]

theorem price_of_ge (h i : ℕ) (hi : firstRank h ≤ i) :
    price h i = (logSize h : ℚ) * matchingSize h / (2 ^ 10 * i) := by
  simp [price, Nat.not_lt.mpr hi]

theorem price_nonneg (h i : ℕ) : 0 ≤ price h i := by
  unfold price
  split_ifs <;> positivity

end OnlineSteinerForest.LowerBound
