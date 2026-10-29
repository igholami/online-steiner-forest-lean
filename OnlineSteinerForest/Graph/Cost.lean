import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Edge costs and residual costs on a standard mathlib simple graph. -/
namespace OnlineSteinerForest

variable {V : Type*} [DecidableEq V]

/-- Original cost of a finite set of undirected edges. -/
def edgeCost (c : Sym2 V → ℝ) (F : Finset (Sym2 V)) : ℝ :=
  ∑ e ∈ F, c e

/-- Purchased edges have residual cost zero. -/
def residualCost (c : Sym2 V → ℝ) (B F : Finset (Sym2 V)) : ℝ :=
  ∑ e ∈ F \ B, c e

@[simp] theorem residualCost_empty (c : Sym2 V → ℝ) (F : Finset (Sym2 V)) :
    residualCost c ∅ F = edgeCost c F := by
  simp [residualCost, edgeCost]

@[simp] theorem residualCost_self (c : Sym2 V → ℝ) (B : Finset (Sym2 V)) :
    residualCost c B B = 0 := by
  simp [residualCost]

/-- Buying a path charges precisely its previously unpurchased edges. -/
theorem edgeCost_union (c : Sym2 V → ℝ) (B F : Finset (Sym2 V)) :
    edgeCost c (B ∪ F) = edgeCost c B + residualCost c B F := by
  have h : B ∪ F = B ∪ (F \ B) := by ext e; simp
  rw [h]
  exact Finset.sum_union (disjoint_sdiff_self_right)

end OnlineSteinerForest
