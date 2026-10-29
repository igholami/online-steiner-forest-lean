import OnlineSteinerForest.Graph.Cost
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Ring

/-! Elementary symmetric sums used in the sampling-without-replacement lemma. -/
namespace OnlineSteinerForest.LowerBound.Sampling

variable {ι : Type*}

/-- Sum of products over all `r`-element subsets of the population. -/
def elementary (s : Finset ι) (r : ℕ) (w : ι → ℝ) : ℝ :=
  ∑ t ∈ s.powersetCard r, ∏ i ∈ t, w i

@[simp] theorem elementary_zero (s : Finset ι) (w : ι → ℝ) :
    elementary s 0 w = 1 := by simp [elementary]

@[simp] theorem elementary_one (s : Finset ι) (w : ι → ℝ) :
    elementary s 1 w = ∑ i ∈ s, w i := by
  simp [elementary, Finset.powersetCard_one]

theorem elementary_congr (s : Finset ι) (r : ℕ) (w z : ι → ℝ)
    (h : ∀ i ∈ s, w i = z i) : elementary s r w = elementary s r z := by
  apply Finset.sum_congr rfl
  intro t ht
  exact Finset.prod_congr rfl (fun i hi => h i ((Finset.mem_powersetCard.mp ht).1 hi))

theorem elementary_nonneg (s : Finset ι) (r : ℕ) (w : ι → ℝ)
    (h : ∀ i ∈ s, 0 ≤ w i) : 0 ≤ elementary s r w := by
  apply Finset.sum_nonneg
  intro t ht
  exact Finset.prod_nonneg (fun i hi => h i ((Finset.mem_powersetCard.mp ht).1 hi))

theorem elementary_constant (s : Finset ι) (r : ℕ) (a : ℝ) :
    elementary s r (fun _ => a) = s.card.choose r * a ^ r := by
  unfold elementary
  calc
    _ = ∑ _t ∈ s.powersetCard r, a ^ r := by
      apply Finset.sum_congr rfl
      intro t ht
      simp only [Finset.prod_const, (Finset.mem_powersetCard.mp ht).2]
    _ = _ := by simp [nsmul_eq_mul]

variable [DecidableEq ι]

theorem elementary_insert_succ (s : Finset ι) (a : ι) (ha : a ∉ s)
    (r : ℕ) (w : ι → ℝ) :
    elementary (insert a s) (r + 1) w =
      elementary s (r + 1) w + w a * elementary s r w := by
  have hdis : Disjoint (s.powersetCard (r + 1)) ((s.powersetCard r).image (insert a)) := by
    apply Finset.disjoint_left.mpr
    intro t ht hu
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hu
    exact ha ((Finset.mem_powersetCard.mp ht).1 (Finset.mem_insert_self _ _))
  have hinj : Set.InjOn (insert a) (s.powersetCard r : Set (Finset ι)) := by
    intro u hu v hv heq
    have hau : a ∉ u := fun h => ha ((Finset.mem_powersetCard.mp hu).1 h)
    have hav : a ∉ v := fun h => ha ((Finset.mem_powersetCard.mp hv).1 h)
    simpa [hau, hav] using congrArg (fun t : Finset ι => t.erase a) heq
  unfold elementary
  rw [Finset.powersetCard_succ_insert ha r, Finset.sum_union hdis, Finset.sum_image hinj]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  exact Finset.prod_insert (fun h => ha ((Finset.mem_powersetCard.mp ht).1 h))

/-- Separating two coordinates gives the manuscript's `A + (x+y)B + xyC`. -/
theorem elementary_insert_pair (s : Finset ι) (a b : ι)
    (ha : a ∉ s) (hb : b ∉ s) (hab : a ≠ b) (r : ℕ) (w : ι → ℝ) :
    elementary (insert a (insert b s)) (r + 2) w =
      elementary s (r + 2) w + (w a + w b) * elementary s (r + 1) w +
        w a * w b * elementary s r w := by
  rw [elementary_insert_succ _ a (by simp [hab, ha]) (r + 1),
    elementary_insert_succ _ b hb (r + 1), elementary_insert_succ _ b hb r]
  ring

end OnlineSteinerForest.LowerBound.Sampling
