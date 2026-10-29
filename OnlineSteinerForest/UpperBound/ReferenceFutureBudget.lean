import OnlineSteinerForest.UpperBound.ReferenceFutureCount
import OnlineSteinerForest.UpperBound.ReferenceStride
import OnlineSteinerForest.UpperBound.GirthComponentAverage

/-! Convert the threshold inequality for actual future pairs into the mark budget. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem future_marks_scale_budget (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (r : Fin (batchClassCount requests.length)) (b : ℕ) (scale reference : ℝ)
    (hscale : 0 ≤ scale) (href : 0 ≤ reference)
    (hthreshold : ((futurePairs G c requests feasible r b).card : ℝ) *
      ((2 : ℝ) ^ batchClassCount requests.length * scale) ≤
        4 * cycleFactor (futurePairs G c requests feasible r b).card * reference) :
    ((futureMarks G c requests feasible r b).card : ℝ) * scale ≤
      8 * cycleFactor requests.length / (2 : ℝ) ^ batchClassCount requests.length * reference := by
  let q := (futurePairs G c requests feasible r b).card
  have hmarks := futureMarks_card_le G c requests feasible r b
  by_cases hq : q = 0
  · have hm : (futureMarks G c requests feasible r b).card = 0 := by
      change _ ≤ 2 * q at hmarks
      omega
    simp only [hm, Nat.cast_zero, zero_mul]
    positivity
  · have hqpos : 1 ≤ q := by omega
    have hqle : q ≤ requests.length := futurePairs_card_le G c requests feasible r b
    have hmono : (cycleFactor q : ℝ) ≤ cycleFactor requests.length :=
      Nat.cast_le.mpr (Girth.cycleFactor_mono hqpos hqle)
    have hth : (q : ℝ) * ((2 : ℝ) ^ batchClassCount requests.length * scale) ≤
        4 * cycleFactor requests.length * reference := by
      exact hthreshold.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmono (by norm_num)) href)
    have hp : 0 < (2 : ℝ) ^ batchClassCount requests.length := pow_pos (by norm_num) _
    have hqbudget : (q : ℝ) * scale ≤
        4 * cycleFactor requests.length * reference / (2 : ℝ) ^ batchClassCount requests.length := by
      apply (le_div_iff₀ hp).mpr
      nlinarith only [hth]
    have hmarks' : ((futureMarks G c requests feasible r b).card : ℝ) ≤ 2 * q := by
      exact_mod_cast hmarks
    calc
      _ ≤ 2 * ((q : ℝ) * scale) := by nlinarith [mul_le_mul_of_nonneg_right hmarks' hscale]
      _ ≤ 2 * (4 * cycleFactor requests.length * reference / (2 : ℝ) ^ batchClassCount requests.length) :=
        mul_le_mul_of_nonneg_left hqbudget (by norm_num)
      _ = _ := by ring

end OnlineSteinerForest.UpperBound
