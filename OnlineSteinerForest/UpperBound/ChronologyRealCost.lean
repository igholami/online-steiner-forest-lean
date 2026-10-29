import OnlineSteinerForest.UpperBound.ChronologyMetricCycle

/-! Transporting finite nonnegative cycle costs between reals and extended nonnegative reals. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

variable {A : Type*}

theorem ofReal_list_sum_map (w : A → ℝ) (hw : ∀ a, 0 ≤ w a) (ds : List A) :
    ENNReal.ofReal ((ds.map w).sum) = (ds.map fun a => ENNReal.ofReal (w a)).sum := by
  induction ds with
  | nil => simp
  | cons a ds ih =>
    have hsum : 0 ≤ (ds.map w).sum := List.sum_nonneg (by
      intro x hx
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
      exact hw a)
    simp only [List.map_cons, List.sum_cons, ENNReal.ofReal_add (hw a) hsum, ih]

end OnlineSteinerForest.UpperBound
