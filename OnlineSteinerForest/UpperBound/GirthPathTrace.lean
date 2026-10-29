import OnlineSteinerForest.UpperBound.GirthLabelledWalks
import OnlineSteinerForest.UpperBound.GirthTrace

/-! The stationary fixed-length paths supply arbitrary-length labelled trace witnesses. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*} [Fintype I] [DecidableEq I] [DecidableEq V]

theorem dartTrace_valid (left right : I → V) (n : ℕ) (p : Paths (Dart I) n)
    (hp : Nonbacktracking left right n p) :
    TraceValid left right (tail left right (first n p)) (head left right (last n p)) (dartTrace n p) := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    exact traceValid_append left right (ih p.1 hp.1) ⟨next_tail_eq left right hp.2, rfl⟩

theorem dartTrace_getLast (n : ℕ) (p : Paths (Dart I) n) :
    (dartTrace n p).getLast? = some (last n p) := by
  cases n <;> simp [dartTrace, last]

theorem dartTrace_nonbacktracking (left right : I → V) (n : ℕ) (p : Paths (Dart I) n)
    (hp : Nonbacktracking left right n p) : TraceNonbacktracking (dartTrace n p) := by
  induction n with
  | zero => simp [dartTrace, TraceNonbacktracking]
  | succ n ih =>
    apply (ih p.1 hp.1).append (List.IsChain.singleton p.2)
    intro a ha b hb
    rw [dartTrace_getLast] at ha
    simp only [Option.mem_def, Option.some.injEq] at ha
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
    subst a
    subst b
    exact (Finset.mem_erase.mp hp.2).1

theorem dartTrace_cost (w : I → ℝ) (n : ℕ) (p : Paths (Dart I) n) :
    traceCost w (dartTrace n p) = walkCost w n p := by
  induction n with
  | zero => simp [traceCost, dartTrace, walkCost, pathCost]
  | succ n ih =>
    change traceCost w (dartTrace n p.1 ++ [p.2]) = _
    simp only [traceCost, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [show ((dartTrace n p.1).map fun d => w d.1).sum = walkCost w n p.1 from ih p.1]
    rfl

end OnlineSteinerForest.UpperBound.Girth
