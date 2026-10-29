import OnlineSteinerForest.LowerBound.Probability.RouteTuple
import OnlineSteinerForest.LowerBound.Probability.RankWeights
import OnlineSteinerForest.LowerBound.Trace.Shape

/-! Finite data describing every weighted alternate-path pattern. -/
namespace OnlineSteinerForest.LowerBound.Probability

variable [OnlineSteinerForest.PathSelection]

open scoped Classical

/-- Lengths are encoded as `value + 1`; `q` is the number of shortcuts. -/
structure RawPattern (h : ℕ) (i : Fin (matchingSize h)) (q : ℕ) where
  start : Fin (2 * matchingSize h)
  destinations : Fin q → Fin (2 * matchingSize h)
  runs : Fin (q + 1) → (Fin (logSize h ^ 2) × Bool)
  ranks : Fin q ↪ {j : Fin (matchingSize h) // j ≠ i}
  flip : Fin q → Bool

noncomputable instance rawPatternFintype (h : ℕ) (i : Fin (matchingSize h)) (q : ℕ) :
    Fintype (RawPattern h i q) := by
  let A := Fin (2 * matchingSize h) × (Fin q → Fin (2 * matchingSize h)) ×
    (Fin (q + 1) → (Fin (logSize h ^ 2) × Bool)) ×
    (Fin q ↪ {j : Fin (matchingSize h) // j ≠ i}) × (Fin q → Bool)
  exact Fintype.ofEquiv A
    { toFun := fun x => ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2⟩
      invFun := fun p => (p.start, p.destinations, p.runs, p.ranks, p.flip)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

namespace RawPattern

variable {h : ℕ} {i : Fin (matchingSize h)} {q : ℕ}

def runData (p : RawPattern h i q) : List (ℕ × Bool) :=
  List.ofFn (fun j => ((p.runs j).1.val + 1, (p.runs j).2))

def boundaryList (p : RawPattern h i q) : List (Fin (2 * matchingSize h)) :=
  (Trace.reconstruct p.start p.runData (List.ofFn p.destinations)).getD []

def Valid (p : RawPattern h i q) : Prop :=
  p.boundaryList.length = 2 * q + 2 ∧ p.boundaryList.Nodup

def imageTuple (p : RawPattern h i q) (hp : p.Valid) :
    Fin (2 * q + 2) ↪ Fin (2 * matchingSize h) where
  toFun k := p.boundaryList.get ⟨k.val, by simpa only [hp.1] using k.isLt⟩
  inj' a b hab := by
    have hinj := List.nodup_iff_injective_get.mp hp.2
    exact Fin.ext (congrArg (fun k : Fin p.boundaryList.length => k.val) (hinj hab))

/-- This weight is at least one for the actual short route that witnesses badness. -/
noncomputable def weight (p : RawPattern h i q) : ℝ :=
  Real.exp (16 * rankFraction h i * rankPrice h i) *
    (∏ j : Fin (q + 1), Real.exp (-(16 * rankFraction h i) *
      (((p.runs j).1.val + 1 : ℕ) : ℝ))) *
    ∏ j : Fin q, shortcutWeight h i (p.ranks j).val

theorem weight_nonneg (p : RawPattern h i q) : 0 ≤ p.weight := by
  unfold weight shortcutWeight
  positivity

end RawPattern

/-- The entire finite covering family; invalid or repeated-vertex shapes are omitted. -/
abbrev Pattern (h : ℕ) (i : Fin (matchingSize h)) :=
  Σ q : Fin (logSize h ^ 2), {p : RawPattern h i q.val // p.Valid}

end OnlineSteinerForest.LowerBound.Probability
