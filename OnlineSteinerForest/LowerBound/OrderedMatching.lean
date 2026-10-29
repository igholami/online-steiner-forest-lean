import Mathlib.Data.Fintype.EquivFin
import Lean.Elab.Tactic.Omega

/-! An ordered perfect matching is encoded by a permutation of paired indices.
Every ordered matching has such an encoding; orientations are immaterial. -/
namespace OnlineSteinerForest.LowerBound

/-- Original vertices plus one private subdivision vertex per rank. -/
abbrev Vertex (m : ℕ) := Fin (2 * m) ⊕ Fin m

/-- Left endpoint of the matching edge of rank `i + 1`. -/
def leftEndpoint {m : ℕ} (σ : Equiv.Perm (Fin (2 * m))) (i : Fin m) : Fin (2 * m) :=
  σ ⟨2 * i.val, by omega⟩

/-- Right endpoint of the matching edge of rank `i + 1`. -/
def rightEndpoint {m : ℕ} (σ : Equiv.Perm (Fin (2 * m))) (i : Fin m) : Fin (2 * m) :=
  σ ⟨2 * i.val + 1, by omega⟩

theorem endpoints_ne {m : ℕ} (σ : Equiv.Perm (Fin (2 * m))) (i : Fin m) :
    leftEndpoint σ i ≠ rightEndpoint σ i := by
  intro heq
  unfold leftEndpoint rightEndpoint at heq
  have h := congrArg Fin.val (σ.injective heq)
  change 2 * i.val = 2 * i.val + 1 at h
  omega

end OnlineSteinerForest.LowerBound
