import OnlineSteinerForest.LowerBound.Trace.GroupedData

/-! Run lengths/directions and shortcut destinations determine the boundary tuple. -/
namespace OnlineSteinerForest.LowerBound.Trace

variable {n : ℕ}

def lineEnd (u : Fin n) (d : ℕ × Bool) : Option (Fin n) :=
  if d.2 then
    if h : d.1 ≤ u.val then some ⟨u.val - d.1, lt_of_le_of_lt (Nat.sub_le _ _) u.isLt⟩ else none
  else
    if h : u.val + d.1 < n then some ⟨u.val + d.1, h⟩ else none

theorem lineEnd_data {m : ℕ} {u v : Fin (2 * m)}
    (w : (SimpleGraph.pathGraph (2 * m)).Walk u v) (hw : w.IsPath) :
    lineEnd u (lineData w) = some v := by
  have hdir := line_path_direction w hw
  by_cases hdown : v.val < u.val
  · have hle : w.length ≤ u.val := by rcases hdir with hdir | hdir <;> omega
    have hval : u.val - w.length = v.val := by rcases hdir with hdir | hdir <;> omega
    simp [lineEnd, lineData, hdown, hle, Fin.ext_iff, hval]
  · have hval : u.val + w.length = v.val := by rcases hdir with hdir | hdir <;> omega
    have hlt : u.val + w.length < 2 * m := by rw [hval]; exact v.isLt
    simp [lineEnd, lineData, hdown, hlt, Fin.ext_iff, hval]

/-- Partial reconstruction, with exactly one possible output for each shape. -/
def reconstruct (u : Fin n) : List (ℕ × Bool) → List (Fin n) → Option (List (Fin n))
  | [d], [] => do
    let v ← lineEnd u d
    pure [u, v]
  | d :: ds, b :: bs => do
    let a ← lineEnd u d
    let rest ← reconstruct b ds bs
    pure (u :: a :: rest)
  | _, _ => none

namespace Grouped

variable {m : ℕ} {σ : Equiv.Perm (Fin (2 * m))} {R : Finset (Fin m)}
variable {u v : Fin (2 * m)}

theorem reconstruct_correct (p : Grouped σ R u v) (hp : p.RunsSimple) :
    reconstruct u p.runData p.destinations = some p.boundaries := by
  induction p with
  | last w => simp [runData, destinations, boundaries, reconstruct, lineEnd_data w hp]
  | next w i hi ho tail ih =>
    simp [runData, destinations, boundaries, reconstruct, lineEnd_data w hp.1, ih hp.2]

end Grouped
end OnlineSteinerForest.LowerBound.Trace
