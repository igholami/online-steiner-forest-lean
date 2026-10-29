import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Fin.Rev
import Lean.Elab.Tactic.Omega

/-! A simple path on the comparison line has one fixed direction. -/
namespace OnlineSteinerForest.LowerBound.Trace

variable {n : ℕ}

theorem first_up_endpoint {a b z : Fin n} (hab : (SimpleGraph.pathGraph n).Adj a b)
    (hup : a.val + 1 = b.val) (p : (SimpleGraph.pathGraph n).Walk b z)
    (hp : (SimpleGraph.Walk.cons hab p).IsPath) : z.val = a.val + p.length + 1 := by
  induction p generalizing a with
  | nil => simpa only [SimpleGraph.Walk.length_nil, Nat.add_zero] using hup.symm
  | @cons b c z hbc p ih =>
    have hca : c ≠ a := by
      intro heq
      have hmem : a ∈ p.support := heq ▸ p.start_mem_support
      exact (SimpleGraph.Walk.cons_isPath_iff hab _).mp hp |>.2
        (List.mem_cons_of_mem b hmem)
    have hbcup : b.val + 1 = c.val := by
      rcases SimpleGraph.pathGraph_adj.mp hbc with hh | hh
      · exact hh
      · have heq : c = a := Fin.ext (by omega)
        exact (hca heq).elim
    have hz := ih hbc hbcup hp.of_cons
    simp only [SimpleGraph.Walk.length_cons]
    omega

def reverseLineHom (n : ℕ) : SimpleGraph.pathGraph n →g SimpleGraph.pathGraph n where
  toFun := Fin.rev
  map_rel' := by
    intro u v huv
    rw [SimpleGraph.pathGraph_adj] at huv ⊢
    simp only [Fin.val_rev]
    rcases huv with huv | huv <;> omega

theorem first_down_endpoint {a b z : Fin n} (hab : (SimpleGraph.pathGraph n).Adj a b)
    (hdown : b.val + 1 = a.val) (p : (SimpleGraph.pathGraph n).Walk b z)
    (hp : (SimpleGraph.Walk.cons hab p).IsPath) : a.val = z.val + p.length + 1 := by
  let f := reverseLineHom n
  have hup : (f a).val + 1 = (f b).val := by
    change (Fin.rev a).val + 1 = (Fin.rev b).val
    simp only [Fin.val_rev]
    omega
  have hmap := hp.map (f := f) Fin.rev_injective
  rw [SimpleGraph.Walk.map_cons] at hmap
  have hz := first_up_endpoint (f.map_rel hab) hup (p.map f) hmap
  rw [SimpleGraph.Walk.length_map] at hz
  change (Fin.rev z).val = (Fin.rev a).val + p.length + 1 at hz
  simp only [Fin.val_rev] at hz
  omega

theorem line_path_direction {u v : Fin n} (p : (SimpleGraph.pathGraph n).Walk u v) (hp : p.IsPath) :
    v.val = u.val + p.length ∨ u.val = v.val + p.length := by
  cases p with
  | nil => simp
  | cons hab p =>
    rcases SimpleGraph.pathGraph_adj.mp hab with hup | hdown
    · left
      simpa only [SimpleGraph.Walk.length_cons, Nat.add_assoc] using first_up_endpoint hab hup p hp
    · right
      simpa only [SimpleGraph.Walk.length_cons, Nat.add_assoc] using first_down_endpoint hab hdown p hp

end OnlineSteinerForest.LowerBound.Trace
