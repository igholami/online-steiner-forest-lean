import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Lean.Elab.Tactic.Omega

/-! Counting boundary exits in a terminal-spanning tree, without suppressing vertices. -/
namespace OnlineSteinerForest.UpperBound

open scoped BigOperators

/-- A tree with no nonterminal leaves has fewer than twice as many terminal
incidences as terminals. This includes the single-vertex tree. -/
theorem terminal_degree_sum_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree)
    (terminals : Finset V) (hdegree : ∀ v ∉ terminals, 2 ≤ G.degree v) :
    (∑ v ∈ terminals, G.degree v) + 2 ≤ 2 * terminals.card := by
  classical
  have hsum := G.sum_degrees_eq_twice_card_edges
  have hcard := hG.card_edgeFinset
  have hsplit := Finset.sum_add_sum_compl terminals (fun v => G.degree v)
  have hlower : 2 * terminalsᶜ.card ≤ ∑ v ∈ terminalsᶜ, G.degree v := by
    calc
      2 * terminalsᶜ.card = ∑ _v ∈ terminalsᶜ, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ v ∈ terminalsᶜ, G.degree v := by
        apply Finset.sum_le_sum
        intro v hv
        exact hdegree v (Finset.mem_compl.mp hv)
  have hcompl := Finset.card_compl terminals
  have hsub := Finset.card_le_univ terminals
  omega

/-- Only hub incidences need attachments, so the same bound holds for any
subset of the required terminals. -/
theorem hub_degree_sum_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree)
    (hubs terminals : Finset V) (hsub : hubs ⊆ terminals)
    (hdegree : ∀ v ∉ terminals, 2 ≤ G.degree v) :
    (∑ v ∈ hubs, G.degree v) + 2 ≤ 2 * terminals.card := by
  have h := terminal_degree_sum_bound G hG terminals hdegree
  have hle := Finset.sum_le_sum_of_subset hsub (f := fun v => G.degree v)
  omega

end OnlineSteinerForest.UpperBound
