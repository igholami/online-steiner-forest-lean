import OnlineSteinerForest.UpperBound.ZonesTerminalTree
import OnlineSteinerForest.UpperBound.ZonesHubDegree

/-! Constructing the minimal terminal trees used in each boundary-hub component. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical BigOperators

/-- In any finite connected graph, an actual terminal-spanning subtree can be
chosen with no nonterminal leaves and at most twice the terminal incidences. -/
theorem exists_terminal_subtree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.Connected) (terminals : Finset V)
    (hne : terminals.Nonempty) :
    ∃ (S : Finset V) (T : SimpleGraph (S : Set V)), terminals ⊆ S ∧
      T ≤ G.induce (S : Set V) ∧ T.IsTree ∧
      (∑ v ∈ Finset.univ.filter (fun v : (S : Set V) => v.val ∈ terminals), T.degree v) + 2 ≤
        2 * terminals.card := by
  classical
  obtain ⟨F, hFG, hF⟩ := hG.exists_isTree_le
  obtain ⟨S, hTS, hS, hdeg⟩ := exists_terminal_tree F hF terminals hne
  let required : Finset (S : Set V) := Finset.univ.filter fun v => v.val ∈ terminals
  have hrequired : required.card = terminals.card := by
    apply Finset.card_bij (fun v _ => v.val)
    · intro v hv
      exact (Finset.mem_filter.mp hv).2
    · intro a _ b _ hab
      exact Subtype.ext hab
    · intro v hv
      exact ⟨⟨v, hTS hv⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩
  refine ⟨S, F.induce (S : Set V), hTS, ?_, hS, ?_⟩
  · intro u v huv
    exact hFG huv
  · have hb := terminal_degree_sum_bound (F.induce (S : Set V)) hS required ?_
    · simp only [← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] at hb ⊢
      simpa only [hrequired, required] using hb
    · intro v hv
      apply hdeg v
      simpa only [required, Finset.mem_filter, Finset.mem_univ, true_and] using hv

end OnlineSteinerForest.UpperBound
