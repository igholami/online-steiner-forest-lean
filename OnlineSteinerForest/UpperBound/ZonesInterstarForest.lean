import OnlineSteinerForest.UpperBound.ZonesStarContraction
import OnlineSteinerForest.UpperBound.ZonesForestCard

/-! An actual spanning forest across assigned stars, with original core-edge representatives. -/
namespace OnlineSteinerForest.UpperBound

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

structure InterstarForest {G : SimpleGraph V} {centers : Finset V}
    (stars : StarContraction G centers) where
  graph : SimpleGraph ↥centers
  subgraph : graph ≤ G.map stars.assign
  acyclic : graph.IsAcyclic
  reachable : graph.Reachable = (G.map stars.assign).Reachable
  left : ↥graph.edgeFinset → V
  right : ↥graph.edgeFinset → V
  adjacent : ∀ e, G.Adj (left e) (right e)
  projects : ∀ e, s(stars.assign (left e), stars.assign (right e)) = e.val

theorem exists_interstar_forest {G : SimpleGraph V} {centers : Finset V}
    (stars : StarContraction G centers) : Nonempty (InterstarForest stars) := by
  obtain ⟨T, hTQ, hT, hreach⟩ := (G.map stars.assign).exists_isAcyclic_reachable_eq_le
  have hex : ∀ e : ↥T.edgeFinset, ∃ u v : V,
      G.Adj u v ∧ s(stars.assign u, stars.assign v) = e.val := by
    intro ⟨e, he⟩
    induction e using Sym2.ind with
    | _ a b =>
      have hab := hTQ (SimpleGraph.mem_edgeFinset.mp he)
      obtain ⟨_, u, v, huv, hua, hvb⟩ := (SimpleGraph.map_adj' stars.assign G a b).mp hab
      exact ⟨u, v, huv, by rw [hua, hvb]⟩
  choose left right hadj hproject using hex
  exact ⟨⟨T, hTQ, hT, hreach, left, right, hadj, hproject⟩⟩

namespace InterstarForest

variable {G : SimpleGraph V} {centers : Finset V} {stars : StarContraction G centers}

theorem edge_count_le (f : InterstarForest stars) : f.graph.edgeFinset.card ≤ centers.card := by
  simpa only [Fintype.card_coe] using forest_edge_count_le f.graph f.acyclic

end InterstarForest
end OnlineSteinerForest.UpperBound
