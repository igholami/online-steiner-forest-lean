import OnlineSteinerForest.UpperBound.GirthConnectedRank
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! Connected endpoint graphs have at least one fewer edge label than vertices. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*} [Fintype V] [Fintype I] [DecidableEq I] [DecidableEq V]

theorem endpoint_edge_card_le (left right : I → V) :
    Nat.card (endpointGraph left right).edgeSet ≤ Fintype.card I := by
  classical
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
  calc
    _ ≤ (Finset.univ.image (fun i : I => s(left i, right i))).card := by
      apply Finset.card_le_card
      intro edge he
      induction edge using Sym2.inductionOn with
      | _ u v =>
        have hadj : (endpointGraph left right).Adj u v := by simpa using he
        obtain ⟨_, ⟨i, b⟩, ht, hh⟩ := hadj
        apply Finset.mem_image.mpr
        refine ⟨i, Finset.mem_univ _, ?_⟩
        cases b
        · simpa [tail, head] using congrArg₂ (fun x y : V => s(x, y)) ht hh
        · simpa [tail, head, Sym2.eq_swap] using congrArg₂ (fun x y : V => s(x, y)) hh ht
    _ ≤ Fintype.card I := Finset.card_image_le.trans (by simp)

theorem connected_vertex_card_le_edges_add_one (left right : I → V)
    (hc : (endpointGraph left right).Connected) : Fintype.card V ≤ Fintype.card I + 1 := by
  have hh := hc.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card] at hh
  exact hh.trans (Nat.add_le_add_right (endpoint_edge_card_le left right) 1)

theorem connected_rank_identity (left right : I → V)
    (hc : (endpointGraph left right).Connected) :
    cycleRank left right + Fintype.card V = Fintype.card I + 1 := by
  have hh := connected_vertex_card_le_edges_add_one left right hc
  rw [connected_cycleRank_eq left right hc]
  omega

end OnlineSteinerForest.UpperBound.Girth
