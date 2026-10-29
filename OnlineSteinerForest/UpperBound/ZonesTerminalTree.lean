import OnlineSteinerForest.UpperBound.NearestNeighborTour

/-! Actual minimal terminal-spanning induced subtrees have no unrequired leaves. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical

/-- In a finite tree, discard unrequired leaves until every remaining leaf is
required. The result is an actual induced tree, not an assumed certificate. -/
theorem exists_terminal_tree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.IsTree) (terminals : Finset V)
    (hne : terminals.Nonempty) :
    ∃ S : Finset V, terminals ⊆ S ∧ (G.induce (S : Set V)).IsTree ∧
      ∀ v : (S : Set V), v.val ∉ terminals →
        2 ≤ (G.induce (S : Set V)).degree v := by
  classical
  have hex : ∃ n : ℕ, ∃ S : Finset V, terminals ⊆ S ∧
      (G.induce (S : Set V)).Connected ∧ S.card = n := by
    refine ⟨Fintype.card V, Finset.univ, Finset.subset_univ _, ?_, Finset.card_univ⟩
    rw [Finset.coe_univ]
    exact G.induceUnivIso.connected_iff.mpr hG.connected
  obtain ⟨S, hTS, hconn, hcard⟩ := Nat.find_spec hex
  refine ⟨S, hTS, ⟨hconn, hG.isAcyclic.induce _⟩, ?_⟩
  intro v hv
  by_contra hdeg
  obtain ⟨t, ht⟩ := hne
  let tS : (S : Set V) := ⟨t, hTS ht⟩
  have htv : v ≠ tS := by
    intro heq
    apply hv
    simpa only [heq] using ht
  have hpos := (hconn v tS).degree_pos_left htv
  have hone : (G.induce (S : Set V)).degree v = 1 := by omega
  let S' := S.erase v.val
  have hTS' : terminals ⊆ S' := by
    intro x hx
    exact Finset.mem_erase.mpr ⟨by intro h; exact hv (h ▸ hx), hTS hx⟩
  let H := G.induce (S : Set V)
  let f : H.induce ({v}ᶜ : Set (S : Set V)) →g G.induce (S' : Set V) :=
    { toFun := fun w => ⟨w.val.val, Finset.mem_erase.mpr
        ⟨by
          intro heq
          exact w.property (Subtype.ext heq), w.val.property⟩⟩
      map_rel' := fun {_ _} h => h }
  have hsurj : Function.Surjective f := by
    intro w
    have hw := Finset.mem_erase.mp w.property
    refine ⟨⟨⟨w.val, hw.2⟩, ?_⟩, rfl⟩
    intro heq
    exact hw.1 (congrArg Subtype.val heq)
  have hconn' : (G.induce (S' : Set V)).Connected :=
    SimpleGraph.Connected.map f hsurj
      (hconn.induce_compl_singleton_of_degree_eq_one hone)
  have hmin := Nat.find_min' hex ⟨S', hTS', hconn', rfl⟩
  have hlt : S'.card < S.card := Finset.card_erase_lt_of_mem v.property
  omega

end OnlineSteinerForest.UpperBound
