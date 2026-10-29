import OnlineSteinerForest.UpperBound.ZonesAttachments

/-! Selecting and simultaneously installing finitely many actual attachment paths. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical

/-- A finite collection of locally constructed attachment paths can be installed
at their summed budget, preserving every supplied skeleton connection. -/
theorem exists_attachment_union {V I : Type*} [DecidableEq V] [Fintype I]
    (G : SimpleGraph V) (c : Sym2 V → ℝ) (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e)
    (skeleton : Finset (Sym2 V)) (start finish : I → V) (budget : ℝ)
    (hlocal : ∀ i, ∃ P : Finset (Sym2 V), (∀ e ∈ P, e ∈ G.edgeSet) ∧
      edgeCost c P ≤ budget ∧
      (SimpleGraph.fromEdgeSet ((skeleton ∪ P : Finset (Sym2 V)) : Set (Sym2 V))).Reachable
        (start i) (finish i)) :
    ∃ A : Finset (Sym2 V), (∀ e ∈ A, e ∈ G.edgeSet) ∧
      edgeCost c A ≤ (Fintype.card I : ℝ) * budget ∧
      ∀ i, (SimpleGraph.fromEdgeSet ((skeleton ∪ A : Finset (Sym2 V)) : Set (Sym2 V))).Reachable
        (start i) (finish i) := by
  classical
  choose P hinput hcost hreach using hlocal
  let A := Finset.univ.biUnion P
  refine ⟨A, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp he
    exact hinput i e hi
  · simpa only [A, Finset.card_univ] using attachment_union_budget c Finset.univ P budget
      (fun i _ e he => hc e (hinput i e he)) (fun i _ => hcost i)
  · intro i
    apply (hreach i).mono
    intro u v huv
    refine ⟨?_, huv.2⟩
    rcases Finset.mem_union.mp huv.1 with hs | hp
    · exact Finset.mem_union_left _ hs
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hp⟩)

end OnlineSteinerForest.UpperBound
