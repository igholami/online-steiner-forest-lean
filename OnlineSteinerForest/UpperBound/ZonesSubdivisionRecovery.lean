import OnlineSteinerForest.UpperBound.ZonesSubdivisionResidualPath

/-! Recover every entire mixed candidate to original edges, preserving all original connections. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]

theorem recover_mixed_candidate (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (E : Finset (Sym2 V))
    (hE : ∀ e ∈ E, e ∈ G.edgeSet) (F : Finset (Sym2 W)) (d : Sym2 W → ℝ)
    (cert : ZoneSubdivisionCertificate E c F d)
    (hsep : ∀ e : Sym2 V, Sym2.map cert.vertices e ∉ F)
    (C : Finset (Sym2 W)) (hC : ∀ e ∈ C, e ∈ (mixedSubdivisionGraph G cert.vertices F).edgeSet) :
    ∃ P : Finset (Sym2 V), (∀ e ∈ P, e ∈ G.edgeSet) ∧
      edgeCost c P ≤ edgeCost (mixedSubdivisionCost cert.vertices F d c) C ∧
      ∀ a b : V, (SimpleGraph.fromEdgeSet (C : Set (Sym2 W))).Reachable (cert.vertices a) (cert.vertices b) →
        (SimpleGraph.fromEdgeSet (P : Set (Sym2 V))).Reachable a b := by
  let H := C ∩ F
  let K := mixedOriginalPart G cert.vertices C
  have hHF : H ⊆ F := Finset.inter_subset_right
  have hparts : H ∪ K.image (Sym2.map cert.vertices) = C := mixed_path_split G cert.vertices F C hsep hC
  obtain ⟨Q, hQE, hcostQ, hreachQ⟩ := cert.recover_mixed H hHF K
  have hKinput : ∀ e ∈ K, e ∈ G.edgeSet := fun e he => G.mem_edgeFinset.mp (Finset.mem_filter.mp he).1
  refine ⟨Q ∪ K, ?_, ?_, ?_⟩
  · intro e he
    rcases Finset.mem_union.mp he with he | he
    · exact hE e (hQE he)
    · exact hKinput e he
  · have hcost : edgeCost (mixedSubdivisionCost cert.vertices F d c) C = edgeCost d H + edgeCost c K := by
      have hs := mixedSubdivision_residual_split cert.vertices F d c hsep ∅ K H hHF
      simp only [Finset.image_empty, residualCost_empty] at hs
      exact (congrArg (edgeCost (mixedSubdivisionCost cert.vertices F d c)) hparts).symm.trans hs
    rw [hcost, edgeCost_union]
    have hres : residualCost c Q K ≤ edgeCost c K :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun e he _ => hc e (hKinput e he))
    exact add_le_add hcostQ hres
  · intro a b hab
    apply hreachQ a b
    simpa only [hparts] using hab

end OnlineSteinerForest.UpperBound
