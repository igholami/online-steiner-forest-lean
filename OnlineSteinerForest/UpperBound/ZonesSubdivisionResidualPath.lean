import OnlineSteinerForest.UpperBound.ZonesSubdivisionResidualCost
import OnlineSteinerForest.UpperBound.ZonesSubdivisionPathSplit
import OnlineSteinerForest.UpperBound.ZonesSubdivisionMixed
import OnlineSteinerForest.Graph.ResidualMetric

/-! Recovering each mixed comparison path gives a sound original residual-cost bound. -/
namespace OnlineSteinerForest.UpperBound

universe uSelection
variable [OnlineSteinerForest.PathSelection.{uSelection}]

open scoped Classical
variable {V W : Type uSelection} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

theorem residualDistance_le_mixed_path (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (E : Finset (Sym2 V))
    (hE : ∀ e ∈ E, e ∈ G.edgeSet) (F : Finset (Sym2 W)) (d : Sym2 W → ℝ)
    (cert : ZoneSubdivisionCertificate E c F d)
    (hsep : ∀ e : Sym2 V, Sym2.map cert.vertices e ∉ F)
    (B : Finset (Sym2 V)) (a b : V) (hab : G.Reachable a b)
    (P : Finset (Sym2 W)) (hP : IsPathEdges (mixedSubdivisionGraph G cert.vertices F)
      (cert.vertices a) (cert.vertices b) P) :
    residualDistance G c B a b hab ≤
      residualCost (mixedSubdivisionCost cert.vertices F d c) (B.image (Sym2.map cert.vertices)) P := by
  let H := P ∩ F
  let K := mixedOriginalPart G cert.vertices P
  have hHF : H ⊆ F := Finset.inter_subset_right
  have hparts : H ∪ K.image (Sym2.map cert.vertices) = P :=
    mixed_path_split G cert.vertices F P hsep hP.subset_edgeSet
  obtain ⟨Q, hQE, hcostQ, hreachQ⟩ := cert.recover_mixed H hHF K
  have hRreach : (SimpleGraph.fromEdgeSet ((Q ∪ K : Finset (Sym2 V)) : Set (Sym2 V))).Reachable a b := by
    apply hreachQ a b
    simpa only [hparts] using hP.reachable
  have hKinput : ∀ e ∈ K, e ∈ G.edgeSet := fun e he =>
    G.mem_edgeFinset.mp (Finset.mem_filter.mp he).1
  have hRinput : ∀ e ∈ Q ∪ K, e ∈ G.edgeSet := by
    intro e he
    rcases Finset.mem_union.mp he with he | he
    · exact hE e (hQE he)
    · exact hKinput e he
  obtain ⟨L, hL, hLsub⟩ := exists_pathEdges_subset hRinput hRreach
  have hQres : residualCost c B Q ≤ edgeCost c Q :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun e he _ => hc e (hE e (hQE he)))
  calc
    _ ≤ residualCost c B L := (shortestPathEdges_spec G c B a b hab).2 L hL
    _ ≤ residualCost c B (Q ∪ K) := residualCost_mono_edges c B _ _ hLsub
      (fun e he => hc e (hRinput e he))
    _ ≤ residualCost c B Q + residualCost c B K := residualCost_union_le c B Q K
      (fun e he => hc e (hKinput e he))
    _ ≤ edgeCost c Q + residualCost c B K := add_le_add hQres le_rfl
    _ ≤ edgeCost d H + residualCost c B K := add_le_add hcostQ le_rfl
    _ = _ := by
      have hs := mixedSubdivision_residual_split cert.vertices F d c hsep B K H hHF
      exact hs.symm.trans (congrArg
        (residualCost (mixedSubdivisionCost cert.vertices F d c) (B.image (Sym2.map cert.vertices))) hparts)

end OnlineSteinerForest.UpperBound
