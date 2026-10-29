import OnlineSteinerForest.UpperBound.ZonesSubdivisionPartition

/-! One final binary subdivision separates all reference segments from copied original edges. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
universe u

theorem exists_separated_subdivided_tree_zonePartition {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.IsTree) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (M : ℝ) (hM : 0 < M)
    (hlarge : M ≤ edgeCost c G.edgeFinset) :
    ∃ (W : Type u) (_ : Fintype W) (_ : DecidableEq W)
      (E : Finset (Sym2 W)) (d : Sym2 W → ℝ)
      (cert : ZoneSubdivisionCertificate G.edgeFinset c E d),
      (∀ e ∈ E, 0 ≤ d e) ∧ (∀ e ∈ E, ¬e.IsDiag) ∧
      (∀ e : Sym2 V, Sym2.map cert.vertices e ∉ E) ∧ Nonempty (ZonePartition E d M) := by
  let r := Classical.choice hG.nonempty
  obtain ⟨t, ht, he, _⟩ := exists_zoneTree G hG r
  have hmem : ∀ e ∈ t.edges, e ∈ G.edgeSet := fun e h => G.mem_edgeFinset.mp (he ▸ h)
  have hnd : ∀ e ∈ t.edges, ¬e.IsDiag := fun e h => G.not_isDiag_of_mem_edgeSet (hmem e h)
  have hct : ∀ e ∈ t.edges, 0 ≤ c e := fun e h => hc e (hmem e h)
  let C := edgeCost c t.edges
  have hC : ∀ e ∈ t.edges, c e ≤ C := fun e h => Finset.single_le_sum hct h
  obtain ⟨n, hn⟩ := exists_binary_subdivision_depth C M hM
  obtain ⟨W, hW, dW, s, T, d, hT, hndT, hcT, hCT, hcost, hcert⟩ :=
    exists_iterated_zoneSubdivision t ht hnd c hct C hC n
  letI := hW
  letI := dW
  let U := T.subdivide
  let k := zoneHalfCost d
  have hU : U.Valid := T.valid_subdivide hT hndT
  have hprop : ∀ e ∈ U.edges, ¬e.IsDiag ∧ 0 ≤ k e ∧ k e ≤ M := by
    intro e heU
    obtain ⟨f, hf, hndf, hweight⟩ := zoneSplitUnion_edge (T.edges_subdivide ▸ heU)
    have hw : k e = d f / 2 := hweight d
    exact ⟨hndf, by rw [hw]; exact div_nonneg (hcT f hf) (by norm_num),
      by rw [hw]; have := (hCT f hf).trans hn; linarith⟩
  have hcostU : edgeCost k U.edges = edgeCost c G.edgeFinset := by
    rw [ZoneTree.edges_subdivide, zoneSplitUnion_cost _ d hndT, hcost, he]
  let hcert' := (Classical.choice hcert).trans (ZoneSubdivisionCertificate.midpoint T.edges d hcT hndT)
  let hcertU : ZoneSubdivisionCertificate G.edgeFinset c U.edges k :=
    hcert'.congr he T.edges_subdivide.symm
  let H := SimpleGraph.fromEdgeSet (U.edges : Set (Sym2 (ZoneSubdivisionVertex W)))
  have hH : ∀ e ∈ U.edges, e ∈ H.edgeSet := by
    intro e heU
    simpa only [H, SimpleGraph.edgeSet_fromEdgeSet, Set.mem_sdiff, Sym2.mem_diagSet, Finset.mem_coe] using
      And.intro heU (hprop e heU).1
  let p := U.partition hU H hH k M hM (fun e h => (hprop e h).2.2)
  refine ⟨ZoneSubdivisionVertex W, inferInstance, inferInstance, U.edges, k, hcertU,
    fun e h => (hprop e h).2.1, fun e h => (hprop e h).1, ?_,
    p.complete hM (U.rooted (fun e h => (hprop e h).1))
      (fun e h => (hprop e h).2.1) (by rw [hcostU]; exact hlarge)⟩
  have hvertices : hcertU.vertices = (Classical.choice hcert).vertices.trans Function.Embedding.inl := by
    simp only [hcertU, hcert', ZoneSubdivisionCertificate.congr, ZoneSubdivisionCertificate.trans,
      ZoneSubdivisionCertificate.midpoint]
  intro e
  rw [hvertices]
  refine Sym2.ind (fun a b => ?_) e
  change s(Sum.inl _, Sum.inl _) ∉ U.edges
  rw [ZoneTree.edges_subdivide]
  exact not_mem_split_old _ _ _

end OnlineSteinerForest.UpperBound
