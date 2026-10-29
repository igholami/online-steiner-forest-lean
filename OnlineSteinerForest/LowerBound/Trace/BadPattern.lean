import OnlineSteinerForest.LowerBound.Trace.PatternWeight
import OnlineSteinerForest.LowerBound.Trace.EncodedRuns
import OnlineSteinerForest.LowerBound.Trace.Shape

/-! The actual bad-rank event is covered by the finite pattern family. -/
namespace OnlineSteinerForest.LowerBound.Trace

variable [OnlineSteinerForest.PathSelection]

open Probability

theorem exists_pattern_of_bad_rank (h : ℕ) (hh : 32 ≤ h)
    (σ : Equiv.Perm (Fin (2 * matchingSize h))) (i : Fin (matchingSize h))
    (hi : firstRank h ≤ i.val + 1) (hbad : ¬ GoodRank h σ i) :
    ∃ q : Fin (logSize h ^ 2), ∃ p : RawPattern h i q.val, ∃ hp : p.Valid,
      (∀ k, σ (boundaryTuple i p.ranks p.flip k) = p.imageTuple hp k) ∧ 1 ≤ p.weight := by
  obtain ⟨r, hr, hcheap⟩ := exists_route_of_bad_rank h σ i hbad
  let g := r.group
  have hgs : g.RunsSimple := r.group_runsSimple hr
  have hgp : g.RunsPositive := r.group_runsPositive hr (endpoints_ne σ i)
    (test_left_unmatched h σ i) (test_right_unmatched h σ i)
  have hq := bad_route_size_bound h hh σ i hi r hr hcheap
  have hgranks : g.ranks = r.ranks := (g.ranks_toRoute).symm.trans
    (congrArg Route.ranks r.group_toRoute)
  have hlen : g.runData.length = r.ranks.length + 1 := by rw [g.runData_length, hgranks]
  have hdestlen : g.destinations.length = r.ranks.length := by rw [g.destinations_length, hgranks]
  have hsum : g.lengths.sum = r.baseSteps := g.sum_lengths.trans
    (congrArg Route.baseSteps r.group_toRoute)
  have hbase := r.baseSteps_le_cost (testPrice h i) (fun j _ => by
    unfold testPrice
    split_ifs
    · exact le_rfl
    · exact rankPrice_nonneg h j)
  have hbasereal : (r.baseSteps : ℝ) ≤ (logSize h : ℝ) ^ 2 :=
    hbase.trans (hcheap.trans (rankPrice_le_logSize_sq h hh i hi))
  have hbaseNat : r.baseSteps ≤ logSize h ^ 2 := by exact_mod_cast hbasereal
  have hpos : ∀ d ∈ g.runData, 0 < d.1 := g.runData_positive hgp
  have hbound : ∀ d ∈ g.runData, d.1 ≤ logSize h ^ 2 := by
    intro d hd
    have hm : d.1 ∈ g.lengths := by
      rw [← g.runData_fst]
      exact List.mem_map.mpr ⟨d, hd, rfl⟩
    have hb := List.le_sum_of_mem hm
    rw [hsum] at hb
    exact hb.trans hbaseNat
  let p : RawPattern h i r.ranks.length :=
    { start := leftEndpoint σ i
      destinations := fun j => g.destinations.get ⟨j.val, by simpa only [hdestlen] using j.isLt⟩
      runs := encodeRuns g.runData hlen hpos hbound
      ranks := routeRanks i r hr (fun _j hj => (Finset.mem_erase.mp hj).1)
      flip := routeFlips r }
  have hdata : p.runData = g.runData := encodeRuns_ofFn g.runData hlen hpos hbound
  have hdest : List.ofFn p.destinations = g.destinations := ofFn_get_of_length_eq _ hdestlen
  have hboundary : p.boundaryList = r.boundaries := by
    unfold RawPattern.boundaryList
    rw [hdata, hdest, Grouped.reconstruct_correct g hgs]
    change g.boundaries = r.boundaries
    exact g.boundaries_toRoute.symm.trans (congrArg Route.boundaries r.group_toRoute)
  have hvalid : p.Valid := by
    rw [RawPattern.Valid, hboundary]
    exact ⟨r.boundaries_length, r.boundaries_nodup hr (endpoints_ne σ i)
      (test_left_unmatched h σ i) (test_right_unmatched h σ i)⟩
  have himage (k : Fin (2 * r.ranks.length + 2)) : p.imageTuple hvalid k =
      r.vertexTuple hr (endpoints_ne σ i) (test_left_unmatched h σ i)
        (test_right_unmatched h σ i) k := by
    have he := congrArg (fun xs : List (Fin (2 * matchingSize h)) => xs[k.val]?) hboundary
    rw [List.getElem?_eq_getElem (by simpa only [hvalid.1] using k.isLt),
      List.getElem?_eq_getElem (by simpa only [r.boundaries_length] using k.isLt)] at he
    exact Option.some.inj he
  have hrunNat : (∑ j : Fin (r.ranks.length + 1), ((p.runs j).1.val + 1)) = r.baseSteps := by
    calc
      _ = (g.runData.map Prod.fst).sum := encodeRuns_sum g.runData hlen hpos hbound
      _ = g.lengths.sum := congrArg List.sum g.runData_fst
      _ = _ := hsum
  have hrun : (∑ j : Fin (r.ranks.length + 1), (((p.runs j).1.val + 1 : ℕ) : ℝ)) =
      (r.baseSteps : ℝ) := by exact_mod_cast hrunNat
  have hranks : (∑ j : Fin r.ranks.length, testPrice h i (p.ranks j).val) =
      (r.ranks.map (testPrice h i)).sum := by
    change (∑ j : Fin r.ranks.length, testPrice h i (r.ranks.get j)) = _
    have he := congrArg (List.map (testPrice h i)) (ofFn_get_of_length_eq r.ranks rfl)
    rw [List.map_ofFn] at he
    simpa only [List.sum_ofFn, Function.comp_apply] using congrArg List.sum he
  refine ⟨⟨r.ranks.length, by omega⟩, p, hvalid, ?_, ?_⟩
  · intro k
    exact (test_route_tuple_images h σ i r hr k).trans (himage k).symm
  · apply pattern_weight_ge_one p _ _ hrun hranks
    rwa [← r.cost_eq_base_plus_ranks (testPrice h i)]

end OnlineSteinerForest.LowerBound.Trace
