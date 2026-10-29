import OnlineSteinerForest.UpperBound.ZonesPartitionFamily

/-! Flatten edge-disjoint component partitions into one common finite zone family. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {I W : Type*} [DecidableEq I] [DecidableEq W]

theorem ZonePartition.zone_subset {E : Finset (Sym2 W)} {c : Sym2 W → ℝ} {M : ℝ}
    (p : ZonePartition E c M) (Z : Finset (Sym2 W)) (hZ : Z ∈ p.zones) : Z ⊆ E := by
  intro e he
  rw [← p.covers]
  exact Finset.mem_biUnion.mpr ⟨Z, hZ, he⟩

noncomputable def joinZonePartitions (indices : Finset I) (E : I → Finset (Sym2 W))
    (c : Sym2 W → ℝ) (M : ℝ) (P : (i : ↥indices) → ZonePartition (E i.val) c M)
    (hdis : (indices : Set I).PairwiseDisjoint E) : ZonePartition (indices.biUnion E) c M := by
  let zones := indices.attach.biUnion (fun i => (P i).zones)
  refine ⟨zones, ?_, ?_, ?_⟩
  · ext e
    constructor
    · intro he
      obtain ⟨Z, hZ, he⟩ := Finset.mem_biUnion.mp he
      obtain ⟨i, hi, hZ⟩ := Finset.mem_biUnion.mp hZ
      exact Finset.mem_biUnion.mpr ⟨i.val, i.property, (P i).zone_subset Z hZ he⟩
    · intro he
      obtain ⟨i, hi, he⟩ := Finset.mem_biUnion.mp he
      let j : ↥indices := ⟨i, hi⟩
      have he' : e ∈ (P j).zones.biUnion id := by rw [(P j).covers]; exact he
      obtain ⟨Z, hZ, he⟩ := Finset.mem_biUnion.mp he'
      exact Finset.mem_biUnion.mpr ⟨Z, Finset.mem_biUnion.mpr ⟨j, Finset.mem_attach _ _, hZ⟩, he⟩
  · intro A hA B hB hAB
    obtain ⟨i, hi, hAi⟩ := Finset.mem_biUnion.mp hA
    obtain ⟨j, hj, hBj⟩ := Finset.mem_biUnion.mp hB
    by_cases hij : i = j
    · subst j
      exact (P i).disjoint A hAi B hBj hAB
    · have hij' : i.val ≠ j.val := fun h => hij (Subtype.ext h)
      exact (hdis i.property j.property hij').mono ((P i).zone_subset A hAi) ((P j).zone_subset B hBj)
  · intro Z hZ
    obtain ⟨i, hi, hZ⟩ := Finset.mem_biUnion.mp hZ
    exact (P i).good Z hZ

end OnlineSteinerForest.UpperBound
