import OnlineSteinerForest.UpperBound.ZonesPartitionBoundary

/-! Convert bottom-up states to finite zone families and merge the root leftover. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [DecidableEq V]

structure ZonePartition (E : Finset (Sym2 V)) (c : Sym2 V → ℝ) (M : ℝ) where
  zones : Finset (Finset (Sym2 V))
  covers : zones.biUnion id = E
  disjoint : ∀ F ∈ zones, ∀ H ∈ zones, F ≠ H → Disjoint F H
  good : ∀ F ∈ zones, ZoneConnected F ∧ M ≤ edgeCost c F ∧ edgeCost c F ≤ 3 * M

private theorem disjoint_of_list {Z : List (Finset (Sym2 V))} (hZ : Z.Pairwise Disjoint)
    {F H : Finset (Sym2 V)} (hF : F ∈ Z) (hH : H ∈ Z) (hne : F ≠ H) : Disjoint F H := by
  induction Z with
  | nil => simp at hF
  | cons A Z ih =>
    obtain ⟨hA, hZ⟩ := List.pairwise_cons.mp hZ
    rcases List.mem_cons.mp hF with hFA | hFtail
    · subst F
      exact hA H (List.mem_cons.mp hH |>.resolve_left (Ne.symm hne))
    · rcases List.mem_cons.mp hH with hHA | hHtail
      · subst H
        exact (hA F hFtail).symm
      · exact ih hZ hFtail hHtail

namespace ZonePartial
variable {r : V} {E : Finset (Sym2 V)} {c : Sym2 V → ℝ} {M : ℝ}

/-- A chosen zone absorbs the root leftover; only its upper budget increases. -/
noncomputable def finish (p : ZonePartial r E c M) (hM : 0 < M)
    (hc : ∀ e ∈ E, 0 ≤ c e) (F : Finset (Sym2 V)) (hF : F ∈ p.zones)
    (hconn : ZoneConnected (F ∪ p.leftover)) : ZonePartition E c M := by
  let Z := p.zones.toFinset
  let A := F ∪ p.leftover
  let T := insert A (Z.erase F)
  have hd : ∀ H ∈ Z, ∀ J ∈ Z, H ≠ J → Disjoint H J := by
    intro H hH J hJ hne
    exact disjoint_of_list (List.pairwise_cons.mp p.disjoint).2
      (List.mem_toFinset.mp hH) (List.mem_toFinset.mp hJ) hne
  have hA (H : Finset (Sym2 V)) (hH : H ∈ Z.erase F) : Disjoint A H := by
    obtain ⟨hne, hH⟩ := Finset.mem_erase.mp hH
    exact Finset.disjoint_union_left.mpr
      ⟨hd F (List.mem_toFinset.mpr hF) H hH (Ne.symm hne), p.left_disjoint (List.mem_toFinset.mp hH)⟩
  have hcover : T.biUnion id = E := by
    ext e
    rw [← p.covers]
    simp only [T, A, Z, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_erase,
      List.mem_toFinset, id_eq, mem_zoneUnion, Finset.mem_union]
    constructor
    · rintro ⟨H, (rfl | ⟨hHF, hH⟩), he⟩
      · rcases Finset.mem_union.mp he with he | he
        · exact Or.inl ⟨F, hF, he⟩
        · exact Or.inr he
      · exact Or.inl ⟨H, hH, he⟩
    · rintro (⟨H, hH, he⟩ | he)
      · by_cases hHF : H = F
        · subst H; exact ⟨F ∪ p.leftover, Or.inl rfl, Finset.mem_union_left _ he⟩
        · exact ⟨H, Or.inr ⟨hHF, hH⟩, he⟩
      · exact ⟨F ∪ p.leftover, Or.inl rfl, Finset.mem_union_right _ he⟩
  refine ⟨T, hcover, ?_, ?_⟩
  · intro H hH J hJ hne
    rcases Finset.mem_insert.mp hH with rfl | hH
    · exact hA J ((Finset.mem_insert.mp hJ).resolve_left (Ne.symm hne))
    · rcases Finset.mem_insert.mp hJ with rfl | hJ
      · exact (hA H hH).symm
      · exact hd H (Finset.mem_erase.mp hH).2 J (Finset.mem_erase.mp hJ).2 hne
  · intro H hH
    rcases Finset.mem_insert.mp hH with rfl | hH
    · have hcost : edgeCost c A = edgeCost c F + edgeCost c p.leftover := by
        exact Finset.sum_union (p.left_disjoint hF).symm
      have hleft : 0 ≤ edgeCost c p.leftover := Finset.sum_nonneg
        (fun e he => hc e (p.leftover_subset he))
      obtain ⟨_, hlo, hhi⟩ := p.good F hF
      exact ⟨hconn, by rw [hcost]; linarith, by rw [hcost]; linarith [p.small]⟩
    · obtain ⟨hconn, hlo, hhi⟩ := p.good H (List.mem_toFinset.mp (Finset.mem_erase.mp hH).2)
      exact ⟨hconn, hlo, by linarith⟩

end ZonePartial
end OnlineSteinerForest.UpperBound
