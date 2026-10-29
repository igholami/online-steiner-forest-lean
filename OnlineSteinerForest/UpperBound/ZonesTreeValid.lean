import OnlineSteinerForest.UpperBound.ZonesTreeShape

/-! Edge-disjoint branches and attachment of a fresh leaf in rooted tree expressions. -/
namespace OnlineSteinerForest.UpperBound.ZoneTree

open scoped Classical
variable {V W : Type*} [DecidableEq V] [DecidableEq W]

def Valid {r : V} : ZoneTree V r → Prop
  | .leaf _ => True
  | .extend r s t => s(r, s) ∉ t.edges ∧ t.Valid
  | .join _ a b => Disjoint a.edges b.edges ∧ a.Valid ∧ b.Valid

theorem endpoint_mem {r : V} (t : ZoneTree V r) {e : Sym2 V} (he : e ∈ t.edges)
    {v : V} (hv : v ∈ e) : v ∈ t.vertices := by
  induction t with
  | leaf => simp [edges] at he
  | extend r s t ih =>
    rcases Finset.mem_insert.mp he with rfl | he
    · rcases Sym2.mem_iff.mp hv with rfl | rfl
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (root_mem t)
    · exact Finset.mem_insert_of_mem (ih he)
  | join _ a b ha hb =>
    rcases Finset.mem_union.mp he with he | he
    · exact Finset.mem_union_left _ (ha he)
    · exact Finset.mem_union_right _ (hb he)

theorem fresh_edge_not_mem {r : V} (t : ZoneTree V r) (u v : V) (hv : v ∉ t.vertices) :
    s(u, v) ∉ t.edges := fun he => hv (endpoint_mem t he (Sym2.mem_mk_right _ _))

theorem valid_map {r : V} (t : ZoneTree V r) (ht : t.Valid) (f : V → W)
    (hf : Function.Injective f) : (t.map f).Valid := by
  induction t with
  | leaf => trivial
  | extend r s t ih =>
    change _ ∧ _
    rw [edges_map]
    constructor
    · intro he
      obtain ⟨e, he, heq⟩ := Finset.mem_image.mp he
      have heq' : Sym2.map f e = Sym2.map f s(r, s) := heq
      exact ht.1 ((Sym2.map.injective hf heq') ▸ he)
    · exact ih ht.2
  | join r a b ha hb =>
    change _ ∧ _ ∧ _
    rw [edges_map, edges_map]
    refine ⟨?_, ha ht.2.1, hb ht.2.2⟩
    apply Finset.disjoint_left.mpr
    intro x hxa hxb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hxa
    obtain ⟨b, hb, heq⟩ := Finset.mem_image.mp hxb
    exact Finset.disjoint_left.mp ht.1 ha ((Sym2.map.injective hf heq) ▸ hb)

theorem valid_graft {r : V} (t : ZoneTree V r) (ht : t.Valid) (u v : V)
    (hu : u ∈ t.vertices) (hv : v ∉ t.vertices) : (t.graft u v hu).Valid := by
  induction t with
  | leaf r =>
    simp [graft, Valid, edges]
  | extend r s t ih =>
    simp only [graft]
    split_ifs with h
    · change Disjoint _ _ ∧ _ ∧ _
      refine ⟨?_, ht, by simp [Valid, edges]⟩
      simp only [edges, Finset.insert_empty, Finset.disjoint_singleton_right]
      subst u
      exact fresh_edge_not_mem (.extend r s t) r v hv
    · change _ ∧ _
      rw [edges_graft]
      refine ⟨?_, ih ht.2 (by simpa [vertices, h] using hu)
        (fun he => hv (Finset.mem_insert_of_mem he))⟩
      intro he
      rcases Finset.mem_insert.mp he with he | he
      · have he' : v ∈ s(r, s) := he ▸ Sym2.mem_mk_right u v
        rcases Sym2.mem_iff.mp he' with he' | he'
        · apply hv
          rw [he']
          exact Finset.mem_insert_self _ _
        · apply hv
          rw [he']
          exact Finset.mem_insert_of_mem (root_mem t)
      · exact ht.1 he
  | join r a b ha hb =>
    simp only [graft]
    split_ifs with h
    · change Disjoint _ _ ∧ _ ∧ _
      rw [edges_graft]
      refine ⟨?_, ha ht.2.1 h (fun he => hv (Finset.mem_union_left _ he)), ht.2.2⟩
      exact Finset.disjoint_insert_left.mpr
        ⟨fresh_edge_not_mem b u v (fun he => hv (Finset.mem_union_right _ he)), ht.1⟩
    · change Disjoint _ _ ∧ _ ∧ _
      rw [edges_graft]
      refine ⟨?_, ht.2.1, hb ht.2.2 (by simpa [vertices, h] using hu)
        (fun he => hv (Finset.mem_union_right _ he))⟩
      exact Finset.disjoint_insert_right.mpr
        ⟨fresh_edge_not_mem a u v (fun he => hv (Finset.mem_union_left _ he)), ht.1⟩

end OnlineSteinerForest.UpperBound.ZoneTree
