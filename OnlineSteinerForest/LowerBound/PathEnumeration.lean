import OnlineSteinerForest.LowerBound.Construction

/-! Enumerate comparison-path edges once, by their smaller endpoint. -/
namespace OnlineSteinerForest.LowerBound

def comparisonEdge {m : ℕ} (i : Fin (2 * m - 1)) : Sym2 (Vertex m) :=
  s(Sum.inl ⟨i.val, by omega⟩, Sum.inl ⟨i.val + 1, by omega⟩)

theorem comparisonEdge_injective (m : ℕ) : Function.Injective (@comparisonEdge m) := by
  intro i j hij
  simp only [comparisonEdge, Sym2.eq_iff, Sum.inl.injEq, Fin.mk.injEq] at hij
  rcases hij with hij | hij
  · exact Fin.ext hij.1
  · omega

theorem comparisonEdges_eq_image (m : ℕ) :
    comparisonEdges m = Finset.univ.image (@comparisonEdge m) := by
  apply Finset.ext
  intro e
  constructor
  · intro he
    obtain ⟨⟨u, v⟩, hp, rfl⟩ := Finset.mem_image.mp he
    rcases (Finset.mem_filter.mp hp).2 with huv | hvu
    · change u.val + 1 = v.val at huv
      refine Finset.mem_image.mpr ⟨⟨u.val, by omega⟩, Finset.mem_univ _, ?_⟩
      change s(Sum.inl u, Sum.inl (⟨u.val + 1, _⟩ : Fin (2 * m))) = _
      congr 1
      exact congrArg Sum.inl (Fin.ext huv)
    · change v.val + 1 = u.val at hvu
      refine Finset.mem_image.mpr ⟨⟨v.val, by omega⟩, Finset.mem_univ _, ?_⟩
      change s(Sum.inl v, Sum.inl (⟨v.val + 1, _⟩ : Fin (2 * m))) = _
      calc
        _ = s(Sum.inl v, Sum.inl u) := by congr 1; exact congrArg Sum.inl (Fin.ext hvu)
        _ = _ := Sym2.eq_swap
  · intro he
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
    refine Finset.mem_image.mpr ⟨(⟨i.val, by omega⟩, ⟨i.val + 1, by omega⟩), ?_, rfl⟩
    simp

theorem comparisonEdges_card (m : ℕ) : (comparisonEdges m).card = 2 * m - 1 := by
  rw [comparisonEdges_eq_image, Finset.card_image_of_injective _ (comparisonEdge_injective m)]
  simp

end OnlineSteinerForest.LowerBound
