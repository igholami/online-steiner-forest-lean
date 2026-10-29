import OnlineSteinerForest.UpperBound.ZonesSubdivisionCertificate

/-! Original auxiliary edges retain their original cost beside disjoint reference segments. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V W : Type*} [DecidableEq V] [DecidableEq W]

noncomputable def embeddedOriginalCost (f : V ↪ W) (c : Sym2 V → ℝ) (x : Sym2 W) : ℝ :=
  if h : ∃ e : Sym2 V, Sym2.map f e = x then c (Classical.choose h) else 0

@[simp] theorem embeddedOriginalCost_apply (f : V ↪ W) (c : Sym2 V → ℝ) (e : Sym2 V) :
    embeddedOriginalCost f c (Sym2.map f e) = c e := by
  unfold embeddedOriginalCost
  rw [dif_pos ⟨e, rfl⟩]
  exact congrArg c (Sym2.map.injective f.injective (Classical.choose_spec (show
    ∃ a : Sym2 V, Sym2.map f a = Sym2.map f e from ⟨e, rfl⟩)))

noncomputable def mixedSubdivisionCost (f : V ↪ W) (F : Finset (Sym2 W))
    (d : Sym2 W → ℝ) (c : Sym2 V → ℝ) (x : Sym2 W) : ℝ :=
  if x ∈ F then d x else embeddedOriginalCost f c x

@[simp] theorem mixedSubdivisionCost_reference (f : V ↪ W) (F : Finset (Sym2 W))
    (d : Sym2 W → ℝ) (c : Sym2 V → ℝ) {x : Sym2 W} (hx : x ∈ F) :
    mixedSubdivisionCost f F d c x = d x := if_pos hx

theorem mixedSubdivisionCost_original (f : V ↪ W) (F : Finset (Sym2 W))
    (d : Sym2 W → ℝ) (c : Sym2 V → ℝ)
    (hsep : ∀ e : Sym2 V, Sym2.map f e ∉ F) (e : Sym2 V) :
    mixedSubdivisionCost f F d c (Sym2.map f e) = c e := by
  simp [mixedSubdivisionCost, hsep]

theorem mixedSubdivisionCost_reference_cost (f : V ↪ W) (F : Finset (Sym2 W))
    (d : Sym2 W → ℝ) (c : Sym2 V → ℝ) (H : Finset (Sym2 W)) (hH : H ⊆ F) :
    edgeCost (mixedSubdivisionCost f F d c) H = edgeCost d H :=
  Finset.sum_congr rfl (fun _ h => mixedSubdivisionCost_reference _ _ _ _ (hH h))

theorem mixedSubdivisionCost_nonneg (f : V ↪ W) (F : Finset (Sym2 W))
    (d : Sym2 W → ℝ) (c : Sym2 V → ℝ) (E : Finset (Sym2 V))
    (hsep : ∀ e : Sym2 V, Sym2.map f e ∉ F) (hd : ∀ e ∈ F, 0 ≤ d e)
    (hc : ∀ e ∈ E, 0 ≤ c e) :
    ∀ x ∈ F ∪ E.image (Sym2.map f), 0 ≤ mixedSubdivisionCost f F d c x := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · rw [mixedSubdivisionCost_reference _ _ _ _ hx]
    exact hd x hx
  · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
    rw [mixedSubdivisionCost_original _ _ _ _ hsep]
    exact hc e he

end OnlineSteinerForest.UpperBound
