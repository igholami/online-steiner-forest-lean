import OnlineSteinerForest.LowerBound.Sampling.Ordered
import Mathlib.Data.Fintype.CardEmbedding

/-! Ordered subset samples are precisely injective tuples. -/
namespace OnlineSteinerForest.LowerBound.Probability

open scoped Classical

variable {α : Type*} [Fintype α] {r : ℕ}

noncomputable def sampleEmbedding (q : Sampling.OrderedSample (Finset.univ : Finset α) r) :
    Fin r ↪ α where
  toFun i := (q.2 i).val
  inj' _i _j hij := q.2.injective (Subtype.ext hij)

theorem mem_sample_range (q : Sampling.OrderedSample (Finset.univ : Finset α) r) (x : α) :
    x ∈ q.1.val ↔ ∃ i, sampleEmbedding q i = x := by
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := q.2.surjective ⟨x, hx⟩
    exact ⟨i, congrArg Subtype.val hi⟩
  · rintro ⟨i, rfl⟩
    exact (q.2 i).prop

theorem sampleEmbedding_injective :
    Function.Injective (@sampleEmbedding α _ r) := by
  intro q q' heq
  have ht : q.1 = q'.1 := by
    apply Subtype.ext
    apply Finset.ext
    intro x
    rw [mem_sample_range, mem_sample_range, heq]
  rcases q with ⟨t, e⟩
  rcases q' with ⟨t', e'⟩
  dsimp at ht
  subst t'
  have he : e = e' := by
    apply Equiv.ext
    intro i
    apply Subtype.ext
    exact congrArg (fun b : Fin r ↪ α => b i) heq
  subst e'
  rfl

theorem sampleEmbedding_surjective :
    Function.Surjective (@sampleEmbedding α _ r) := by
  intro b
  let t := Finset.univ.image b
  have ht : t ∈ (Finset.univ : Finset α).powersetCard r := by
    apply Finset.mem_powersetCard.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    simp only [t, Finset.card_image_of_injective _ b.injective, Finset.card_univ,
      Fintype.card_fin]
  let f : Fin r → ↥t := fun i => ⟨b i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      exact b.injective (congrArg Subtype.val hij)
    · intro x
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp x.prop
      exact ⟨i, Subtype.ext hi⟩
  refine ⟨⟨⟨t, ht⟩, Equiv.ofBijective f hf⟩, ?_⟩
  apply Function.Embedding.ext
  intro i
  rfl

noncomputable def orderedSampleEquivEmbedding :
    Sampling.OrderedSample (Finset.univ : Finset α) r ≃ (Fin r ↪ α) :=
  Equiv.ofBijective sampleEmbedding ⟨sampleEmbedding_injective, sampleEmbedding_surjective⟩

end OnlineSteinerForest.LowerBound.Probability
