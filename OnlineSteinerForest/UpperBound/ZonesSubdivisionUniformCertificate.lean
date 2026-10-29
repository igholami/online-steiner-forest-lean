import OnlineSteinerForest.UpperBound.ZonesSubdivisionUniformProperties

/-! A single global certificate works simultaneously for every reference component. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
universe u
variable {V : Type u} [DecidableEq V]

noncomputable def uniformSubdivisionCertificate (E : Finset (Sym2 V)) (c : Sym2 V → ℝ)
    (hnd : ∀ e ∈ E, ¬e.IsDiag) (hc : ∀ e ∈ E, 0 ≤ c e) :
    (n : ℕ) → ZoneSubdivisionCertificate E c (subdivisionEdges E n) (subdivisionCost c n)
  | 0 => .refl E c
  | n + 1 => (uniformSubdivisionCertificate E c hnd hc n).trans
      (.midpoint (subdivisionEdges E n) (subdivisionCost c n)
        (fun e he => (subdivisionProperties E c hnd hc n e he).2)
        (fun e he => (subdivisionProperties E c hnd hc n e he).1))

@[simp] theorem uniformSubdivisionCertificate_vertices (E : Finset (Sym2 V)) (c : Sym2 V → ℝ)
    (hnd : ∀ e ∈ E, ¬e.IsDiag) (hc : ∀ e ∈ E, 0 ≤ c e) (n : ℕ) :
    (uniformSubdivisionCertificate E c hnd hc n).vertices = subdivisionEmbedding V n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [uniformSubdivisionCertificate, ZoneSubdivisionCertificate.trans,
      ZoneSubdivisionCertificate.midpoint, subdivisionEmbedding, ih]

theorem subdivisionEmbedding_separated (E : Finset (Sym2 V)) (n : ℕ) (e : Sym2 V) :
    Sym2.map (subdivisionEmbedding V (n + 1)) e ∉ subdivisionEdges E (n + 1) := by
  refine Sym2.ind (fun a b => ?_) e
  change s(Sum.inl _, Sum.inl _) ∉ (subdivisionEdges E n).biUnion zoneSplitEdges
  exact not_mem_split_old _ _ _

end OnlineSteinerForest.UpperBound
