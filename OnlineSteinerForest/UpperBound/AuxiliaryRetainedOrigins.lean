import OnlineSteinerForest.UpperBound.AuxiliaryRetainedCorrect

/-! Retained endpoints inherit every reference-large vertex property of their input batch. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem extractAuxiliary_endpoint_origin (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (batch : Finset (Fin requests.length)) (scale : ℝ)
    (i : Fin requests.length) (out : AuxiliaryOutput V)
    (hout : extractAuxiliary G c hc requests feasible fallback batch scale i = some out) :
    (∃ j ∈ batch, out.left = requests[j.val].1 ∨ out.left = requests[j.val].2) ∧
      (∃ j ∈ batch, out.right = requests[j.val].1 ∨ out.right = requests[j.val].2) := by
  unfold extractAuxiliary at hout
  split_ifs at hout with hi hp hb
  · have heq := Option.some.inj hout
    subst out
    exact ⟨⟨i, hi, Or.inl rfl⟩, ⟨i, hi, Or.inr rfl⟩⟩
  · exact extractLabelAux_endpoint_origin G c hc requests feasible fallback batch _ _ scale _ out hout

theorem retainedAuxOutput_endpoints (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (batch : Finset (Fin requests.length)) (scale : ℝ) (P : V → Prop)
    (hP : ∀ j ∈ batch, P requests[j.val].1 ∧ P requests[j.val].2)
    (i : Fin requests.length) (hi : i ∈ retainedAuxRequests G c hc requests feasible fallback batch scale) :
    P (retainedAuxOutput G c hc requests feasible fallback batch scale i hi).left ∧
      P (retainedAuxOutput G c hc requests feasible fallback batch scale i hi).right := by
  unfold retainedAuxOutput
  have hor := extractAuxiliary_endpoint_origin G c hc requests feasible fallback batch scale i _
    (Option.some_get (Finset.mem_filter.mp hi).2).symm
  constructor
  · obtain ⟨j, hj, hleft | hleft⟩ := hor.1 <;> rw [hleft]
    · exact (hP j hj).1
    · exact (hP j hj).2
  · obtain ⟨j, hj, hright | hright⟩ := hor.2 <;> rw [hright]
    · exact (hP j hj).1
    · exact (hP j hj).2

end OnlineSteinerForest.UpperBound
