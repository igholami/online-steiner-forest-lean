import OnlineSteinerForest.LowerBound.Construction
import Mathlib.Data.Finset.Sort

/-! Every constructed instance is feasible because its comparison path is present. -/
namespace OnlineSteinerForest.LowerBound

/-- Include the comparison path in the constructed graph. -/
def comparisonHom {m : ℕ} (σ : Equiv.Perm (Fin (2 * m))) (R : Finset (Fin m)) :
    SimpleGraph.pathGraph (2 * m) →g constructionGraph σ R where
  toFun := Sum.inl
  map_rel' := by
    intro u v huv
    refine ⟨Finset.mem_union_left _ ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨(u, v),
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, SimpleGraph.pathGraph_adj.mp huv⟩, rfl⟩
    · exact fun h => (SimpleGraph.ne_of_adj _ huv) (Sum.inl.inj h)

theorem base_reachable {m : ℕ} (σ : Equiv.Perm (Fin (2 * m))) (R : Finset (Fin m))
    (u v : Fin (2 * m)) :
    (constructionGraph σ R).Reachable (Sum.inl u) (Sum.inl v) :=
  (SimpleGraph.pathGraph_preconnected (2 * m) u v).map (comparisonHom σ R)

/-- Retained pairs arrive in increasing rank order, with natural ranks `i + 1`. -/
def requestedPairs {m : ℕ} (σ : Equiv.Perm (Fin (2 * m))) (R : Finset (Fin m)) :
    List (Vertex m × Vertex m) :=
  (R.sort (· ≤ ·)).map (fun i => (Sum.inl (leftEndpoint σ i), Sum.inl (rightEndpoint σ i)))

theorem requestedPairs_feasible {m : ℕ} (σ : Equiv.Perm (Fin (2 * m)))
    (R : Finset (Fin m)) :
    ∀ q ∈ requestedPairs σ R, (constructionGraph σ R).Reachable q.1 q.2 := by
  intro q hq
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hq
  exact base_reachable σ R _ _

@[simp] theorem requestedPairs_length {m : ℕ} (σ : Equiv.Perm (Fin (2 * m)))
    (R : Finset (Fin m)) : (requestedPairs σ R).length = R.card := by
  simp [requestedPairs]

end OnlineSteinerForest.LowerBound
