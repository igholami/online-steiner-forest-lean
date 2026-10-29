import OnlineSteinerForest.UpperBound.GirthPruneLeaf
import OnlineSteinerForest.UpperBound.GirthEndpointGraph
import OnlineSteinerForest.UpperBound.GirthSuppressionBijection

/-! Deleting a leaf preserves connectedness of the remaining endpoint graph. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*} [Fintype V] [Fintype I] [DecidableEq I] [DecidableEq V]

theorem leafCollapse_dart_reachable (left right : I → V) (v : V) (d : Dart I)
    (hd : outgoing left right v = {d}) (a : Dart I) :
    (endpointGraph (leafLeft left right v d hd) (leafRight left right v d hd)).Reachable
      (leafCollapse left right v d hd (tail left right a))
      (leafCollapse left right v d hd (head left right a)) := by
  let f := leafCollapse left right v d hd
  let L := leafLeft left right v d hd
  let R := leafRight left right v d hd
  have ht : tail left right d = v := by
    have hm : d ∈ outgoing left right v := by rw [hd]; simp
    exact (Finset.mem_filter.mp hm).2
  have hn := leaf_nonloop left right v d hd
  have hreach : (endpointGraph L R).Reachable (f (tail left right d)) (f (head left right d)) := by
    have heq : f (tail left right d) = f (head left right d) := by
      apply Subtype.ext
      simp [f, ht, leafCollapse, hn]
    rw [heq]
  by_cases ha : a.1 = d.1
  · rcases dart_eq_or_reverse_of_label_eq a d ha with rfl | rfl
    · exact hreach
    · simpa only [tail_reverse, head_reverse] using hreach.symm
  · have havoid := leaf_edge_avoids left right v d hd a.1 ha
    have hh := dart_endpoint_reachable L R (⟨a.1, ha⟩, a.2)
    convert hh using 1 <;> apply Subtype.ext <;>
      cases hb : a.2 <;> simp [f, L, R, leafCollapse, tail, head, leafLeft, leafRight, hb, havoid.1, havoid.2]

theorem leaf_endpoint_connected (left right : I → V) (v : V) (d : Dart I)
    (hd : outgoing left right v = {d}) (hc : (endpointGraph left right).Connected) :
    (endpointGraph (leafLeft left right v d hd) (leafRight left right v d hd)).Connected where
  preconnected x y := by
    have hf : ∀ u z, (endpointGraph left right).Adj u z →
        (endpointGraph (leafLeft left right v d hd) (leafRight left right v d hd)).Reachable
          (leafCollapse left right v d hd u) (leafCollapse left right v d hd z) := by
      intro u z huz
      obtain ⟨_, a, rfl, rfl⟩ := huz
      exact leafCollapse_dart_reachable left right v d hd a
    have hh := reachable_map_of_adj_reachable (leafCollapse left right v d hd) hf
      (hc.preconnected x.val y.val)
    convert hh using 1 <;> apply Subtype.ext <;> simp [leafCollapse, x.property, y.property]
  nonempty := ⟨⟨head left right d, leaf_nonloop left right v d hd⟩⟩

end OnlineSteinerForest.UpperBound.Girth
