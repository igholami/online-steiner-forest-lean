import OnlineSteinerForest.LowerBound.Trace.Basic

/-! Compress a simple subdivided-graph path into original path steps and shortcuts. -/
namespace OnlineSteinerForest.LowerBound.Trace

variable {m : ℕ} (σ : Equiv.Perm (Fin (2 * m))) (R : Finset (Fin m))

theorem base_adj_imp (u v : Fin (2 * m))
    (huv : (constructionGraph σ R).Adj (Sum.inl u) (Sum.inl v)) :
    (SimpleGraph.pathGraph (2 * m)).Adj u v := by
  have he : s(Sum.inl u, Sum.inl v) ∈ constructionEdges σ R := huv.1
  rcases Finset.mem_union.mp he with he | he
  · obtain ⟨⟨a, b⟩, hab, heq⟩ := Finset.mem_image.mp he
    have h := (Finset.mem_filter.mp hab).2
    change a.val + 1 = b.val ∨ b.val + 1 = a.val at h
    rw [SimpleGraph.pathGraph_adj]
    simp only [Sym2.eq_iff, Sum.inl.injEq] at heq
    rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h
    · exact h.symm
  · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp he
    simp [matchingEdges] at hi

/-- Compression preserves the actual mathlib walk, not just its endpoints or cost. -/
theorem exists_route_of_isPath (u v : Fin (2 * m))
    (p : (constructionGraph σ R).Walk (Sum.inl u) (Sum.inl v)) (hp : p.IsPath) :
    ∃ r : Route σ R u v, r.realize = p := by
  have aux : ∀ n : ℕ, ∀ u v : Fin (2 * m),
      ∀ p : (constructionGraph σ R).Walk (Sum.inl u) (Sum.inl v),
      p.length = n → p.IsPath → ∃ r : Route σ R u v, r.realize = p := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro u v p hn hp
      by_cases huv : u = v
      · subst v
        have hpnil : p.Nil := hp.nil_iff_eq.mpr rfl
        cases hpnil
        exact ⟨.nil u, rfl⟩
      · obtain ⟨next, hadj, q, rfl⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne
          (by simpa only [ne_eq, Sum.inl.injEq] using huv) p
        cases next with
        | inl y =>
          have hbase := base_adj_imp σ R u y hadj
          have hlt : q.length < n := by rw [← hn, SimpleGraph.Walk.length_cons]; omega
          obtain ⟨r, hr⟩ := ih q.length hlt y v q rfl hp.of_cons
          refine ⟨.base hbase r, ?_⟩
          change SimpleGraph.Walk.cons hadj r.realize = SimpleGraph.Walk.cons hadj q
          rw [hr]
        | inr i =>
          have hstart := (subdivision_adj σ R i (Sum.inl u)).mp hadj.symm
          have hu : u = leftEndpoint σ i ∨ u = rightEndpoint σ i := by
            simpa only [Sum.inl.injEq] using hstart.2
          obtain ⟨next, hnext, r, rfl⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne (by simp) q
          cases next with
          | inr j =>
            have hh := (subdivision_adj σ R i (Sum.inr j)).mp hnext
            simp at hh
          | inl z =>
            have hend := (subdivision_adj σ R i (Sum.inl z)).mp hnext
            have hz : z = leftEndpoint σ i ∨ z = rightEndpoint σ i := by
              simpa only [Sum.inl.injEq] using hend.2
            have huz : u ≠ z := by
              intro heq
              subst z
              have hnoreturn := (SimpleGraph.Walk.cons_isPath_iff hadj _).mp hp |>.2
              exact hnoreturn (by simp)
            have hor : (u = leftEndpoint σ i ∧ z = rightEndpoint σ i) ∨
                (u = rightEndpoint σ i ∧ z = leftEndpoint σ i) := by
              rcases hu with hu | hu <;> rcases hz with hz | hz
              · exact (huz (hu.trans hz.symm)).elim
              · exact Or.inl ⟨hu, hz⟩
              · exact Or.inr ⟨hu, hz⟩
              · exact (huz (hu.trans hz.symm)).elim
            have hlt : r.length < n := by
              rw [← hn, SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_cons]
              omega
            obtain ⟨s, hs⟩ := ih r.length hlt z v r rfl hp.of_cons.of_cons
            exact ⟨.shortcut i hstart.1 hor s, by simp only [Route.realize, hs]⟩
  exact aux p.length u v p rfl hp

end OnlineSteinerForest.LowerBound.Trace
