import OnlineSteinerForest.LowerBound.Trace.Grouped
import OnlineSteinerForest.LowerBound.EndpointFacts

/-! Runs in a simple alternate route are simple paths of positive length. -/
namespace OnlineSteinerForest.LowerBound.Trace

variable {m : ℕ} {σ : Equiv.Perm (Fin (2 * m))} {R : Finset (Fin m)}

namespace Route

theorem prependRun_path_parts {u a v : Fin (2 * m)}
    (w : (SimpleGraph.pathGraph (2 * m)).Walk u a) (p : Route σ R a v)
    (hp : (prependRun w p).realize.IsPath) : w.IsPath ∧ p.realize.IsPath := by
  rw [realize_prependRun] at hp
  exact ⟨hp.of_append_left.of_map, hp.of_append_right⟩

end Route

namespace Grouped

variable {u v : Fin (2 * m)}

def RunsSimple : {u v : Fin (2 * m)} → Grouped σ R u v → Prop
  | _, _, .last w => w.IsPath
  | _, _, .next w _ _ _ tail => w.IsPath ∧ tail.RunsSimple

def RunsPositive : {u v : Fin (2 * m)} → Grouped σ R u v → Prop
  | _, _, .last w => 0 < w.length
  | _, _, .next w _ _ _ tail => 0 < w.length ∧ tail.RunsPositive

def firstLength : {u v : Fin (2 * m)} → Grouped σ R u v → ℕ
  | _, _, .last w => w.length
  | _, _, .next w _ _ _ _ => w.length

theorem runsSimple_of_isPath (p : Grouped σ R u v) (hp : p.toRoute.realize.IsPath) : p.RunsSimple := by
  induction p with
  | last w => exact (Route.prependRun_path_parts w _ hp).1
  | next w i hi ho tail ih =>
    have ht := Route.prependRun_path_parts w (.shortcut i hi ho tail.toRoute) hp
    exact ⟨ht.1, ih ht.2.of_cons.of_cons⟩

theorem firstLength_pos_of_unmatched (p : Grouped σ R u v) (huv : u ≠ v)
    (hstart : ∀ i ∈ R, u ≠ leftEndpoint σ i ∧ u ≠ rightEndpoint σ i) : 0 < p.firstLength := by
  cases p with
  | last w =>
    cases w with
    | nil => exact (huv rfl).elim
    | cons => simp [firstLength, SimpleGraph.Walk.length_cons]
  | next w i hi ho tail =>
    cases w with
    | nil =>
      rcases ho with ho | ho
      · exact ((hstart i hi).1 ho.1).elim
      · exact ((hstart i hi).2 ho.1).elim
    | cons => simp [firstLength, SimpleGraph.Walk.length_cons]

theorem firstLength_pos_of_previous (p : Grouped σ R u v) (i : Fin m) (hi : i ∈ R)
    (hu : u = leftEndpoint σ i ∨ u = rightEndpoint σ i) (hnot : i ∉ p.ranks)
    (hend : ∀ j ∈ R, v ≠ leftEndpoint σ j ∧ v ≠ rightEndpoint σ j) : 0 < p.firstLength := by
  cases p with
  | last w =>
    cases w with
    | nil =>
      rcases hu with hu | hu
      · exact ((hend i hi).1 hu).elim
      · exact ((hend i hi).2 hu).elim
    | cons => simp [firstLength, SimpleGraph.Walk.length_cons]
  | next w j hj ho tail =>
    cases w with
    | nil =>
      have hj' : u = leftEndpoint σ j ∨ u = rightEndpoint σ j := by
        rcases ho with ho | ho
        · exact Or.inl ho.1
        · exact Or.inr ho.1
      have heq := endpoint_rank_unique σ u i j hu hj'
      exact (hnot (by simp [ranks, heq])).elim
    | cons => simp [firstLength, SimpleGraph.Walk.length_cons]

theorem runsPositive_of_first (p : Grouped σ R u v) (hfirst : 0 < p.firstLength)
    (hnd : p.ranks.Nodup)
    (hend : ∀ i ∈ R, v ≠ leftEndpoint σ i ∧ v ≠ rightEndpoint σ i) : p.RunsPositive := by
  induction p with
  | last w => exact hfirst
  | @next u a b v w i hi ho tail ih =>
    change (i :: tail.ranks).Nodup at hnd
    have hb : b = leftEndpoint σ i ∨ b = rightEndpoint σ i := by
      rcases ho with ho | ho
      · exact Or.inr ho.2
      · exact Or.inl ho.2
    have hf := firstLength_pos_of_previous tail i hi hb (List.nodup_cons.mp hnd).1 hend
    exact ⟨hfirst, ih hf (List.nodup_cons.mp hnd).2 hend⟩

end Grouped

namespace Route

variable {u v : Fin (2 * m)}

theorem group_runsSimple (p : Route σ R u v) (hp : p.realize.IsPath) : p.group.RunsSimple := by
  apply Grouped.runsSimple_of_isPath
  rwa [group_toRoute]

theorem group_runsPositive (p : Route σ R u v) (hp : p.realize.IsPath) (huv : u ≠ v)
    (hstart : ∀ i ∈ R, u ≠ leftEndpoint σ i ∧ u ≠ rightEndpoint σ i)
    (hend : ∀ i ∈ R, v ≠ leftEndpoint σ i ∧ v ≠ rightEndpoint σ i) : p.group.RunsPositive := by
  apply Grouped.runsPositive_of_first _ (Grouped.firstLength_pos_of_unmatched _ huv hstart) _ hend
  rw [← Grouped.ranks_toRoute, group_toRoute]
  exact p.ranks_nodup hp

end Route
end OnlineSteinerForest.LowerBound.Trace
