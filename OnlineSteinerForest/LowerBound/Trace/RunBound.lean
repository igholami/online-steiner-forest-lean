import OnlineSteinerForest.LowerBound.Trace.Support
import OnlineSteinerForest.LowerBound.EndpointFacts

/-! In a simple alternate route, shortcuts are separated by nonempty path runs. -/
namespace OnlineSteinerForest.LowerBound.Trace

variable {m : ℕ} {σ : Equiv.Perm (Fin (2 * m))} {R : Finset (Fin m)}

theorem successive_shortcuts_backtrack (u v z : Fin (2 * m)) (i j : Fin m)
    (hi : (u = leftEndpoint σ i ∧ v = rightEndpoint σ i) ∨
      (u = rightEndpoint σ i ∧ v = leftEndpoint σ i))
    (hj : (v = leftEndpoint σ j ∧ z = rightEndpoint σ j) ∨
      (v = rightEndpoint σ j ∧ z = leftEndpoint σ j)) : u = z := by
  have hvi : v = leftEndpoint σ i ∨ v = rightEndpoint σ i := by
    rcases hi with hi | hi
    · exact Or.inr hi.2
    · exact Or.inl hi.2
  have hvj : v = leftEndpoint σ j ∨ v = rightEndpoint σ j := by
    rcases hj with hj | hj
    · exact Or.inl hj.1
    · exact Or.inr hj.1
  have hij := endpoint_rank_unique σ v i j hvi hvj
  subst j
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · exact (endpoints_ne σ i (hj.1.symm.trans hi.2)).elim
  · exact hi.1.trans hj.2.symm
  · exact hi.1.trans hj.2.symm
  · exact (endpoints_ne σ i (hi.2.symm.trans hj.1)).elim

namespace Route

variable {u v z t : Fin (2 * m)}

def StartsBase : {u v : Fin (2 * m)} → Route σ R u v → Prop
  | _, _, .base _ _ => True
  | _, _, _ => False

theorem no_consecutive_shortcuts (i : Fin m) (hi : i ∈ R) (oi)
    (j : Fin m) (hj : j ∈ R) (oj) (p : Route σ R z t)
    (hp : (Route.shortcut (u := u) (v := v) i hi oi (.shortcut j hj oj p)).realize.IsPath) : False := by
  have hback := successive_shortcuts_backtrack u v z i j oi oj
  have hn := support_nodup _ hp
  change (u :: v :: p.support).Nodup at hn
  have hmem : u ∈ p.support := hback.symm ▸ p.start_mem_support
  exact (List.nodup_cons.mp hn).1 (List.mem_cons_of_mem v hmem)

/-- Ending at a vertex without a matching edge forces one final path run. -/
theorem counts_end_unmatched (p : Route σ R u v) (hp : p.realize.IsPath)
    (hend : ∀ i ∈ R, v ≠ leftEndpoint σ i ∧ v ≠ rightEndpoint σ i) :
    p.ranks.length ≤ p.baseSteps ∧ (p.StartsBase → p.ranks.length + 1 ≤ p.baseSteps) := by
  induction p with
  | nil => simp [ranks, baseSteps, StartsBase]
  | base h p ih =>
    have ht := ih hp.of_cons hend
    simp only [ranks, baseSteps, StartsBase]
    constructor <;> omega
  | @shortcut a b c i hi oi p ih =>
    cases p with
    | nil b =>
      rcases oi with oi | oi
      · exact ((hend i hi).2 oi.2).elim
      · exact ((hend i hi).1 oi.2).elim
    | base h p =>
      have ht := ih hp.of_cons.of_cons hend
      have hstrong := ht.2 (by trivial)
      constructor
      · change p.ranks.length + 1 ≤ p.baseSteps + 1
        change p.ranks.length + 1 ≤ p.baseSteps + 1 at hstrong
        exact hstrong
      · simp [StartsBase]
    | shortcut j hj oj p => exact (no_consecutive_shortcuts i hi oi j hj oj p hp).elim

/-- Alternate paths start and end with nonempty original-path runs. -/
theorem shortcut_count_add_one_le_baseSteps (p : Route σ R u v) (hp : p.realize.IsPath)
    (huv : u ≠ v)
    (hstart : ∀ i ∈ R, u ≠ leftEndpoint σ i ∧ u ≠ rightEndpoint σ i)
    (hend : ∀ i ∈ R, v ≠ leftEndpoint σ i ∧ v ≠ rightEndpoint σ i) :
    p.ranks.length + 1 ≤ p.baseSteps := by
  cases p with
  | nil => exact (huv rfl).elim
  | base h p => exact (counts_end_unmatched _ hp hend).2 (by trivial)
  | shortcut i hi oi p =>
    rcases oi with oi | oi
    · exact ((hstart i hi).1 oi.1).elim
    · exact ((hstart i hi).2 oi.1).elim

end Route
end OnlineSteinerForest.LowerBound.Trace
