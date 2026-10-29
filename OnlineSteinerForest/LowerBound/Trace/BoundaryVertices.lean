import OnlineSteinerForest.LowerBound.Trace.RunBound

/-! Distinct vertices prescribed by an alternate route, in interleaved run order. -/
namespace OnlineSteinerForest.LowerBound.Trace.Route

variable {m : ℕ} {σ : Equiv.Perm (Fin (2 * m))} {R : Finset (Fin m)}
variable {u v : Fin (2 * m)}

def shortcutVertices : {u v : Fin (2 * m)} → Route σ R u v → List (Fin (2 * m))
  | _, _, .nil _ => []
  | _, _, .base _ p => p.shortcutVertices
  | a, _, .shortcut (v := b) _ _ _ p => a :: b :: p.shortcutVertices

def boundaries (p : Route σ R u v) : List (Fin (2 * m)) :=
  u :: (p.shortcutVertices ++ [v])

theorem shortcutVertices_length (p : Route σ R u v) :
    p.shortcutVertices.length = 2 * p.ranks.length := by
  induction p <;> simp [shortcutVertices, ranks, *] <;> omega

@[simp] theorem boundaries_length (p : Route σ R u v) :
    p.boundaries.length = 2 * p.ranks.length + 2 := by
  simp [boundaries, shortcutVertices_length]

/-- Appending the final terminal to shortcut endpoints stays within the original support.
If the route starts with a base edge, it also stays within the support's tail. -/
theorem endpoints_end_sublist (p : Route σ R u v) (hp : p.realize.IsPath)
    (hend : ∀ i ∈ R, v ≠ leftEndpoint σ i ∧ v ≠ rightEndpoint σ i) :
    (p.shortcutVertices ++ [v]).Sublist p.support ∧
      (p.StartsBase → (p.shortcutVertices ++ [v]).Sublist p.support.tail) := by
  induction p with
  | nil => simp [shortcutVertices, support, StartsBase]
  | @base a b z h p ih =>
    have ht := ih hp.of_cons hend
    constructor
    · exact List.Sublist.cons a ht.1
    · intro _; exact ht.1
  | @shortcut a b c i hi oi p ih =>
    cases p with
    | nil b =>
      rcases oi with oi | oi
      · exact ((hend i hi).2 oi.2).elim
      · exact ((hend i hi).1 oi.2).elim
    | base h p =>
      have ht := ih hp.of_cons.of_cons hend
      have hs := ht.2 (by trivial)
      constructor
      · change (a :: b :: (p.shortcutVertices ++ [c])).Sublist (a :: b :: p.support)
        change (p.shortcutVertices ++ [c]).Sublist p.support at hs
        exact List.Sublist.cons_cons a (List.Sublist.cons_cons b hs)
      · simp [StartsBase]
    | shortcut j hj oj p => exact (no_consecutive_shortcuts i hi oi j hj oj p hp).elim

theorem boundaries_sublist (p : Route σ R u v) (hp : p.realize.IsPath) (huv : u ≠ v)
    (hstart : ∀ i ∈ R, u ≠ leftEndpoint σ i ∧ u ≠ rightEndpoint σ i)
    (hend : ∀ i ∈ R, v ≠ leftEndpoint σ i ∧ v ≠ rightEndpoint σ i) :
    p.boundaries.Sublist p.support := by
  have hbase : p.StartsBase := by
    cases p with
    | nil => exact (huv rfl).elim
    | base => trivial
    | shortcut i hi oi p =>
      rcases oi with oi | oi
      · exact ((hstart i hi).1 oi.1).elim
      · exact ((hstart i hi).2 oi.1).elim
  have hs := (endpoints_end_sublist p hp hend).2 hbase
  have heq : p.support = u :: p.support.tail := by cases p <;> rfl
  rw [heq]
  exact List.Sublist.cons_cons u hs

theorem boundaries_nodup (p : Route σ R u v) (hp : p.realize.IsPath) (huv : u ≠ v)
    (hstart : ∀ i ∈ R, u ≠ leftEndpoint σ i ∧ u ≠ rightEndpoint σ i)
    (hend : ∀ i ∈ R, v ≠ leftEndpoint σ i ∧ v ≠ rightEndpoint σ i) : p.boundaries.Nodup :=
  List.Nodup.sublist (boundaries_sublist p hp huv hstart hend) (p.support_nodup hp)

/-- The injective image tuple used when counting compatible permutations. -/
def vertexTuple (p : Route σ R u v) (hp : p.realize.IsPath) (huv : u ≠ v)
    (hstart : ∀ i ∈ R, u ≠ leftEndpoint σ i ∧ u ≠ rightEndpoint σ i)
    (hend : ∀ i ∈ R, v ≠ leftEndpoint σ i ∧ v ≠ rightEndpoint σ i) :
    Fin (2 * p.ranks.length + 2) ↪ Fin (2 * m) where
  toFun k := p.boundaries.get ⟨k.val, by simpa only [boundaries_length] using k.isLt⟩
  inj' := by
    intro a b hab
    have hinj := List.nodup_iff_injective_get.mp (p.boundaries_nodup hp huv hstart hend)
    exact Fin.ext (congrArg (fun k : Fin p.boundaries.length => k.val) (hinj hab))

end OnlineSteinerForest.LowerBound.Trace.Route
