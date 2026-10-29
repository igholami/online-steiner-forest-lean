import OnlineSteinerForest.Graph.Cost

/-! An actual simple charging graph uses one fresh vertex for every auxiliary edge. -/
namespace OnlineSteinerForest.UpperBound.Charging

open scoped Classical
variable {W J : Type*}

/-- Two spokes keep parallel auxiliary edges distinct in a standard simple graph. -/
def graph (H : SimpleGraph W) (left right : J → W) : SimpleGraph (W ⊕ J) where
  Adj x y := match x, y with
    | .inl u, .inl v => H.Adj u v
    | .inl u, .inr j => u = left j ∨ u = right j
    | .inr j, .inl u => u = left j ∨ u = right j
    | .inr _, .inr _ => False
  symm.symm x y := by
    cases x <;> cases y
    · exact fun h => h.symm
    · exact id
    · exact id
    · exact id
  loopless.irrefl x := by cases x <;> simp [SimpleGraph.irrefl]

/-- Delete the auxiliary middle spokes: only the base graph and fresh leaves remain. -/
def referenceSpokes (H : SimpleGraph W) (left : J → W) : SimpleGraph (W ⊕ J) where
  Adj x y := match x, y with
    | .inl u, .inl v => H.Adj u v
    | .inl u, .inr j => u = left j
    | .inr j, .inl u => u = left j
    | .inr _, .inr _ => False
  symm.symm x y := by
    cases x <;> cases y
    · exact fun h => h.symm
    · exact id
    · exact id
    · exact id
  loopless.irrefl x := by cases x <;> simp [SimpleGraph.irrefl]

def middle (right : J → W) (j : J) : Sym2 (W ⊕ J) := s(Sum.inr j, Sum.inl (right j))
def first (left : J → W) (j : J) : Sym2 (W ⊕ J) := s(Sum.inl (left j), Sum.inr j)

noncomputable def edgeLabel [DecidableEq W] (right : J → W) : Sym2 (W ⊕ J) → Option J :=
  Sym2.lift ⟨(fun x y => match x, y with
    | .inl u, .inr j => if u = right j then some j else none
    | .inr j, .inl u => if u = right j then some j else none
    | _, _ => none), by intro x y; cases x <;> cases y <;> rfl⟩

@[simp] theorem edgeLabel_middle [DecidableEq W] (right : J → W) (j : J) :
    edgeLabel right (middle right j) = some j := by simp [edgeLabel, middle]

@[simp] theorem edgeLabel_first [DecidableEq W] (left right : J → W)
    (hne : ∀ j, left j ≠ right j) (j : J) : edgeLabel right (first left j) = none := by
  simp [edgeLabel, first, hne j]

@[simp] theorem edgeLabel_reference [DecidableEq W] (right : J → W) (u v : W) :
    edgeLabel right s(Sum.inl u, Sum.inl v) = none := rfl

noncomputable def cost (c : Sym2 W → ℝ) : Sym2 (W ⊕ J) → ℝ :=
  Sym2.lift ⟨(fun x y => match x, y with
    | .inl u, .inl v => c s(u, v)
    | _, _ => 0), by intro x y; cases x <;> cases y <;> simp [Sym2.eq_swap]⟩

@[simp] theorem cost_reference (c : Sym2 W → ℝ) (u v : W) :
    cost (J := J) c s(Sum.inl u, Sum.inl v) = c s(u, v) := rfl
@[simp] theorem cost_first (c : Sym2 W → ℝ) (left : J → W) (j : J) : cost c (first left j) = 0 := rfl
@[simp] theorem cost_middle (c : Sym2 W → ℝ) (right : J → W) (j : J) : cost c (middle right j) = 0 := rfl

end OnlineSteinerForest.UpperBound.Charging
