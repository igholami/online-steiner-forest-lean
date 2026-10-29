import OnlineSteinerForest.UpperBound.GirthSubdivision

/-! Explicit lists decode the subdivided walk without identifying parallel edge labels. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*}

def dartTrace : (n : ℕ) → Paths (Dart I) n → List (Dart I)
  | 0, p => [p]
  | n + 1, p => dartTrace n p.1 ++ [p.2]

@[simp] theorem dartTrace_length (n : ℕ) (p : Paths (Dart I) n) :
    (dartTrace n p).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [dartTrace, ih]

theorem dartTrace_injective (n : ℕ) : Function.Injective (dartTrace (I := I) n) := by
  induction n with
  | zero => intro p q h; exact List.singleton_injective h
  | succ n ih =>
    intro p q h
    change Paths (Dart I) n × Dart I at p q
    change dartTrace n p.1 ++ [p.2] = dartTrace n q.1 ++ [q.2] at h
    have hh := List.append_inj h (by simp)
    exact Prod.ext (ih hh.1) (List.singleton_injective hh.2)

def nodeTriple (left right : I → V) (d : Dart I) : List (V ⊕ Dart I) :=
  [.inr d, .inr (reverse d), .inl (head left right d)]

def nodeTrace (left right : I → V) : (n : ℕ) → Paths (Dart I) n → List (V ⊕ Dart I)
  | 0, p => nodeTriple left right p
  | n + 1, p => nodeTrace left right n p.1 ++ nodeTriple left right p.2

def decodeTrace : List (V ⊕ Dart I) → List (Dart I)
  | .inr d :: _ :: _ :: xs => d :: decodeTrace xs
  | _ => []

theorem decode_nodeTrace_append (left right : I → V) (n : ℕ) (p : Paths (Dart I) n)
    (xs : List (V ⊕ Dart I)) :
    decodeTrace (nodeTrace left right n p ++ xs) = dartTrace n p ++ decodeTrace xs := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
    change decodeTrace ((nodeTrace left right n p.1 ++ nodeTriple left right p.2) ++ xs) = _
    rw [List.append_assoc, ih]
    simp only [nodeTriple, List.cons_append, List.nil_append, decodeTrace, dartTrace,
      List.append_assoc, List.singleton_append]

theorem nodeTrace_injective (left right : I → V) (n : ℕ) :
    Function.Injective (nodeTrace left right n) := by
  intro p q h
  apply dartTrace_injective n
  have hp := decode_nodeTrace_append left right n p []
  have hq := decode_nodeTrace_append left right n q []
  simp only [List.append_nil, decodeTrace] at hp hq
  exact hp.symm.trans ((congrArg decodeTrace h).trans hq)

end OnlineSteinerForest.UpperBound.Girth
