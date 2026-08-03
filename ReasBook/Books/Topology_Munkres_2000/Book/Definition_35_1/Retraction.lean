module

public import Mathlib.Topology.ContinuousMap.Basic

public section

universe u

namespace Set

variable {X : Type u} [TopologicalSpace X]

/-- A retraction onto `A` is a continuous map to `A` that is a left inverse of the
subtype inclusion. -/
structure Retraction (A : Set X) where
  toContinuousMap : C(X, A)
  leftInverse : Function.LeftInverse toContinuousMap Subtype.val

namespace Retraction

/-- Construct a retraction from a continuous left inverse to the subtype inclusion. -/
@[expose]
def ofContinuousMap {A : Set X} (r : C(X, A))
    (leftInverse : Function.LeftInverse r Subtype.val) : Retraction A :=
  ⟨r, leftInverse⟩

/-- Evaluate a retraction through its underlying continuous map. -/
@[expose]
def apply {A : Set X} (r : Retraction A) (x : X) : A :=
  r.toContinuousMap x

/-- Two retractions are equal when they agree pointwise. -/
@[ext]
theorem ext {A : Set X} {r s : Retraction A} (h : ∀ x, r.apply x = s.apply x) : r = s := by
  cases r
  cases s
  simp only [apply] at h
  congr
  exact ContinuousMap.ext h

/-- Evaluation of a retraction agrees with evaluation of its continuous map. -/
@[simp]
theorem apply_eq {A : Set X} (r : Retraction A) (x : X) :
    r.apply x = r.toContinuousMap x := rfl

/-- A retraction restricts to the identity on its target subset. -/
@[simp]
theorem apply_coe {A : Set X} (r : Retraction A) (a : A) : r.apply a = a :=
  r.leftInverse a

end Retraction

/-- A subset is a retract when it admits a retraction from the ambient space. -/
def IsRetract (A : Set X) : Prop :=
  Nonempty (Retraction A)

/-- A subset is a retract exactly when a continuous left inverse to its inclusion exists. -/
theorem isRetract_iff (A : Set X) :
    IsRetract A ↔ ∃ r : C(X, A), Function.LeftInverse r Subtype.val := by
  constructor
  · rintro ⟨r⟩
    exact ⟨r.toContinuousMap, r.leftInverse⟩
  · rintro ⟨r, hr⟩
    exact ⟨Retraction.ofContinuousMap r hr⟩

end Set
