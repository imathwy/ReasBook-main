import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open TopologicalSpace

namespace ContinuousMap

variable {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]

/- Definition 4.25-extra-1 (1): a section of a bundled continuous map `π : C(M, N)` is exactly a
continuous right inverse `σ : C(N, M)`, expressed by the canonical owner
`Function.RightInverse σ π`. -/
recall Function.RightInverse

variable (π : C(M, N)) (U : TopologicalSpace.Opens N) (σ : C(U, M))

/- Definition 4.25-extra-1 (2): a local section of a continuous map `π : C(M, N)` over an open
subset `U` of the base is a continuous map `σ : C(U, M)` whose composite with `π` is the
inclusion `U → N`. -/
def IsLocalSection : Prop :=
  ∀ x : U, π (σ x) = x

namespace IsLocalSection

/-- A local section satisfies the section equation at each point of its open domain. -/
theorem apply_eq {π : C(M, N)} {U : Opens N} {σ : C(U, M)} (hσ : π.IsLocalSection U σ)
    (x : U) : π (σ x) = x := by
  exact hσ x

end IsLocalSection

end ContinuousMap

namespace Function.RightInverse

open ContinuousMap TopologicalSpace

variable {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]

/-- A global section restricts to a local section on the whole target. -/
theorem isLocalSection_restrict_top {π : C(M, N)} {σ : C(N, M)}
    (hσ : Function.RightInverse σ π) :
    π.IsLocalSection ⊤ (σ.restrict (⊤ : Set N)) := by
  intro x
  simpa using hσ.eq (x : N)

end Function.RightInverse
