import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_32_1
import StacksProject_2024.stacks_project.Chap29.Lemma_29_35_9

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Semantic recall / analogue check:
- `lean_leansearch` recalled the ring-level unramified/formally-unramified owners;
- local Chapter 29 precedent fixes the scheme-side owners here as `Unramified`, `GUnramified`,
  and `Ω[f.toShHom]`.
-/

variable {X S : Scheme.{u}}

/-- Lemma 29.35.2 (1): a morphism of schemes is unramified if and only if it is locally of finite
type and its sheaf of relative differentials vanishes. -/
@[stacks 02G5]
theorem unramified_iff_locallyOfFiniteType_and_isZero_relativeDifferentials
    (f : X ⟶ S) :
    Unramified f ↔
      LocallyOfFiniteType f ∧ CategoryTheory.Limits.IsZero (Ω[f.toShHom]) := sorry

/-- Lemma 29.35.2 (2): a morphism of schemes is G-unramified if and only if it is locally of
finite presentation and its sheaf of relative differentials vanishes. -/
@[stacks 02G5]
theorem gUnramified_iff_locallyOfFinitePresentation_and_isZero_relativeDifferentials
    (f : X ⟶ S) :
    GUnramified f ↔
      LocallyOfFinitePresentation f ∧ CategoryTheory.Limits.IsZero (Ω[f.toShHom]) := sorry

end AlgebraicGeometry
