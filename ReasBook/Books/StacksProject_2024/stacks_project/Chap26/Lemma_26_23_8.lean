import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Separated

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

namespace AlgebraicGeometry

universe u

-- Source/core/bridge triage:
-- - source-facing: the two scheme-theoretic consequences recorded in Stacks Lemma 26.23.8.
-- - core/canonical: the ambient `IsPreimmersion → Mono` instance inherited by immersions and
--   `IsSeparated.isSeparated_of_mono`.
-- - bridge/view: none beyond these direct owner-side consequences.

variable {X Y : Scheme.{u}}

/-- Lemma 26.23.8 (1): an immersion of schemes is a monomorphism. -/
@[stacks 01L7]
theorem Scheme.Hom.mono_of_isImmersion (j : X ⟶ Y) [IsImmersion j] :
    Mono j :=
  inferInstance

/-- Lemma 26.23.8 (2): in particular, an immersion of schemes is separated. -/
@[stacks 01L7]
theorem Scheme.Hom.isSeparated_of_isImmersion (j : X ⟶ Y) [IsImmersion j] :
    IsSeparated j := by
  let _ : Mono j := j.mono_of_isImmersion
  exact IsSeparated.isSeparated_of_mono

end AlgebraicGeometry
