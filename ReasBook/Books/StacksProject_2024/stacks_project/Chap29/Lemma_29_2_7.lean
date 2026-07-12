import StacksProject_2024.Chap26.Lemma_26_23_3

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry

/- Semantic recall / owner check:
Local chapter precedent identifies the canonical separatedness owner as
`AlgebraicGeometry.IsSeparated`, and the reusable bridge for this source-facing statement is the
canonical mathlib instance `AlgebraicGeometry.IsSeparated.isSeparated_of_mono` together with the
monomorphism instance attached to closed immersions. -/

/-- Lemma 29.2.7: a closed immersion is separated. -/
@[stacks 01KV]
theorem closedImmersion_isSeparated
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] :
    IsSeparated f := by
  let _ : Mono f := inferInstance
  exact IsSeparated.isSeparated_of_mono

end AlgebraicGeometry
