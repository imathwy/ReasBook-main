import Mathlib.AlgebraicGeometry.Noetherian
import StacksProject_2024.stacks_project.Chap28.Lemma_28_5_3

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Semantic recall / source-core-bridge triage:
- `source-facing`: Lemma 28.5.6 records the standard transfer facts for locally closed
  subschemes, i.e. immersions of schemes.
- `core/canonical`: mathlib already supplies these transfer facts canonically through typeclass
  search on the scheme predicates `IsLocallyNoetherian` and `IsNoetherian`.
- `bridge/view`: the source statements therefore stay as thin source-facing wrappers around those
  canonical owners. The Noetherian clause uses the canonical `IsNoetherian.mk` constructor
  together with the Chapter 28 quasi-compactness transfer owner
  `quasiCompact_of_isImmersion_of_isLocallyNoetherian`.
-/

/- Lemma 28.5.6 (1): any locally closed subscheme of a locally Noetherian scheme is locally
Noetherian. Formally, a locally closed subscheme is represented by an immersion `f : X ⟶ Y`. -/
@[stacks 01P6]
theorem IsLocallyNoetherian.of_isImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsImmersion f] [IsLocallyNoetherian Y] :
    IsLocallyNoetherian X :=
  LocallyOfFiniteType.isLocallyNoetherian f

/- Lemma 28.5.6 (2): any locally closed subscheme of a Noetherian scheme is Noetherian.
Formally, a locally closed subscheme is represented by an immersion `f : X ⟶ Y`. -/
@[stacks 01P6]
theorem IsNoetherian.of_isImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsImmersion f] [IsNoetherian Y] :
    IsNoetherian X := by
  let _ : QuasiCompact f := quasiCompact_of_isImmersion_of_isLocallyNoetherian (f := f)
  refine IsNoetherian.mk ?_ ?_
  · exact IsLocallyNoetherian.of_isImmersion f
  · exact QuasiCompact.compactSpace_of_compactSpace f

end AlgebraicGeometry
