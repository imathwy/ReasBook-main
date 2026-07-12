import StacksProject_2024.Chap29.Definition_29_15_1
import StacksProject_2024.Chap29.Definition_29_21_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)

-- Semantic recall / analogue check:
-- - `Definition_29_15_1.lean` records the source phrase “of finite type” for scheme morphisms as
--   `Scheme.Hom.FiniteType`, i.e. the canonical pair `QuasiCompact` and `LocallyOfFiniteType`;
-- - `Definition_29_21_1.lean` records the source phrase “of finite presentation” as
--   `Scheme.Hom.FinitePresentation`;
-- - the local-finite-type implication from local finite presentation is a pure canonical recall,
--   while the scheme-side finite-type consequence is source-facing and belongs on the local owner
--   `Scheme.Hom.FiniteType`.

/-- Lemma 29.21.8 (1): a morphism which is locally of finite presentation is locally of finite
type. This is a pure canonical recall of the existing mathlib instance. -/
theorem locallyOfFiniteType_of_locallyOfFinitePresentation
    [LocallyOfFinitePresentation f] : LocallyOfFiniteType f :=
  inferInstance

/-- A morphism of finite presentation is canonically of finite type. -/
instance instFiniteTypeOfFinitePresentation [FinitePresentation f] :
    FiniteType f :=
  { toQuasiCompact := inferInstance
    toLocallyOfFiniteType := inferInstance }

/-- Lemma 29.21.8 (2): a morphism of finite presentation is of finite type. -/
@[stacks 01TV]
theorem finiteType_of_finitePresentation [FinitePresentation f] :
    FiniteType f :=
  inferInstance

end AlgebraicGeometry.Scheme.Hom
