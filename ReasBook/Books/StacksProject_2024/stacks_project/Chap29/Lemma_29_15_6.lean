import Mathlib.AlgebraicGeometry.Noetherian
import StacksProject_2024.Chap29.Definition_29_15_1

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall: `lean_leansearch` surfaced the canonical local transfer theorem
-- `LocallyOfFiniteType.isLocallyNoetherian`. Nearby Chapter 29 precedent for Lemma `29.15.5`
-- records “of finite type” on scheme morphisms through the chapter owner `Scheme.Hom.FiniteType`,
-- while Chapter 28 fixes `IsLocallyNoetherian` and `IsNoetherian` as the owner predicates for
-- Noetherian schemes. This item is therefore best exposed as an exact recall for the local
-- Noetherian transfer together with a thin source-facing bridge from `Scheme.Hom.FiniteType` to
-- `IsNoetherian`.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Lemma 29.15.6 (1): if `S` is locally Noetherian and `f : X ⟶ S` is locally of finite type,
then `X` is locally Noetherian. -/
@[stacks 01T6]
theorem isLocallyNoetherian_of_locallyOfFiniteType
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] :
    IsLocallyNoetherian X :=
  LocallyOfFiniteType.isLocallyNoetherian f

/-- Lemma 29.15.6 (2): if `S` is Noetherian and `f : X ⟶ S` is of finite type, then `X` is
Noetherian. -/
@[stacks 01T6]
theorem isNoetherian_of_finiteType [FiniteType f] [IsNoetherian S] :
    IsNoetherian X := by
  refine IsNoetherian.mk ?_ ?_
  · exact isLocallyNoetherian_of_locallyOfFiniteType f
  · exact QuasiCompact.compactSpace_of_compactSpace f

end AlgebraicGeometry.Scheme.Hom
