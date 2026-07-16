import StacksProject_2024.stacks_project.Chap32.Lemma_32_17_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` returned the canonical properness owner `IsProper` and
-- `isProper_iff`; local Chapter 32 precedent supplies the Nagata-base valuative existence and
-- uniqueness predicates used here as the source-facing exact-unique dotted-arrow condition.

/-- Lemma 32.17.3: let `S` be a Nagata scheme and let `f : X ⟶ Y` be a quasi-compact morphism
of schemes locally of finite type over `S`. Then `f` is proper if and only if the Nagata-base
one-dimensional normal-curve valuative test has a unique dotted lift. -/
@[stacks 0GWX]
theorem isProper_iff_nagataCurveValuativeExistsUnique
    {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S) (f : X ⟶ Y)
    [Scheme.Nagata S] [QuasiCompact f] [LocallyOfFiniteType pX] [LocallyOfFiniteType pY]
    (hf_over : f ≫ pY = pX) :
    IsProper f ↔
      NagataCurveValuativeExistence pX pY f ∧
        NagataCurveValuativeUniqueness pX pY f := sorry

end AlgebraicGeometry
