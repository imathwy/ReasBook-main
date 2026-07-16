import Mathlib
import StacksProject_2024.stacks_project.Chap28.Definition_28_15_1
import StacksProject_2024.stacks_project.Chap29.Definition_29_45_1
import StacksProject_2024.stacks_project.Chap29.Definition_29_54_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall / local analogue check: `lean_leansearch` recalled
-- `Scheme.Hom.normalization` and `Scheme.Hom.fromNormalization`; local Chapter 29 packages the
-- source normalization morphism as `Scheme.normalizationTo` and universal homeomorphisms as
-- `UniversalHomeomorphism`. The Stacks tag evidence is consistent: item tag `0GIQ` matches
-- `https://stacks.math.columbia.edu/tag/0GIQ`.

/-- An irreducible scheme has finitely many irreducible components on each quasi-compact open,
providing the ambient finiteness hypothesis needed for `X.normalizationTo`. -/
instance instHasFiniteIrreducibleComponentsOnCompactOpensOfIrreducibleSpace
    (X : Scheme.{u}) [IrreducibleSpace X] :
    HasFiniteIrreducibleComponentsOnCompactOpens X := sorry

/-- Lemma 29.54.12: let `X` be an irreducible, geometrically unibranch scheme. The normalization
morphism `ν : X^ν ⟶ X`, formalized as `X.normalizationTo`, is a universal homeomorphism. -/
@[stacks 0GIQ]
theorem universalHomeomorphism_normalizationTo_of_irreducible_geometricallyUnibranch
    (X : Scheme.{u}) [IrreducibleSpace X]
    [QuasiCompact (genericPointSpectrumCoproductTo X)]
    [QuasiSeparated (genericPointSpectrumCoproductTo X)]
    (hX : X.isGeometricallyUnibranch) :
    UniversalHomeomorphism X.normalizationTo := sorry

end AlgebraicGeometry.Scheme
