import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory Limits TopCat.Sheaf
open PresheafOfModules.DifferentialsConstruction

noncomputable section

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

-- Semantic recall: `lean_leansearch` surfaced the scheme diagonal immersion API, and local
-- Chapter 29 precedent fixes the source-facing differential and conormal surfaces as
-- `Ω[f.toShHom]`, `immersionConormalSheaf`, and `ShortComplex` exactness. This remark records
-- the diagonal conormal sequence after the canonical conormal-differentials identification.

/-- The commutative-ring-valued inverse-image structure-sheaf morphism associated to a scheme
map, used here to keep the differential-sheaf construction independent of a stale imported
project notation module. -/
noncomputable abbrev schemePullbackStructureSheafHomCommForDifferentials (f : X ⟶ S) :
    (TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf ⟶ X.sheaf :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).homEquiv _ _).symm
    ⟨f.c⟩

/-- The relative differential sheaf of a scheme morphism, expanded directly as the sheafification
of presheaf-level relative differentials. -/
noncomputable abbrev schemeRelativeDifferentialsForDiagonalSequence (f : X ⟶ S) :
    SheafOfModules X.ringCatSheaf :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (relativeDifferentials' (schemePullbackStructureSheafHomCommForDifferentials f).hom)

/-- Companion expansion for `schemeRelativeDifferentialsForDiagonalSequence`. -/
theorem schemeRelativeDifferentialsForDiagonalSequence_def (f : X ⟶ S) :
    schemeRelativeDifferentialsForDiagonalSequence f =
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
        (relativeDifferentials' (schemePullbackStructureSheafHomCommForDifferentials f).hom) := sorry

/-- The `(-1, 1)` map from `Ω_{X/S}` to `Ω_{X/S} ⊕ Ω_{X/S}` used after identifying the
diagonal conormal sheaf with `Ω_{X/S}`. -/
@[stacks 060N]
abbrev diagonalRelativeDifferentialsLeftMap (f : X ⟶ S) :
    schemeRelativeDifferentialsForDiagonalSequence f ⟶
      schemeRelativeDifferentialsForDiagonalSequence f ⊞
        schemeRelativeDifferentialsForDiagonalSequence f :=
  biprod.lift (-𝟙 (schemeRelativeDifferentialsForDiagonalSequence f))
    (𝟙 (schemeRelativeDifferentialsForDiagonalSequence f))

/-- The `(1, 1)` map from `Ω_{X/S} ⊕ Ω_{X/S}` to `Ω_{X/S}` in the diagonal conormal
sequence. -/
@[stacks 060N]
abbrev diagonalRelativeDifferentialsRightMap (f : X ⟶ S) :
    schemeRelativeDifferentialsForDiagonalSequence f ⊞
        schemeRelativeDifferentialsForDiagonalSequence f ⟶
      schemeRelativeDifferentialsForDiagonalSequence f :=
  biprod.desc (𝟙 (schemeRelativeDifferentialsForDiagonalSequence f))
    (𝟙 (schemeRelativeDifferentialsForDiagonalSequence f))

/-- A concrete section of the `(1, 1)` map, given by the first coproduct inclusion. -/
@[stacks 060N]
abbrev diagonalRelativeDifferentialsRightMapSection (f : X ⟶ S) :
    schemeRelativeDifferentialsForDiagonalSequence f ⟶
      schemeRelativeDifferentialsForDiagonalSequence f ⊞
        schemeRelativeDifferentialsForDiagonalSequence f :=
  biprod.inl

/-- Remark 29.32.17 (1): after using the product formula for differentials and the canonical
identification of `Ω_{X/S}` with the conormal sheaf of the diagonal, the diagonal conormal
sequence is the short exact sequence with left arrow `(-1, 1)` and right arrow `(1, 1)`. -/
@[stacks 060N]
theorem diagonalRelativeDifferentials_shortExact (f : X ⟶ S) :
    ∃ h :
      diagonalRelativeDifferentialsLeftMap f ≫ diagonalRelativeDifferentialsRightMap f = 0,
      (ShortComplex.mk
        (diagonalRelativeDifferentialsLeftMap f)
        (diagonalRelativeDifferentialsRightMap f)
        h).ShortExact := sorry

/-- Remark 29.32.17 (2): the right arrow `(1, 1)` in the diagonal conormal sequence is split by
the first coproduct inclusion. -/
@[stacks 060N]
theorem diagonalRelativeDifferentialsRightMapSection_comp (f : X ⟶ S) :
    diagonalRelativeDifferentialsRightMapSection f ≫
      diagonalRelativeDifferentialsRightMap f =
        𝟙 (schemeRelativeDifferentialsForDiagonalSequence f) := sorry

end AlgebraicGeometry
