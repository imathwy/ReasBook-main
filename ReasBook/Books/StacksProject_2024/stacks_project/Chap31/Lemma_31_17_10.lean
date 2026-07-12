import StacksProject_2024.Chap31.Lemma_31_17_5
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import StacksProject_2024.Chap28.Definition_28_7_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/- Semantic recall: `lean_leansearch` surfaced the canonical scheme finite-morphism owner
`AlgebraicGeometry.IsFinite`; local Section 31.17 precedent uses `Scheme.IsQuasiAffine` for
quasi-affine schemes and `AlgebraicGeometry.Surjective` for surjective morphisms. As in
Proposition 31.17.9, the source phrase "finite locally free" is represented by flatness and
local finite presentation under the ambient finite hypothesis. Normality is recorded by
`Scheme.isNormal`. The Stacks tag evidence is consistent: tag `0BD5` comes from
`https://stacks.math.columbia.edu/tag/0BD5`. -/

/-- Lemma 31.17.10 (1): let `π : X ⟶ Y` be a finite surjective morphism of schemes.
If `X` is quasi-affine and `π` is finite locally free, then `Y` is quasi-affine. The finite
locally free condition is represented by flatness and local finite presentation under the ambient
finite hypothesis. -/
@[stacks 0BD5]
theorem isQuasiAffine_target_of_isFinite_surjective_flat_locallyOfFinitePresentation
    {X Y : Scheme.{u}} (π : X ⟶ Y) [IsFinite π] [Surjective π] [Flat π]
    [LocallyOfFinitePresentation π]
    (hX : X.IsQuasiAffine) :
    Y.IsQuasiAffine := sorry

/-- Lemma 31.17.10 (2): let `π : X ⟶ Y` be a finite surjective morphism of schemes.
If `X` is quasi-affine and `Y` is integral and normal, then `Y` is quasi-affine. -/
@[stacks 0BD5]
theorem isQuasiAffine_target_of_isFinite_surjective_isIntegral_isNormal
    {X Y : Scheme.{u}} (π : X ⟶ Y) [IsFinite π] [Surjective π] [IsIntegral Y]
    (hYnormal : Y.isNormal) (hX : X.IsQuasiAffine) :
    Y.IsQuasiAffine := sorry

end AlgebraicGeometry.Scheme
