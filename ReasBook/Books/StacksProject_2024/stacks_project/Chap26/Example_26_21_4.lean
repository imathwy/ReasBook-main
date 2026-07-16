import Mathlib
import StacksProject_2024.stacks_project.Chap26.Example_26_19_6

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry PrimeSpectrum

namespace AlgebraicGeometry

noncomputable section

universe u

variable (k : Type u) [Field k]

-- Semantic recall: `lean_leansearch` surfaced the canonical morphism owner
-- `AlgebraicGeometry.QuasiSeparated` and its diagonal quasi-compactness API
-- `AlgebraicGeometry.QuasiSeparated.quasiCompact_diagonal`. Local Chapter 26 precedent supplies
-- the punctured infinite affine spectrum as `infiniteAffinePuncture`.

/-- The base affine scheme `Spec(k)` in the infinite doubled-origin example. -/
@[stacks 01KL]
abbrev infiniteAffineSpaceWithZeroDoubledBase : Scheme.{u} :=
  Spec (CommRingCat.of k)

/-- The common overlap identified with the punctured infinite affine spectrum is not compact. -/
@[stacks 01KL]
theorem infiniteAffineSpaceWithZeroDoubled_overlap_notIsCompact
    {X : Scheme.{u}} (X1 X2 : X.Opens)
    (overlapIso : (X1 ⊓ X2).toScheme ≅ (infiniteAffinePuncture k).toScheme) :
    ¬ IsCompact ((X1 ⊓ X2 : X.Opens) : Set X) := sorry

/-- Example 26.21.4: the morphism `X -> Spec(k)` obtained by gluing two copies of
`Spec(k[t_1, t_2, t_3, ...])` along the punctured affine spectrum is not quasi-separated. The
obstruction is that the inverse image under the diagonal of the mixed affine chart
`X_1 ×_S X_2` is the punctured infinite affine spectrum, which is not quasi-compact. -/
@[stacks 01KL]
theorem infiniteAffineSpaceWithZeroDoubled_toBase_not_quasiSeparated
    {X : Scheme.{u}} (f : X ⟶ infiniteAffineSpaceWithZeroDoubledBase k)
    (X1 X2 : X.Opens)
    (hcover : X1 ⊔ X2 = ⊤)
    (hX1 : IsAffineOpen X1) (hX2 : IsAffineOpen X2)
    (chart1Iso : X1.toScheme ≅ infiniteAffineSpectrum k)
    (chart2Iso : X2.toScheme ≅ infiniteAffineSpectrum k)
    (overlapIso : (X1 ⊓ X2).toScheme ≅ (infiniteAffinePuncture k).toScheme) :
    ¬ QuasiSeparated f := sorry

end

end AlgebraicGeometry
