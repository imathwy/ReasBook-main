import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.CategoryTheory.Limits.IsLimit

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the affine-transition scheme-limit API and the
-- finite-type morphism owners `QuasiCompact` and `LocallyOfFiniteType`. Local Chapter 32 precedent
-- represents inverse limits by scheme diagrams with explicit transition maps; here the
-- source-facing relative system is a natural transformation between two such diagrams together
-- with the structure morphisms to `Spec ℤ`.
-- The Stacks source tag evidence is consistent with tag `0GS1`.

/-- Stage and transition properties for a relative Noetherian approximation system over `Spec ℤ`. -/
@[stacks 0GS1]
structure RelativeNoetherianApproximationSystem {I : Type u} [Preorder I]
    (Xsys Ssys : OrderDual I ⥤ Scheme) (φ : Xsys ⟶ Ssys)
    (xToSpec : ∀ i : I, Xsys.obj i ⟶ Spec (CommRingCat.of ℤ))
    (sToSpec : ∀ i : I, Ssys.obj i ⟶ Spec (CommRingCat.of ℤ)) : Prop where
  /-- Source transition maps are affine. -/
  sourceTransitionAffine : ∀ ⦃i i' : I⦄ (hii' : i ≤ i'),
    IsAffineHom (Xsys.map (homOfLE hii'))
  /-- Target transition maps are affine. -/
  targetTransitionAffine : ∀ ⦃i i' : I⦄ (hii' : i ≤ i'),
    IsAffineHom (Ssys.map (homOfLE hii'))
  /-- Source transition maps commute with the structure maps to `Spec ℤ`. -/
  sourceTransition_overSpec : ∀ ⦃i i' : I⦄ (hii' : i ≤ i'),
    Xsys.map (homOfLE hii') ≫ xToSpec i = xToSpec i'
  /-- Target transition maps commute with the structure maps to `Spec ℤ`. -/
  targetTransition_overSpec : ∀ ⦃i i' : I⦄ (hii' : i ≤ i'),
    Ssys.map (homOfLE hii') ≫ sToSpec i = sToSpec i'
  /-- The stage morphisms are morphisms over `Spec ℤ`. -/
  stageMap_overSpec : ∀ i : I, φ.app i ≫ sToSpec i = xToSpec i
  /-- Source stages are quasi-compact over `Spec ℤ`. -/
  sourceStageQuasiCompact : ∀ i : I, QuasiCompact (xToSpec i)
  /-- Source stages are locally of finite type over `Spec ℤ`. -/
  sourceStageLocallyOfFiniteType : ∀ i : I, LocallyOfFiniteType (xToSpec i)
  /-- Target stages are quasi-compact over `Spec ℤ`. -/
  targetStageQuasiCompact : ∀ i : I, QuasiCompact (sToSpec i)
  /-- Target stages are locally of finite type over `Spec ℤ`. -/
  targetStageLocallyOfFiniteType : ∀ i : I, LocallyOfFiniteType (sToSpec i)

/-- Lemma 32.7.1: let `f : X ⟶ S` be a morphism of quasi-compact and quasi-separated schemes.
Then `f` is the inverse limit of a directed system of morphisms `X_i ⟶ S_i`, with affine
transition morphisms on both source and target, and with each `X_i` and `S_i` of finite type
over `ℤ`. -/
@[stacks 0GS1]
theorem exists_relativeNoetherianApproximation
    {X S : Scheme} (f : X ⟶ S) [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace S] [QuasiSeparatedSpace S] :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (Xsys Ssys : OrderDual I ⥤ Scheme) (φ : Xsys ⟶ Ssys)
      (xToSpec : ∀ i : I, Xsys.obj i ⟶ Spec (CommRingCat.of ℤ))
      (sToSpec : ∀ i : I, Ssys.obj i ⟶ Spec (CommRingCat.of ℤ))
      (cX : Cone Xsys) (cS : Cone Ssys)
      (hcX : IsLimit cX) (hcS : IsLimit cS) (eX : X ≅ cX.pt) (eS : S ≅ cS.pt),
        (∀ i : I, eX.hom ≫ cX.π.app i ≫ φ.app i = f ≫ eS.hom ≫ cS.π.app i) ∧
          RelativeNoetherianApproximationSystem Xsys Ssys φ xToSpec sToSpec := sorry

end AlgebraicGeometry
