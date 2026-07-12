import StacksProject_2024.Chap29.Lemma_29_31_3
import StacksProject_2024.Chap31.Definition_31_31_6

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

-- Source/core/bridge triage:
-- - source-facing: Lemma 31.31.6 on sections of a projective bundle and the quotient data they
--   determine;
-- - core/canonical: `IsProjectiveBundle.liftEquiv` / `projectiveBundleLiftEquivQuotient`;
-- - bridge/view: the identity-base specialization used for actual sections `X ⟶ P`.

variable {X P : Scheme.{u}} {ℰ : X.Modules}

/-- The tensor product `\ker(q) \otimes \mathcal L^{\otimes -1}` attached to a quotient
`q : \mathcal F \twoheadrightarrow \mathcal L`, modeled using the internal-Hom inverse of the
invertible quotient module. -/
noncomputable def projectiveBundleQuotientConormalModule
    {T : Scheme.{u}} [MonoidalCategory T.Modules] [SymmetricCategory T.Modules]
    [MonoidalClosed T.Modules] [HasZeroMorphisms T.Modules] [HasKernels T.Modules]
    {ℱ : T.Modules} (q : ProjectiveBundleQuotient ℱ) : T.Modules :=
  tensorObj (kernel q.hom) ((ihom q.module).obj (SheafOfModules.unit T.ringCatSheaf : T.Modules))

/-- Lemma 31.31.6 (1): let `X` be a scheme and let `ℰ` be a quasi-coherent
`\mathcal O_X`-module. For a projective bundle morphism `π : P ⟶ X` attached to `ℰ`, the sections
of `π` are in bijection with surjections `ℰ ⟶ \mathcal L` where `\mathcal L` is an invertible
`\mathcal O_X`-module. This is the identity-base specialization of
`projectiveBundleLiftEquivQuotient`. -/
abbrev projectiveBundleSectionsEquivQuotient
    [MonoidalCategory X.Modules]
    (π : P ⟶ X) [IsProjectiveBundle π ℰ] :
    ProjectiveBundleLifts π (𝟙 X) ≃ ProjectiveBundleQuotient ℰ :=
  projectiveBundleLiftEquivQuotient (T := X) (ℰ := ℰ) (π := π) (𝟙 X)

/-- The quotient attached to a section of a projective bundle through the identity-base
specialization of the universal quotient correspondence. -/
abbrev projectiveBundleSectionQuotient
    [MonoidalCategory X.Modules]
    (π : P ⟶ X) [IsProjectiveBundle π ℰ]
    (σ : ProjectiveBundleLifts π (𝟙 X)) :
    ProjectiveBundleQuotient ℰ :=
  projectiveBundleSectionsEquivQuotient π σ

/-- Lemma 31.31.6 (2): under the section-quotient correspondence for a projective bundle, every
section `σ : X ⟶ P` is a closed immersion. -/
theorem projectiveBundleSection_isClosedImmersion
    [MonoidalCategory X.Modules]
    (π : P ⟶ X) [IsProjectiveBundle π ℰ]
    (σ : ProjectiveBundleLifts π (𝟙 X)) :
    IsClosedImmersion σ.1 := sorry

section Conormal

variable [HasWeakSheafify (Opens.grothendieckTopology ↥X) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥X) CommRingCat.{u}]
variable [(Opens.grothendieckTopology ↥X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [(Opens.grothendieckTopology ↥X).HasSheafCompose
  (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology ↥X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasBinaryCoproducts (Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u})]

/-- Lemma 31.31.6 (3): if a section `σ : X ⟶ P` corresponds to a quotient
`q : ℰ ⟶ \mathcal L`, then the kernel of `q`, tensored with the internal-Hom model of
`\mathcal L^{\otimes -1}`, is canonically isomorphic to the conormal sheaf of `σ(X)` in `P`. -/
theorem projectiveBundleSectionConormalIso
    [MonoidalCategory X.Modules] [SymmetricCategory X.Modules] [MonoidalClosed X.Modules]
    [HasZeroMorphisms X.Modules] [HasKernels X.Modules]
    (π : P ⟶ X) [IsProjectiveBundle π ℰ]
    (σ : ProjectiveBundleLifts π (𝟙 X))
    :
    projectiveBundleQuotientConormalModule (projectiveBundleSectionQuotient π σ) ≅
      immersionConormalSheaf σ.1 := sorry

/-- Lemma 31.31.6 (3), equality-form companion: if a section `σ : X ⟶ P` corresponds to a
quotient `q : ℰ ⟶ \mathcal L`, then the conormal comparison for the canonical quotient attached
to `σ` transports along `q`. -/
theorem projectiveBundleSectionConormalIso_of_eq
    [MonoidalCategory X.Modules] [SymmetricCategory X.Modules] [MonoidalClosed X.Modules]
    [HasZeroMorphisms X.Modules] [HasKernels X.Modules]
    (π : P ⟶ X) [IsProjectiveBundle π ℰ]
    (σ : ProjectiveBundleLifts π (𝟙 X))
    (q : ProjectiveBundleQuotient ℰ)
    (hσq : projectiveBundleSectionQuotient π σ = q) :
    projectiveBundleQuotientConormalModule q ≅ immersionConormalSheaf σ.1 := sorry

end Conormal

end AlgebraicGeometry.Scheme
