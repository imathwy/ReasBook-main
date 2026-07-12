import StacksProject_2024.Chap13.Definition_13_16_2
import StacksProject_2024.Chap13.Lemma_13_16_6
import StacksProject_2024.Chap20.Lemma_20_10_2
import StacksProject_2024.Chap20.OpensInstances

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CategoryTheory.CohomologicalDeltaFunctor
open CategoryTheory.Limits
open ComplexShape
open DerivedCategory.TStructure

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow_isLocalization

/-
Domain-style sampling for Lemma 20.10.5:
- primary domain: cohomological `δ`-functors and right derived functors for Čech cohomology on
  presheaf modules over a ringed space;
- sampled owner declarations:
  `CohomologicalDeltaFunctor.IsUniversal`,
  `Functor.rightDerived`,
  `Functor.isZero_rightDerived_obj_injective_succ`,
  `InjectiveResolution.isoRightDerivedObj`;
- best owner abstractions:
  `CohomologicalDeltaFunctor.IsUniversal` for universality, `Functor.rightDerived` for the higher
  derived comparison, and `InjectiveResolution.isoRightDerivedObj` for the injective-resolution
  computation;
- primitive data vs derived API:
  the primitive data in this file are the degreewise Čech cohomology functors together with the
  canonical owner `ringedSpaceCechCohomologyDeltaFunctor U 𝒰` from `Lemma_20.10.2`; the
  degree-zero term is not a separate owner and the right-derived comparison statements are
  derived API built from the canonical owners above rather than from a chosen-resolution wrapper.

Source/core/bridge triage:
- `source-facing`: the three textbook consequences for Čech cohomology in Lemma `20.10.5`;
- `core/canonical`: `CohomologicalDeltaFunctor.IsUniversal`, `Functor.rightDerived`, and
  `InjectiveResolution.isoRightDerivedObj`;
- `bridge/view`: the specialization of those owners to the Čech cohomology `δ`-functor of the
  cover `𝒰`, expressed through `ringedSpaceCechCohomologyDeltaFunctor U 𝒰`.
-/

variable {X : RingedSpace.{u}}
variable (U : Opens X.carrier) {ι : Type u} (𝒰 : ι → Over U)

local notation "ModU" => ModuleCat (X.presheaf.obj (op U))
local notation "PModX" => RingedSpace.PresheafModules X

/-- Lemma 20.10.5 (1): the Čech cohomology `δ`-functor of the covering `𝒰` is universal on
presheaves of `𝒪_X`-modules. -/
@[stacks 01EN]
theorem ringedSpaceCechCohomologyDeltaFunctor_isUniversal :
    CohomologicalDeltaFunctor.IsUniversal (ringedSpaceCechCohomologyDeltaFunctor U 𝒰) := by
  sorry

section BoundedBelowComparison

-- Proof sketch: use part `(1)` to extend the canonical degree-zero comparison
-- `ringedSpaceCechCohomologyDegree U 𝒰 0 ⟶ RF.boundedBelowRightDerived 0`, formalized as
-- `Functor.toBoundedBelowRightDerivedZero`, and then rewrite its codomain along
-- `boundedBelowRightDerivedDeltaFunctor_obj` to obtain a degree-zero comparison into the
-- bounded-below right-derived `δ`-functor itself.

/-- The degree-zero comparison from Čech `H⁰` to a bounded-below right derived functor model,
rewritten so that its codomain is the degree-zero branch of
`boundedBelowRightDerivedDeltaFunctor RF`. -/
noncomputable def ringedSpaceCechCohomologyNatTrans_toBoundedBelowRightDerivedZero
    (RF : D⁺(PModX) ⥤ D⁺(ModU))
    [RF.CommShift ℤ] [RF.IsTriangulated]
    [(mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 PModX)).IsLocalization
      (boundedBelowHomotopyQuasiIso PModX)]
    (α :
        mapBoundedBelowHomotopyCategoryToDerivedBelow
          (ringedSpaceCechCohomologyDegree U 𝒰 0).obj ⟶
        mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 PModX) ⋙ RF)
    [RF.IsRightDerivedFunctor α (boundedBelowHomotopyQuasiIso PModX)] :
    ((ringedSpaceCechCohomologyDeltaFunctor U 𝒰 0).obj) ⟶
      ((boundedBelowRightDerivedDeltaFunctor RF 0).obj) :=
  (ringedSpaceCechCohomologyDegree U 𝒰 0).obj.toBoundedBelowRightDerivedZero RF α ≫
    eqToHom (boundedBelowRightDerivedDeltaFunctor_obj RF 0).symm

@[simp, reassoc] theorem
    ringedSpaceCechCohomologyNatTrans_toBoundedBelowRightDerivedZero_comp_hom
    (RF : D⁺(PModX) ⥤ D⁺(ModU))
    [RF.CommShift ℤ] [RF.IsTriangulated]
    [(mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 PModX)).IsLocalization
      (boundedBelowHomotopyQuasiIso PModX)]
    (α :
        mapBoundedBelowHomotopyCategoryToDerivedBelow
          (ringedSpaceCechCohomologyDegree U 𝒰 0).obj ⟶
        mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 PModX) ⋙ RF)
    [RF.IsRightDerivedFunctor α (boundedBelowHomotopyQuasiIso PModX)] :
    ringedSpaceCechCohomologyNatTrans_toBoundedBelowRightDerivedZero U 𝒰 RF α ≫
        (eqToIso (boundedBelowRightDerivedDeltaFunctor_obj RF 0)).hom =
      (ringedSpaceCechCohomologyDegree U 𝒰 0).obj.toBoundedBelowRightDerivedZero RF α := by
  simp [ringedSpaceCechCohomologyNatTrans_toBoundedBelowRightDerivedZero]

/-- Lemma 20.10.5, source-facing `δ`-functor comparison: for any bounded-below right derived
model `RF` of `ringedSpaceCechCohomologyDegree U 𝒰 0` whose associated cohomological
`δ`-functor is universal, the degree-zero comparison extends uniquely from
`ringedSpaceCechCohomologyDeltaFunctor U 𝒰` to that right-derived `δ`-functor. The source-facing
degree-zero comparison is the named bridge
`ringedSpaceCechCohomologyNatTrans_toBoundedBelowRightDerivedZero U 𝒰 RF α`. -/
@[stacks 01EN]
theorem ringedSpaceCechCohomologyDeltaFunctor_existsUnique_hom_to_boundedBelowRightDerived
    (RF : D⁺(PModX) ⥤ D⁺(ModU))
    [RF.CommShift ℤ] [RF.IsTriangulated]
    [(mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 PModX)).IsLocalization
      (boundedBelowHomotopyQuasiIso PModX)]
    (α :
        mapBoundedBelowHomotopyCategoryToDerivedBelow
          (ringedSpaceCechCohomologyDegree U 𝒰 0).obj ⟶
        mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 PModX) ⋙ RF)
    [RF.IsRightDerivedFunctor α (boundedBelowHomotopyQuasiIso PModX)]
    [CohomologicalDeltaFunctor.IsUniversal (boundedBelowRightDerivedDeltaFunctor RF)] :
    ∃! τ : ringedSpaceCechCohomologyDeltaFunctor U 𝒰 ⟶
        boundedBelowRightDerivedDeltaFunctor RF,
      τ.app 0 =
        ringedSpaceCechCohomologyNatTrans_toBoundedBelowRightDerivedZero U 𝒰 RF α := by
  exact
    (ringedSpaceCechCohomologyDeltaFunctor_isUniversal U 𝒰).existsUnique_hom
      (boundedBelowRightDerivedDeltaFunctor RF)
      (ringedSpaceCechCohomologyNatTrans_toBoundedBelowRightDerivedZero U 𝒰 RF α)

end BoundedBelowComparison

section

-- Proof sketch: the degree-zero term of the universal `δ`-functor is Čech `H^0`, while part
-- `(1)` shows that Čech cohomology is itself universal. Lemma `13.20.4` gives the universal
-- `δ`-functor built from the higher right derived functors of Čech `H^0`, and Lemma `12.12.5`
-- identifies the two universal `δ`-functors uniquely. The theorem below records the resulting
-- degreewise canonical isomorphism in positive degree.
/-- Lemma 20.10.5 (2): for each `p`, the degree-`p + 1` Čech cohomology functor of the cover `𝒰`
is canonically isomorphic to the `(p + 1)`-st right derived functor of the degree-zero Čech
cohomology functor. This is the degreewise companion to the `δ`-functor comparison above. -/
@[stacks 01EN]
theorem ringedSpaceHigherCechCohomologyFunctor_isomorphic_rightDerived
    (p : ℕ) [HasInjectiveResolutions PModX] :
    IsIsomorphic (ringedSpaceCechCohomologyDegree U 𝒰 (p + 1)).obj
      ((ringedSpaceCechCohomologyDegree U 𝒰 0).obj.rightDerived (p + 1)) := by
  sorry

-- Proof sketch: for any injective resolution `I` of `ℱ`, form the double complex whose `q`-th
-- column is the Čech complex of the `q`-th injective term, and compare both the Čech complex of
-- `ℱ` and the complex computing the right-derived Čech `H^0` of `ℱ` to the corresponding total
-- complex using Lemma `12.25.4`. The injective-resolution complex on the right computes the
-- derived value by the standard `InjectiveResolution.isoRightDerivedObj` comparison.
/-- Lemma 20.10.5 (3), source-facing complex comparison: for a presheaf `ℱ` of `𝒪_X`-modules and
an injective resolution `I`, there exists a quasi-isomorphism from the Čech complex of `ℱ` for
the cover `𝒰` to the cochain complex obtained by applying the degree-zero Čech cohomology functor
termwise to `I`. This is the explicit complex model for the source quasi-isomorphism from the
Čech complex of `ℱ` to the right-derived Čech `H^0` of `ℱ`. -/
@[stacks 01EN]
theorem ringedSpaceCechComplex_exists_quasiIso_to_injectiveResolutionCechH0
    (ℱ : PModX) (I : InjectiveResolution ℱ) :
    ∃ φ :
      (ringedSpaceModuleCechComplexFunctor U 𝒰).obj ℱ ⟶
        (((ringedSpaceCechCohomologyDegree U 𝒰 0).obj.mapHomologicalComplex
            (ComplexShape.up ℕ)).obj I.cocomplex),
      QuasiIso φ := sorry

/-- Lemma 20.10.5 (3), canonical isomorphism companion: for a presheaf `ℱ` of `𝒪_X`-modules, the
complex obtained by applying degree-zero Čech cohomology termwise to an injective resolution of
`ℱ` computes the right derived functors of the degree-zero Čech cohomology functor at `ℱ`. -/
@[stacks 01EN]
noncomputable def ringedSpaceRightDerivedCechH0_objIsoHomologyOfInjectiveResolution
    (ℱ : PModX) (I : InjectiveResolution ℱ) (p : ℕ) [HasInjectiveResolutions PModX] :
    (((ringedSpaceCechCohomologyDegree U 𝒰 0).obj.rightDerived p).obj ℱ) ≅
      ((HomologicalComplex.homologyFunctor
          ModU
          (ComplexShape.up ℕ) p).obj
        (((ringedSpaceCechCohomologyDegree U 𝒰 0).obj.mapHomologicalComplex
            (ComplexShape.up ℕ)).obj I.cocomplex)) :=
  I.isoRightDerivedObj (ringedSpaceCechCohomologyDegree U 𝒰 0).obj p

/-- Lemma 20.10.5 (3), homology companion: for a presheaf `ℱ` of `𝒪_X`-modules, the complex
obtained by applying degree-zero Čech cohomology termwise to an injective resolution of `ℱ`
computes the right derived functors of the degree-zero Čech cohomology functor at `ℱ`. -/
@[stacks 01EN]
theorem ringedSpaceRightDerivedCechH0_obj_isomorphic_to_homology_of_injectiveResolution
    (ℱ : PModX) (I : InjectiveResolution ℱ) (p : ℕ) [HasInjectiveResolutions PModX] :
    IsIsomorphic
      (((ringedSpaceCechCohomologyDegree U 𝒰 0).obj.rightDerived p).obj ℱ)
      ((HomologicalComplex.homologyFunctor
          ModU
          (ComplexShape.up ℕ) p).obj
        (((ringedSpaceCechCohomologyDegree U 𝒰 0).obj.mapHomologicalComplex
            (ComplexShape.up ℕ)).obj I.cocomplex)) := by
  exact ⟨ringedSpaceRightDerivedCechH0_objIsoHomologyOfInjectiveResolution U 𝒰 ℱ I p⟩

end

end AlgebraicGeometry.RingedSpace
