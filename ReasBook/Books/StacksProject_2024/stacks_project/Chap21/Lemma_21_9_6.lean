import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap12.Lemma_12_7_2
import StacksProject_2024.stacks_project.Chap13.Definition_13_16_2
import StacksProject_2024.stacks_project.Chap13.Lemma_13_11_6
import StacksProject_2024.stacks_project.Chap13.Lemma_13_16_6
import StacksProject_2024.stacks_project.Chap21.Lemma_21_9_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits
open DerivedCategory.TStructure
open ComplexShape

noncomputable section

universe w v u

namespace CategoryTheory

/-
Domain-style sampling for Lemma 21.9.6:
- primary domain: Čech cohomology on abelian presheaves, viewed as a cohomological `δ`-functor and
  compared with higher right derived functors and with the corresponding injective-resolution
  complex models;
- sampled owner declarations:
  `cechCohomologyDeltaFunctor`,
  `CohomologicalDeltaFunctor.IsUniversal`,
  `CohomologicalDeltaFunctor.universal_delta_functor_unique_up_to_unique_iso`,
  `Functor.toBoundedBelowRightDerivedZero`,
  `boundedBelowRightDerivedDeltaFunctor`,
  `CategoryTheory.InjectiveResolution.isoRightDerivedObj`;
- best owner abstractions: the source-facing owner `cechCohomologyDeltaFunctor U family` for the
  Čech package, together with the canonical owners `CohomologicalDeltaFunctor.IsUniversal`,
  `boundedBelowRightDerivedDeltaFunctor`, and `InjectiveResolution.isoRightDerivedObj` for the
  universality, `δ`-functor comparison, and injective-resolution comparison;
- primitive data: the covering family `family : ι → Over U`, the degree-zero owner
  `(cechCohomologyDegree U family 0).obj`, and an injective resolution `I : InjectiveResolution F`;
- derived API: the universality statement, the `δ`-functor isomorphism to a bounded-below
  right-derived model of Čech `H⁰`, the degreewise right-derived comparison, the Čech-complex
  quasi-isomorphism, and direct reuse of `InjectiveResolution.isoRightDerivedObj` for the
  injective-resolution homology computation.

Source/core/bridge triage:
- `source-facing`: the three Stacks statements collected in Lemma 21.9.6;
- `core/canonical`: `CohomologicalDeltaFunctor.IsUniversal`,
  `boundedBelowRightDerivedDeltaFunctor`, `Functor.rightDerived`, and
  `InjectiveResolution.isoRightDerivedObj`;
- `bridge/view`: the comparison from the source-facing Čech `δ`-functor to a bounded-below
  right-derived model of Čech `H⁰`, together with the injective-resolution complex model
  computing the same derived value.
-/

attribute [local instance] HasDerivedCategory.standard
section

variable {C : Type u} [Category.{v} C]
variable (U : C) [Limits.HasFiniteProducts (Over U)]
variable {ι : Type (max u v)} (family : ι → Over U)
variable [HasProducts AddCommGrpCat]
variable [HasDerivedCategory.{w} (Cᵒᵖ ⥤ AddCommGrpCat)] [HasDerivedCategory.{w} AddCommGrpCat]

-- Proof sketch: Lemma `21.9.2` gives the cohomological `δ`-functor structure on Čech
-- cohomology. For an injective abelian presheaf `I`, Lemmas `21.9.3` and `21.9.4` identify the
-- Čech complex with a Hom complex out of an exact positive-degree resolution, so
-- Čech cohomology vanishes in positive degree on `I`. Thus the positive degrees are weakly
-- effaceable, and Lemma `12.12.4` implies universality.
/-- Lemma 21.9.6 (1): the Čech cohomology functors attached to `family` form a universal
cohomological `δ`-functor on abelian presheaves on `C`. -/
@[stacks 03AU, instance]
instance cechCohomologyDeltaFunctor_isUniversal :
    (cechCohomologyDeltaFunctor U family).IsUniversal := sorry

end

section BoundedBelowComparison

variable {C : Type u} [Category.{v} C]
variable (U : C) [Limits.HasFiniteProducts (Over U)]
variable {ι : Type (max u v)} (family : ι → Over U)
variable [HasProducts AddCommGrpCat]
variable [HasDerivedCategory.{w} (Cᵒᵖ ⥤ AddCommGrpCat)] [HasDerivedCategory.{w} AddCommGrpCat]
variable [(mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 (Cᵒᵖ ⥤ AddCommGrpCat))).IsLocalization
  (boundedBelowHomotopyQuasiIso (Cᵒᵖ ⥤ AddCommGrpCat))]

instance cechCohomologyDegreeZero_preservesFiniteLimits :
    PreservesFiniteLimits
      (((cechCohomologyDegree U family 0).obj) :
        (Cᵒᵖ ⥤ AddCommGrpCat) ⥤ AddCommGrpCat) := by
  let F0 :
      (Cᵒᵖ ⥤ AddCommGrpCat) ⥤ AddCommGrpCat :=
    (cechCohomologyDegree U family 0).obj
  exact (F0.preservesFiniteLimits_iff_forall_exact_map_and_mono).2 fun S hS ↦ by
    refine ⟨?_, ?_⟩
    · change (S.map ((cechCohomologyDeltaFunctor U family 0).obj)).Exact
      exact (cechCohomologyDeltaFunctor U family).map_exact hS 0
    · change Mono (((cechCohomologyDeltaFunctor U family 0).obj).map S.f)
      exact (cechCohomologyDeltaFunctor U family).mono_map_f_zero hS

-- Proof sketch: part `(1)` makes the Čech package a universal cohomological `δ`-functor. If
-- `RF` is any bounded-below right derived model of Čech `H⁰(𝒰, -)`, then the
-- degree-zero comparison from Čech `H⁰` to `H⁰(RF(-[0]))` is the canonical
-- `Functor.toBoundedBelowRightDerivedZero`. The left exactness of Čech `H⁰` is an internal
-- consequence of the Čech cohomological `δ`-functor package, so this degree-zero comparison is an
-- isomorphism. Lemma `12.12.5` then yields the unique isomorphism of `δ`-functors.
/-- Lemma 21.9.6 (2), source-facing `δ`-functor comparison: for any bounded-below right derived
model `RF` of Čech `H⁰(𝒰, -)` whose associated cohomological `δ`-functor is
universal, the Čech cohomology `δ`-functor is canonically isomorphic to that right-derived
`δ`-functor. -/
@[stacks 03AU]
theorem cechCohomologyDeltaFunctor_existsUnique_iso_to_boundedBelowRightDerived
    (RF : D⁺((Cᵒᵖ ⥤ AddCommGrpCat)) ⥤ D⁺(AddCommGrpCat))
    [RF.CommShift ℤ] [RF.IsTriangulated]
    (α :
      mapBoundedBelowHomotopyCategoryToDerivedBelow
          ((cechCohomologyDegree U family 0).obj) ⟶
        mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 (Cᵒᵖ ⥤ AddCommGrpCat)) ⋙ RF)
    [RF.IsRightDerivedFunctor α (boundedBelowHomotopyQuasiIso (Cᵒᵖ ⥤ AddCommGrpCat))]
    [CohomologicalDeltaFunctor.IsUniversal (boundedBelowRightDerivedDeltaFunctor RF)] :
    ∃! e :
      cechCohomologyDeltaFunctor U family ≅
        boundedBelowRightDerivedDeltaFunctor RF,
      e.hom.app 0 ≫
          (eqToIso (boundedBelowRightDerivedDeltaFunctor_obj RF 0)).hom =
        ((cechCohomologyDegree U family 0).obj).toBoundedBelowRightDerivedZero RF α := by
  let t := ((cechCohomologyDegree U family 0).obj).toBoundedBelowRightDerivedZero RF α
  let h0 := boundedBelowRightDerivedDeltaFunctor_obj RF 0
  letI : IsIso t :=
    (isIso_toBoundedBelowRightDerivedZero_iff_preservesFiniteLimits
      ((cechCohomologyDegree U family 0).obj) RF α).2 inferInstance
  let e0 :
      ((boundedBelowRightDerivedDeltaFunctor RF 0).obj) ≅
        ((cechCohomologyDegree U family 0).obj) :=
    (eqToIso h0) ≪≫ (asIso t).symm
  rcases
      (CohomologicalDeltaFunctor.universal_delta_functor_unique_up_to_unique_iso
      ((cechCohomologyDegree U family 0).obj)
      (inferInstance :
        CohomologicalDeltaFunctor.IsUniversal (cechCohomologyDeltaFunctor U family))
      (inferInstance :
        CohomologicalDeltaFunctor.IsUniversal (boundedBelowRightDerivedDeltaFunctor RF))
      (Iso.refl ((cechCohomologyDegree U family 0).obj))
      e0) with
    ⟨e, he, huniq⟩
  refine ⟨e, ?_, ?_⟩
  · simpa [t, h0, e0, Category.assoc] using
      congrArg (fun k ↦ k ≫ (eqToIso h0).hom) he
  · intro e' he'
    apply huniq
    calc
      e'.hom.app 0 = e'.hom.app 0 ≫ (eqToIso h0).hom ≫ (eqToIso h0).inv := by
        simp
      _ = t ≫ (eqToIso h0).inv := by
        simpa [t, Category.assoc] using
          congrArg (fun k ↦ k ≫ (eqToIso h0).inv) he'

end BoundedBelowComparison

section

variable {C : Type u} [Category.{v} C]
variable (U : C) [Limits.HasFiniteProducts (Over U)]
variable {ι : Type (max u v)} (family : ι → Over U)
variable [HasProducts AddCommGrpCat]
variable [HasDerivedCategory.{w} (Cᵒᵖ ⥤ AddCommGrpCat)] [HasDerivedCategory.{w} AddCommGrpCat]

variable [HasInjectiveResolutions (Cᵒᵖ ⥤ AddCommGrpCat)]

-- Proof sketch: the degree-zero term of the universal `δ`-functor is Čech `H⁰`, while
-- part (1) shows that Čech cohomology is itself universal. Lemma `13.20.4` gives the universal
-- `δ`-functor built from the higher right derived functors of Čech `H⁰`, and Lemma `12.12.5`
-- identifies the two universal `δ`-functors uniquely. In positive degree this yields the stated
-- canonical functor isomorphism.
/-- Lemma 21.9.6 (2): for each `p`, the higher Čech cohomology functor
`H⁽p+1⁾` of the Čech covering is canonically isomorphic to the `(p + 1)`-st right derived
functor of Čech `H⁰(𝒰, -)`. This is the degreewise companion to the `δ`-functor
comparison above. -/
@[stacks 03AU]
theorem higherCechCohomologyFunctor_isomorphic_rightDerived (p : ℕ) :
    IsIsomorphic ((cechCohomologyDegree U family (p + 1)).obj)
      (((cechCohomologyDegree U family 0).obj).rightDerived (p + 1)) := sorry

-- Proof sketch: fix an injective resolution `I` of `F`, form the double complex whose
-- `q`-th column is the Čech complex of the `q`-th injective term, and compare both
-- the Čech cochain complex of `F` and the complex computing the right derived value of Čech
-- `H⁰(𝒰, F)` to the corresponding total complex using Lemma `12.25.4`. This
-- gives the source functorial quasi-isomorphism to the injective-resolution model built from `I`.
/-- Lemma 21.9.6 (3), source-facing complex comparison: for an abelian presheaf `F`, there
exists a quasi-isomorphism from the Čech complex on `F` to the cochain complex obtained by
applying Čech `H⁰(𝒰, -)` termwise to an injective resolution `I` of `F`. -/
@[stacks 03AU]
theorem cechComplex_exists_quasiIso_to_injectiveResolutionCechH0
    (F : Cᵒᵖ ⥤ AddCommGrpCat) (I : InjectiveResolution F) :
    ∃ φ :
      (cechComplexOnPresheaves U family).obj F ⟶
        ((((cechCohomologyDegree U family 0).obj).mapHomologicalComplex (up ℕ)).obj
          I.cocomplex),
      QuasiIso φ := sorry

omit [HasDerivedCategory (Cᵒᵖ ⥤ AddCommGrpCat)] [HasDerivedCategory AddCommGrpCat] in
/-- Lemma 21.9.6 (3), homology companion: for an abelian presheaf `F`, the complex obtained by
applying Čech `H⁰(𝒰, -)` termwise to an injective resolution `I` computes the `p`-th right
derived functor of Čech `H⁰(𝒰, -)` at `F`. -/
@[stacks 03AU]
theorem rightDerivedCechH0_obj_isomorphic_to_homology_of_injectiveResolution
    (F : Cᵒᵖ ⥤ AddCommGrpCat) (I : InjectiveResolution F) (p : ℕ) :
    IsIsomorphic ((((cechCohomologyDegree U family 0).obj).rightDerived p).obj F)
      ((HomologicalComplex.homologyFunctor AddCommGrpCat (up ℕ) p).obj
        ((((cechCohomologyDegree U family 0).obj).mapHomologicalComplex (up ℕ)).obj
          I.cocomplex)) :=
  ⟨I.isoRightDerivedObj ((cechCohomologyDegree U family 0).obj) p⟩

/- The right derived functors of Čech `H⁰(𝒰, -)` are computed by applying Čech `H⁰(𝒰, -)`
termwise to an injective resolution. This is direct canonical reuse of
`InjectiveResolution.isoRightDerivedObj`. -/
recall CategoryTheory.InjectiveResolution.isoRightDerivedObj

end

end CategoryTheory
