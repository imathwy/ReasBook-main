import Mathlib
import stacks_proof.stacks_project.Chap15.Definition_15_92_4
import stacks_proof.stacks_project.Chap15.Lemma_15_90_1

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A]

namespace ModuleCat

local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)

/-- Helper for Lemma 15.92.3: restricting scalars carries the degree-zero localization object
`(A_f)[0]` to the degree-zero `A`-module underlying `A_f`. -/
noncomputable def restrictScalars_localizationAway_single_iso
    (f : A) :
    ((ModuleCat.restrictScalars.{u, u, u} (algebraMap A (Localization.Away f))).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u, u} (Localization.Away f)) (0 : ℤ)).obj
        (ModuleCat.of.{u, u} (Localization.Away f) (Localization.Away f)))) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u, u} A) (0 : ℤ)).obj
        (((ModuleCat.restrictScalars.{u, u, u} (algebraMap A (Localization.Away f))).obj
          (ModuleCat.of.{u, u} (Localization.Away f) (Localization.Away f)))) := by
  -- Proof comment: normalize the restricted degree-zero object through `Q` and the standard
  -- single-complex compatibility isomorphisms.
  exact
    (((ModuleCat.restrictScalars.{u, u, u} (algebraMap A (Localization.Away f))).mapDerivedCategory).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ
        (ModuleCat.{u, u} (Localization.Away f)) (0 : ℤ)).app
          (ModuleCat.of.{u, u} (Localization.Away f) (Localization.Away f)))) ≪≫
    (ModuleCat.restrictScalars.{u, u, u} (algebraMap A (Localization.Away f))).mapDerivedCategoryFactors.app
      ((CochainComplex.singleFunctor (ModuleCat.{u, u} (Localization.Away f)) (0 : ℤ)).obj
        (ModuleCat.of.{u, u} (Localization.Away f) (Localization.Away f))) ≪≫
    DerivedCategory.Q.mapIso
      ((CategoryTheory.Functor.mapCochainComplexSingleFunctor
        (ModuleCat.restrictScalars.{u, u, u} (algebraMap A (Localization.Away f)))
        (0 : ℤ)).app (ModuleCat.of.{u, u} (Localization.Away f) (Localization.Away f)))

/-- Helper for Lemma 15.92.3: the degree-zero localization-away vanishing condition forces every
`A`-linear map `A_f → M` to vanish. -/
lemma subsingleton_linearMap_from_localizationAway_of_localizationAwayDerivedHomVanishingCondition
    (f : A) (M : ModuleCat.{u, u} A)
    (hvanish : CategoryTheory.DerivedCategory.localizationAwayDerivedHomVanishingCondition f
      ((single₀).obj M)) :
    Subsingleton (Localization.Away f →ₗ[A] M) := by
  -- Route correction: isolate the persistent `A_f[0]` transport in this helper file and reuse
  -- the stabilized proof shape from the later chapter file instead of repeating it inline.
  let singleA := DerivedCategory.singleFunctor (ModuleCat.{u, u} A) (0 : ℤ)
  let singleAway := DerivedCategory.singleFunctor (ModuleCat.{u, u} (Localization.Away f)) (0 : ℤ)
  let source : ModuleCat.{u, u} A :=
    ((ModuleCat.restrictScalars.{u, u, u} (algebraMap A (Localization.Away f))).obj
      (ModuleCat.of.{u, u} (Localization.Away f) (Localization.Away f)))
  let sourceIso :
      ((ModuleCat.restrictScalars.{u, u, u} (algebraMap A (Localization.Away f))).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u, u} (Localization.Away f)) (0 : ℤ)).obj
          (ModuleCat.of.{u, u} (Localization.Away f) (Localization.Away f)))) ≅
      singleA.obj source :=
    restrictScalars_localizationAway_single_iso (A := A) f
  have hDerived :
      Subsingleton ((singleA.obj source) ⟶ singleA.obj M) := by
    let E := singleAway.obj (ModuleCat.of.{u, u} (Localization.Away f) (Localization.Away f))
    have hE :
        Subsingleton
          (((ModuleCat.restrictScalars.{u, u, u} (algebraMap A (Localization.Away f))).mapDerivedCategory.obj
            E) ⟶ singleA.obj M) :=
      hvanish E
    letI := hE
    -- Proof comment: `homCongr` transports the subsingleton hom-space across the source
    -- isomorphism, so the target proof never has to elaborate this transport again.
    let e :
        (((ModuleCat.restrictScalars.{u, u, u} (algebraMap A (Localization.Away f))).mapDerivedCategory.obj
          E) ⟶ singleA.obj M) ≃ ((singleA.obj source) ⟶ singleA.obj M) :=
      sourceIso.homCongr (CategoryTheory.eqToIso rfl)
    exact e.symm.injective.subsingleton
  let hFaithful : singleA.Faithful := inferInstance
  have hSource : Subsingleton (source ⟶ M) := by
    letI := hDerived
    refine ⟨fun φ ψ ↦ ?_⟩
    -- Proof comment: faithfulness of `single₀` descends the derived-category subsingleton to
    -- ordinary module morphisms out of the restricted source module.
    exact hFaithful.map_injective (Subsingleton.elim _ _)
  let eLinear : source ≃ₗ[A] Localization.Away f :=
    restrictScalars_selfLinearEquiv (A := A) (B := Localization.Away f)
  let eSource : source ≅ ModuleCat.of A (Localization.Away f) := eLinear.toModuleIso
  have hCanonical : Subsingleton (ModuleCat.of A (Localization.Away f) ⟶ M) := by
    letI := hSource
    -- Proof comment: transport the subsingleton from the restricted-source model to the
    -- canonical localization owner.
    let e : (source ⟶ M) ≃ (ModuleCat.of A (Localization.Away f) ⟶ M) :=
      eSource.homCongr (CategoryTheory.eqToIso rfl)
    exact e.symm.injective.subsingleton
  letI := hCanonical
  refine ⟨fun φ ψ ↦ ?_⟩
  -- Proof comment: once the canonical source hom-set is subsingleton, equality of the original
  -- linear maps follows from injectivity of `ModuleCat.ofHom` on the underlying map.
  have hEqCanonical : ModuleCat.ofHom φ = ModuleCat.ofHom ψ := Subsingleton.elim _ _
  simpa using congrArg ModuleCat.Hom.hom hEqCanonical

end ModuleCat

end
