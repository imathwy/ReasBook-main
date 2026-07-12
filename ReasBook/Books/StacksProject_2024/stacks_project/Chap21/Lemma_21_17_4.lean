import StacksProject_2024.Chap15.Definition_15_59_1
import StacksProject_2024.Chap15.Lemma_15_59_3
import StacksProject_2024.Chap18.Lemma_18_19_2
import Mathlib.CategoryTheory.Limits.Preserves.Finite

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [CategoryTheory.Limits.HasBinaryProducts C]
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

local notation "Mod" => ringedSiteModuleCategory J 𝒪

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]

variable (U : C)

local notation "ModU" => ringedSiteModuleCategory (J.over U) (𝒪.over U)

variable [MonoidalCategory (ringedSiteModuleCategory (J.over U) (𝒪.over U))]
variable [MonoidalPreadditive (ringedSiteModuleCategory (J.over U) (𝒪.over U))]

omit [CategoryTheory.Limits.HasBinaryProducts C]
  [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
  [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]
  [MonoidalCategory (ringedSiteModuleCategory (J.over U) (𝒪.over U))]
  [MonoidalPreadditive (ringedSiteModuleCategory (J.over U) (𝒪.over U))] in
/-- Helper for Lemma 21.17.4: localized restriction of a cochain complex is computed degreewise. -/
private theorem localizedRestrictionComplexObjX
    (K : CochainComplex Mod ℤ) (n : ℤ) :
    ((((ringedSiteLocalizedRestriction J 𝒪 U).mapHomologicalComplex (up ℤ)).obj K).X n) =
      (ringedSiteLocalizedRestriction J 𝒪 U).obj (K.X n) := by
  -- Proof comment: `mapHomologicalComplex` applies the functor termwise, so the `X n` field is
  -- definitionally the restricted degree-`n` module.
  rfl

omit [CategoryTheory.Limits.HasBinaryProducts C]
  [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
  [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]
  [MonoidalCategory (ringedSiteModuleCategory (J.over U) (𝒪.over U))]
  [MonoidalPreadditive (ringedSiteModuleCategory (J.over U) (𝒪.over U))] in
/-- Helper for Lemma 21.17.4: localized restriction sends each differential of a cochain complex
to the corresponding restricted differential. -/
private theorem localizedRestrictionComplexObjD
    (K : CochainComplex Mod ℤ) (i j : ℤ) :
    ((((ringedSiteLocalizedRestriction J 𝒪 U).mapHomologicalComplex (up ℤ)).obj K).d i j) =
      (ringedSiteLocalizedRestriction J 𝒪 U).map (K.d i j) := by
  -- Proof comment: `mapHomologicalComplex` also applies the functor to each differential, so the
  -- differential field is definitionally the image of the original differential.
  rfl

omit [CategoryTheory.Limits.HasBinaryProducts C]
  [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
  [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]
  [MonoidalCategory (ringedSiteModuleCategory (J.over U) (𝒪.over U))]
  [MonoidalPreadditive (ringedSiteModuleCategory (J.over U) (𝒪.over U))] in
/-- Helper for Lemma 21.17.4: localized restriction sends each component of a cochain map to the
corresponding restricted map. -/
private theorem localizedRestrictionComplexMapF
    {K L : CochainComplex Mod ℤ} (f : K ⟶ L) (n : ℤ) :
    ((((ringedSiteLocalizedRestriction J 𝒪 U).mapHomologicalComplex (up ℤ)).map f).f n) =
      (ringedSiteLocalizedRestriction J 𝒪 U).map (f.f n) := by
  -- Proof comment: cochain-map components are also mapped degreewise by
  -- `mapHomologicalComplex`.
  rfl

/-- Helper for Lemma 21.17.4: acyclicity transports across an isomorphism of cochain complexes. -/
private theorem acyclicOfIso
    {A : Type*} [Category A] [CategoryTheory.Limits.HasZeroMorphisms A]
    {K L : CochainComplex A ℤ}
    (e : K ≅ L) (hK : K.Acyclic) :
    L.Acyclic := by
  -- Proof comment: exactness at each degree is invariant under complex isomorphism.
  rw [HomologicalComplex.acyclic_iff] at hK ⊢
  intro n
  exact HomologicalComplex.ExactAt.of_iso (hK n) e

/-- Helper for Lemma 21.17.4: after forgetting module structure, localized extension by zero is
the additive-sheaf pushforward along `Over.star U`. -/
private theorem localizedExtensionByZeroCompToSheaf
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}] :
    ringedSiteLocalizedExtensionByZero J 𝒪 U ⋙
        SheafOfModules.toSheaf (ringSheaf J 𝒪) =
      SheafOfModules.toSheaf (ringSheaf (J.over U) (𝒪.over U)) ⋙
        (Over.star U).sheafPushforwardContinuous AddCommGrpCat.{max u v} J (J.over U) := by
  -- Proof comment: the localized module pushforward is definitionally the additive-sheaf
  -- pushforward after forgetting the module structure.
  rfl

/-- Helper for Lemma 21.17.4: localized extension by zero of a cochain complex is computed
degreewise on objects. -/
private theorem localizedExtensionByZeroComplexObjX
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (L : CochainComplex ModU ℤ) (n : ℤ) :
    ((((ringedSiteLocalizedExtensionByZero J 𝒪 U).mapHomologicalComplex (up ℤ)).obj L).X n) =
      (ringedSiteLocalizedExtensionByZero J 𝒪 U).obj (L.X n) := by
  -- Proof comment: `mapHomologicalComplex` applies localized extension by zero termwise, so the
  -- degree-`n` object is definitionally the pushforward of `L.X n`.
  rfl

/-- Helper for Lemma 21.17.4: localized extension by zero sends each differential of a cochain
complex to the corresponding pushed-forward differential. -/
private theorem localizedExtensionByZeroComplexObjD
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (L : CochainComplex ModU ℤ) (i j : ℤ) :
    ((((ringedSiteLocalizedExtensionByZero J 𝒪 U).mapHomologicalComplex (up ℤ)).obj L).d i j) =
      (ringedSiteLocalizedExtensionByZero J 𝒪 U).map (L.d i j) := by
  -- Proof comment: the differentials are also mapped degreewise by `mapHomologicalComplex`.
  rfl

/-- Helper for Lemma 21.17.4: localized extension by zero sends each component of a cochain map
to the corresponding pushed-forward map. -/
private theorem localizedExtensionByZeroComplexMapF
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    {L M : CochainComplex ModU ℤ} (f : L ⟶ M) (n : ℤ) :
    ((((ringedSiteLocalizedExtensionByZero J 𝒪 U).mapHomologicalComplex (up ℤ)).map f).f n) =
      (ringedSiteLocalizedExtensionByZero J 𝒪 U).map (f.f n) := by
  -- Proof comment: cochain-map components are also mapped degreewise by
  -- `mapHomologicalComplex`.
  rfl

/-- Helper for Lemma 21.17.4: localized extension by zero sends acyclic cochain complexes to
acyclic cochain complexes. -/
private theorem localizedExtensionByZeroAcyclic
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (L : CochainComplex ModU ℤ) (hL : L.Acyclic) :
    (((ringedSiteLocalizedExtensionByZero J 𝒪 U).mapHomologicalComplex (up ℤ)).obj L).Acyclic := by
  -- TODO: the stable next step is a dependency-closed degreewise exactness bridge for localized
  -- extension by zero, obtained by combining `localizedExtensionByZeroCompToSheaf`,
  -- `localizedExtensionByZeroComplexObjX`, `localizedExtensionByZeroComplexObjD`,
  -- `localizedExtensionByZeroComplexMapF`, the exact additive pushforward route, and
  -- `ShortComplex.exact_map_iff_of_faithful`.
  sorry

/-- Helper for Lemma 21.17.4: once localized extension by zero reflects acyclicity and provides
the mixed tensor comparison, ambient K-flatness descends to the localized restriction. -/
private theorem isKFlat_localizedRestriction_from_helpers
    (K : CochainComplex Mod ℤ) (hK : K.IsKFlat) :
    (((ringedSiteLocalizedRestriction J 𝒪 U).mapHomologicalComplex (up ℤ)).obj K).IsKFlat := by
  -- Proof comment: test localized K-flatness against an arbitrary acyclic localized complex.
  change CochainComplex.IsKFlat
    (((ringedSiteLocalizedRestriction J 𝒪 U).mapHomologicalComplex (up ℤ)).obj K)
  rw [CochainComplex.isKFlat_iff]
  intro L _ hL
  have hPushL :
      (((ringedSiteLocalizedExtensionByZero J 𝒪 U).mapHomologicalComplex (up ℤ)).obj L).Acyclic :=
    localizedExtensionByZeroAcyclic (J := J) (𝒪 := 𝒪) (U := U) L hL
  -- Proof comment: the remaining helper should combine ambient K-flatness with the localized
  -- tensor comparison to descend acyclicity to the localized tensor complex.
  have hLocalizedTensor :
      (HomologicalComplex.tensorObj L
        (((ringedSiteLocalizedRestriction J 𝒪 U).mapHomologicalComplex (up ℤ)).obj K)).Acyclic := by
    -- TODO: combine ambient K-flatness of `K`, the mixed tensor comparison coming from the
    -- localized adjunction, and the still-missing acyclicity reflection for localized extension
    -- by zero to descend acyclicity to the localized tensor test complex.
    sorry
  exact hLocalizedTensor

/-- Lemma 21.17.4: if `K^•` is a K-flat complex of `𝒪`-modules on a ringed site and `U : C`,
then the restricted complex `K^•|_U` is K-flat over `𝒪_U`. -/
@[stacks 0E8K]
theorem isKFlat_localizedRestriction
    (K : CochainComplex Mod ℤ) (hK : K.IsKFlat) :
    (((ringedSiteLocalizedRestriction J 𝒪 U).mapHomologicalComplex (up ℤ)).obj K).IsKFlat := by
  -- Route correction: the proof is now factored so the main theorem uses only the textbook
  -- lower-shriek skeleton. The remaining blockers are isolated as two owner-level helpers:
  -- acyclicity reflection for localized extension by zero and the mixed tensor comparison after
  -- pushing forward.
  exact isKFlat_localizedRestriction_from_helpers
    (J := J) (𝒪 := 𝒪) (U := U) K hK

end SheafOfModules.RingedSite
