import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Homology.Augment
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.AlgebraicTopology.CechNerve
import StacksProject_2024.Chap10.Lemma_10_24_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open AlgebraicTopology

universe u v

/-
Domain-style sampling for the extended alternating Čech complex:
- owner abstraction: `extendedAlternatingCechComplex`
- same-domain declarations inspected:
  `awayLocalizationFamilyMap`
  `Arrow.augmentedCechConerve`
  `alternatingCofaceMapComplex`
  `CochainComplex.fromSingle₀AsComplex`

Layer triage:
- `source-facing`: the extended alternating Čech complex of a finite family `f` and an `R`-module
  `M`
- `core/canonical`: the ordinary alternating Čech complex obtained from the Čech conerve of the
  canonical localization-family map, then extended in degree `0` by
  `CochainComplex.fromSingle₀AsComplex`
- `bridge/view`: the degree-zero augmentation map from `M` into the ordinary alternating Čech
  complex

Primitive data is only the canonical localization-family map `awayLocalizationFamilyMap M f`.
The ordinary alternating Čech complex, its augmentation, and the extended complex are derived
from that owner construction; the finite-subset indexing, sign bookkeeping, and entrywise
differentials should therefore not remain primitive public data here.
-/

section

variable {R : Type u} [CommRing R]
variable {r : ℕ}

/-- The ordinary alternating Čech complex of `M` attached to the family `f`. -/
abbrev alternatingCechComplex (f : Fin r → R) (M : Type (max u v))
    [AddCommGroup M] [Module R M] :
    CochainComplex (ModuleCat.{max u v} R) ℕ :=
  (alternatingCofaceMapComplex (ModuleCat.{max u v} R)).obj
    ((Arrow.mk (ModuleCat.ofHom (awayLocalizationFamilyMap M f))).cechConerve)

/-- The degree-zero augmentation map from `M` to the ordinary alternating Čech complex. -/
abbrev alternatingCechComplexAugmentationMap (f : Fin r → R) (M : Type (max u v))
    [AddCommGroup M] [Module R M] :
    ModuleCat.of R M ⟶ (alternatingCechComplex f M).X 0 :=
  (Arrow.mk (ModuleCat.ofHom (awayLocalizationFamilyMap M f))).augmentedCechConerve.hom.app
    (SimplexCategory.mk 0)

/-- Helper for Lemma 15.29.1: in degree `0`, the alternating Čech differential is the
alternating sum of the two coface maps. -/
lemma alternatingCechComplex_d_zero_one_eq
    (f : Fin r → R) (M : Type (max u v)) [AddCommGroup M] [Module R M] :
    (alternatingCechComplex f M).d 0 1 =
      ((Arrow.mk (ModuleCat.ofHom (awayLocalizationFamilyMap M f))).cechConerve).δ 0 -
        ((Arrow.mk (ModuleCat.ofHom (awayLocalizationFamilyMap M f))).cechConerve).δ 1 := by
  let δ₀ : (alternatingCechComplex f M).X 0 ⟶ (alternatingCechComplex f M).X 1 :=
    ((Arrow.mk (ModuleCat.ofHom (awayLocalizationFamilyMap M f))).cechConerve).δ 0
  let δ₁ : (alternatingCechComplex f M).X 0 ⟶ (alternatingCechComplex f M).X 1 :=
    ((Arrow.mk (ModuleCat.ofHom (awayLocalizationFamilyMap M f))).cechConerve).δ 1
  -- Expose the standard alternating-coface differential and evaluate the two-term sum.
  rw [show (alternatingCechComplex f M).d 0 1 = AlgebraicTopology.AlternatingCofaceMapComplex.objD
      ((Arrow.mk (ModuleCat.ofHom (awayLocalizationFamilyMap M f))).cechConerve) 0 by
      rfl]
  rw [AlgebraicTopology.AlternatingCofaceMapComplex.objD, Fin.sum_univ_two]
  change (-1 : ℤ) ^ (0 : ℕ) • δ₀ + (-1 : ℤ) ^ (1 : ℕ) • δ₁ = δ₀ - δ₁
  norm_num
  rw [sub_eq_add_neg]

/-- Helper for Lemma 15.29.1: composing the augmentation with the first coface gives the
degree-one augmentation component. -/
lemma alternatingCechComplexAugmentationMap_comp_coface_zero
    (f : Fin r → R) (M : Type (max u v)) [AddCommGroup M] [Module R M] :
    alternatingCechComplexAugmentationMap f M ≫
      ((Arrow.mk (ModuleCat.ofHom (awayLocalizationFamilyMap M f))).cechConerve).δ 0 =
        (Arrow.mk (ModuleCat.ofHom (awayLocalizationFamilyMap M f))).augmentedCechConerve.hom.app
          (SimplexCategory.mk 1) := by
  -- Naturality of the augmentation identifies the composite with the degree-one component.
  simpa using
    ((Arrow.mk (ModuleCat.ofHom (awayLocalizationFamilyMap M f))).augmentedCechConerve.hom.naturality
      (SimplexCategory.δ 0)).symm

/-- Helper for Lemma 15.29.1: composing the augmentation with the second coface also gives the
degree-one augmentation component. -/
lemma alternatingCechComplexAugmentationMap_comp_coface_one
    (f : Fin r → R) (M : Type (max u v)) [AddCommGroup M] [Module R M] :
    alternatingCechComplexAugmentationMap f M ≫
      ((Arrow.mk (ModuleCat.ofHom (awayLocalizationFamilyMap M f))).cechConerve).δ 1 =
        (Arrow.mk (ModuleCat.ofHom (awayLocalizationFamilyMap M f))).augmentedCechConerve.hom.app
          (SimplexCategory.mk 1) := by
  -- The same naturality argument applies to the second coface.
  simpa using
    ((Arrow.mk (ModuleCat.ofHom (awayLocalizationFamilyMap M f))).augmentedCechConerve.hom.naturality
      (SimplexCategory.δ 1)).symm

-- Proof sketch: the two degree-zero coface maps are induced by the same localization-family map,
-- so their alternating sum vanishes after precomposition with the augmentation map.
/-- The degree-zero augmentation map is a cocycle for the ordinary alternating Čech complex. -/
theorem alternatingCechComplexAugmentationMap_comp_d_zero_one
    (f : Fin r → R) (M : Type (max u v)) [AddCommGroup M] [Module R M] :
    alternatingCechComplexAugmentationMap f M ≫ (alternatingCechComplex f M).d 0 1 = 0 := by
  let α : ModuleCat.of R M ⟶ (alternatingCechComplex f M).X 0 := alternatingCechComplexAugmentationMap f M
  let δ₀ : (alternatingCechComplex f M).X 0 ⟶ (alternatingCechComplex f M).X 1 :=
    ((Arrow.mk (ModuleCat.ofHom (awayLocalizationFamilyMap M f))).cechConerve).δ 0
  let δ₁ : (alternatingCechComplex f M).X 0 ⟶ (alternatingCechComplex f M).X 1 :=
    ((Arrow.mk (ModuleCat.ofHom (awayLocalizationFamilyMap M f))).cechConerve).δ 1
  -- Rewrite the first differential as the alternating sum of the two cofaces.
  rw [alternatingCechComplex_d_zero_one_eq]
  change α ≫ (δ₀ - δ₁) = 0
  calc
    α ≫ (δ₀ - δ₁) = α ≫ δ₀ - α ≫ δ₁ := by
      -- Composition distributes over subtraction in any preadditive category.
      exact CategoryTheory.Preadditive.comp_sub _ _ _
    _ = 0 := by
      -- Each coface composite is the same degree-one augmentation component.
      rw [show α ≫ δ₀ =
          (Arrow.mk (ModuleCat.ofHom (awayLocalizationFamilyMap M f))).augmentedCechConerve.hom.app
            (SimplexCategory.mk 1) by
          simpa [α, δ₀] using alternatingCechComplexAugmentationMap_comp_coface_zero f M]
      rw [show α ≫ δ₁ =
          (Arrow.mk (ModuleCat.ofHom (awayLocalizationFamilyMap M f))).augmentedCechConerve.hom.app
            (SimplexCategory.mk 1) by
          simpa [α, δ₁] using alternatingCechComplexAugmentationMap_comp_coface_one f M]
      simpa using sub_self
        ((Arrow.mk (ModuleCat.ofHom (awayLocalizationFamilyMap M f))).augmentedCechConerve.hom.app
          (SimplexCategory.mk 1))

/-- The augmentation from `M` to the ordinary alternating Čech complex of `f`. -/
abbrev alternatingCechComplexAugmentation (f : Fin r → R) (M : Type (max u v))
    [AddCommGroup M] [Module R M] :
    (CochainComplex.single₀ (ModuleCat.{max u v} R)).obj (ModuleCat.of R M) ⟶
      alternatingCechComplex f M :=
  (CochainComplex.fromSingle₀Equiv (alternatingCechComplex f M) (ModuleCat.of R M)).symm
    ⟨alternatingCechComplexAugmentationMap f M,
      alternatingCechComplexAugmentationMap_comp_d_zero_one f M⟩

/-- Lemma 15.29.1: the extended alternating Čech complex attached to a finite family
`f : Fin r → R` and an `R`-module `M`, obtained by adjoining the canonical degree-zero
augmentation to the ordinary alternating Čech complex. The ring-valued extended alternating Čech
complex is the special case `M = R`. -/
def extendedAlternatingCechComplex (f : Fin r → R) (M : Type (max u v))
    [AddCommGroup M] [Module R M] :
    CochainComplex (ModuleCat.{max u v} R) ℕ :=
  CochainComplex.fromSingle₀AsComplex (alternatingCechComplex f M) (ModuleCat.of R M)
    (alternatingCechComplexAugmentation f M)

end
