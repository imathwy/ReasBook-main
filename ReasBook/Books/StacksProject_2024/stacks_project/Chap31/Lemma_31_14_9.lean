import StacksProject_2024.stacks_project.Chap31.Definition_31_13_1
import StacksProject_2024.stacks_project.Chap31.Definition_31_14_6
import StacksProject_2024.stacks_project.Chap31.Definition_31_14_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced mathlib's generic zero-locus API, while local
-- Chapter 31 precedent fixes the source-facing owner for this item as `Scheme.zeroIdealSheaf` /
-- `Scheme.zeroScheme`; the canonical pullback-of-sections owner is
-- `LocallyRingedSpace.Hom.pullbackSections`, while local principality/effective-Cartier
-- assertions are expressed on the canonical closed-immersion owner attached to `zeroIdealSheaf`.

variable {X Y Z : Scheme.{u}}

open CategoryTheory.MonoidalCategory

local notation "ModX" => Scheme.Modules X
local notation "IsInvertibleX" =>
  (fun ℒ : ModX ↦ Functor.IsEquivalence (tensorRight ℒ))

variable [MonoidalCategory ModX]

/-- Internal shorthand for the zero section of a pulled-back invertible sheaf. -/
local abbrev pullbackZeroSection (f : Y ⟶ X) (ℒ : ModX) [IsInvertibleX ℒ] :
    ((Scheme.Modules.pullback f).obj ℒ).sections :=
  (((Scheme.Modules.pullback f).obj ℒ).unitHomEquiv 0)

/-- Canonical bridge for Lemma 31.14.9: the pullback of `s` along `f` vanishes exactly when the
zero ideal sheaf of `s` is contained in the kernel ideal sheaf of `f`. This is the ideal-sheaf
form of factorization through the closed subscheme `Z(s)`. -/
theorem pullbackSections_eq_zero_iff_zeroIdealSheaf_le_ker
    (ℒ : ModX) [IsInvertibleX ℒ] (s : ℒ.sections)
    (f : Y ⟶ X) :
    Scheme.pullbackSections f s = pullbackZeroSection f ℒ ↔
      zeroIdealSheaf ℒ s ≤ Scheme.Hom.ker f := sorry

/-- Lemma 31.14.9 (1): if a closed immersion `i : Z ⟶ X` pulls the section `s` of the invertible
sheaf `\mathcal L` back to zero, then `i` factors through the zero scheme `Z(s)`. This is the
maximality statement for the zero scheme among closed immersions on which `s` vanishes. -/
@[stacks 0C6I]
theorem exists_factorization_zeroScheme_of_pullbackSections_eq_zero
    (ℒ : ModX) [IsInvertibleX ℒ] (s : ℒ.sections)
    (i : Z ⟶ X)
    (hzero : Scheme.pullbackSections i s = pullbackZeroSection i ℒ) :
    ∃ g : Z ⟶ zeroScheme ℒ s, g ≫ zeroSchemeι ℒ s = i := sorry

/-- Lemma 31.14.9 (2): for any morphism of schemes `f : Y ⟶ X`, the pulled-back section `f^*s`
vanishes if and only if `f` factors through the zero scheme `Z(s)`. -/
@[stacks 0C6I]
theorem pullbackSections_eq_zero_iff_exists_factorization_zeroScheme
    (ℒ : ModX) [IsInvertibleX ℒ] (s : ℒ.sections)
    (f : Y ⟶ X) :
    Scheme.pullbackSections f s = pullbackZeroSection f ℒ ↔
      ∃ g : Y ⟶ zeroScheme ℒ s, g ≫ zeroSchemeι ℒ s = f := sorry

/-- Lemma 31.14.9 (3): the zero scheme `Z(s)` is a locally principal closed subscheme. In the
closed-immersion owner used in this chapter, this is the local-principality statement for the
canonical inclusion `Z(s) ⟶ X`. -/
@[stacks 0C6I]
theorem zeroScheme_isLocallyPrincipalClosedSubscheme
    (ℒ : ModX) [IsInvertibleX ℒ] (s : ℒ.sections) :
    IsLocallyPrincipalClosedSubscheme (zeroSchemeι ℒ s) := sorry

/-- Lemma 31.14.9 (4): the canonical inclusion `Z(s) ⟶ X` of the zero scheme of `s` is an
effective Cartier divisor if and only if the section `s` of `\mathcal L` is regular. The
chapter's regular-section owner is `LocallyRingedSpace.IsRegularSection`, whose companion theorem
identifies this with the associated morphism `\mathcal O_X \to \mathcal L` being a monomorphism.
-/
@[stacks 0C6I]
theorem zeroScheme_isEffectiveCartierDivisor_iff_isRegularSection
    (ℒ : ModX) [IsInvertibleX ℒ] (s : ℒ.sections) :
    AlgebraicGeometry.IsEffectiveCartierDivisor (zeroSchemeι ℒ s) ↔
      LocallyRingedSpace.IsRegularSection ℒ s := sorry

end AlgebraicGeometry.Scheme
