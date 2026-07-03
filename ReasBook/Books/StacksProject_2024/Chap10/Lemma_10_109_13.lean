import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap10.Definition_10_109_10

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open CategoryTheory
open TensorProduct

variable {R : Type u} [CommRing R]

/- The helper localization bound on projective dimension is the canonical mathlib theorem
`ModuleCat.localizedModule_hasProjectiveDimensionLE`. -/
recall ModuleCat.localizedModule_hasProjectiveDimensionLE

/-
Source/core/bridge triage:
- `source-facing`: a localization of a ring of global dimension at most `n` again has global
  dimension at most `n`;
- `core/canonical`: the chapter owner `HasGlobalDimensionLE R n`;
- `bridge/view`: restriction of scalars to `R`, localization back along `S`, and the canonical
  tensor-product identification
  `LocalizedModule.equivTensorProduct ≪≫ₗ IsLocalization.moduleLid`.

Primitive data is the owner bound `HasGlobalDimensionLE R n`. The explicit quantifier form is only
the source-facing companion, while the owner instance remains the main public interface.
-/

/- Lemma 10.109.13: a localization of a ring of global dimension at most `n` again has global
dimension at most `n`. -/
-- Proof sketch: restrict a `Localization S`-module to an `R`-module, apply the projective-
-- dimension bound over `R`, and identify the resulting localized module with the original module
-- by passing through `Localization S ⊗[R] M`.
/-- Source-facing companion to `localization_hasGlobalDimensionLE`: if every `R`-module has
projective dimension at most `n`, then every `Localization S`-module has projective dimension at
most `n`. -/
theorem localization_has_finite_global_dimension_le (n : ℕ) (S : Submonoid R)
    (hR : ∀ M : ModuleCat.{u} R, HasProjectiveDimensionLE M n)
    (M : ModuleCat.{u} (Localization S)) : HasProjectiveDimensionLE M n := by
  letI : Small.{u} (Localization S) := small_of_surjective Localization.mkHom_surjective
  letI : Module R (↑M) := Module.compHom (↑M) (algebraMap R (Localization S))
  letI : IsScalarTower R (Localization S) (↑M) := by
    refine ⟨?_⟩
    intro r s m
    simpa [Algebra.smul_def] using (smul_assoc ((algebraMap R (Localization S)) r) s m)
  let M₀ : ModuleCat.{u} R := (ModuleCat.restrictScalars (algebraMap R (Localization S))).obj M
  letI : IsScalarTower R (Localization S) (↑M₀) := by
    refine ⟨?_⟩
    intro r s m
    simpa [Algebra.smul_def] using (smul_assoc ((algebraMap R (Localization S)) r) s m)
  letI : Small.{u} (LocalizedModule S (↑M₀)) :=
    small_of_surjective (IsLocalizedModule.mk'_surjective S (LocalizedModule.mkLinearMap S (↑M₀)))
  let hM : HasProjectiveDimensionLE (M₀.localizedModule S) n :=
    ModuleCat.localizedModule_hasProjectiveDimensionLE n S M₀
  let e : (M₀.localizedModule S) ≃ₗ[Localization S] M :=
    (Shrink.linearEquiv.{u} (Localization S) (LocalizedModule S M₀)).trans <|
      (LocalizedModule.equivTensorProduct S M₀).trans <|
        IsLocalization.moduleLid S (Localization S) M₀
  exact ModuleCat.hasProjectiveDimensionLE_of_linearEquiv e n

/-- Lemma 10.109.13 in owner form: a localization of a ring of global dimension at most `n`
again has global dimension at most `n`. -/
instance localization_hasGlobalDimensionLE (n : ℕ) (S : Submonoid R) [HasGlobalDimensionLE R n] :
    HasGlobalDimensionLE (Localization S) n where
  hasProjectiveDimensionLE M :=
    localization_has_finite_global_dimension_le n S HasGlobalDimensionLE.hasProjectiveDimensionLE M

end
