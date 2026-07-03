import Mathlib
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import StacksProject_2024.Chap13.Definition_13_34_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite

universe u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.DerivedCategory

section

variable {A : Type u} [CommRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)

/- Domain-style sampling:
- primary domain: the Stacks-project object `T(K, f)` and its vanishing criterion in `D(A)`;
- sampled owner-side declarations:
  `(ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory`,
  `DerivedCategory.singleFunctor`,
  `Functor.ofOpSequence`,
  `CategoryTheory.IsDerivedLimit`;
- best owner abstraction: keep the source-facing owner `T(K, f)` visible, realized through the
  canonical internal-Hom owner on `D(A)` under an ambient monoidal-closed structure, while the
  localization-away predicate remains the canonical owner-independent vanishing criterion;
- primitive data: `f : A`, `K : D(A)`, and the restriction-of-scalars functor `D(A_f) ⥤ D(A)`;
- derived API: the Milnor tower model of `T(K, f)`, the equivalence theorem to the vanishing
  predicate, and the module-level specialization `ModuleCat.moduleLocalizationAwayTVanishing`.

Layer triage:
- `source-facing`: `localizationAwayT H f K`, the textbook `T(K, f)`;
- `core/canonical`: the owner-independent predicate
  `localizationAwayDerivedHomVanishingCondition f K`;
- `bridge/view`: `localizationAwayTower`, `localizationAwayT_isDerivedLimit`, the vanishing
  equivalence, and the degree-zero module specialization. -/

/-- Lemma 15.92.1 source-facing owner: after restriction of scalars along `A → A_f`, every
morphism from an object of `D(A_f)` to `K` is zero. -/
def localizationAwayDerivedHomVanishingCondition (f : A) (K : DMod) : Prop :=
  ∀ E : DerivedCategory (ModuleCat (Localization.Away f)),
    Subsingleton
      (((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj E) ⟶ K)

/-- The constant tower `\cdots \xrightarrow{f} K \xrightarrow{f} K \xrightarrow{f} K` in `D(A)`,
with transition maps given by multiplication by `f`. -/
abbrev localizationAwayTower (f : A) (K : DMod) : ℕᵒᵖ ⥤ DMod :=
  let X : ℕ → DMod := fun _ ↦ K
  let step : (n : ℕ) → X (n + 1) ⟶ X n := fun _ ↦ f • 𝟙 K
  Functor.ofOpSequence step

section Monoidal

variable [MonoidalCategory (DerivedCategory (ModuleCat A))]
  (H : MonoidalClosed (DerivedCategory (ModuleCat A)))
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)

/-- The textbook object `T(K, f)`, realized canonically as the derived internal Hom
`R\mathrm{Hom}_A(A_f, K)` in `D(A)`. -/
abbrev localizationAwayT (f : A) (K : DMod) : DMod := by
  letI := H
  exact (ihom ((single₀).obj (ModuleCat.of A (Localization.Away f)))).obj K

-- Proof sketch: use the standard two-term resolution of `A_f` and identify the resulting derived
-- internal Hom with the Milnor triangle for the constant tower with transition `f • 𝟙`.
/-- Lemma 15.92.1: the textbook object `T(K, f)` is a derived limit of the constant tower
`\cdots \xrightarrow{f} K \xrightarrow{f} K \xrightarrow{f} K`. -/
theorem localizationAwayT_isDerivedLimit (f : A) (K : DMod) :
    IsDerivedLimit (localizationAwayTower f K) (localizationAwayT H f K) := sorry

-- Proof sketch: by derived adjunction, morphisms from an object of `D(A_f)` to `K` after
-- restriction of scalars are the same source-facing data as morphisms into `T(K, f)`, so the
-- universal vanishing condition is equivalent to `T(K, f)` being zero.
/-- The textbook vanishing statement `T(K, f) = 0` is equivalent to the owner-independent
localization-away derived-Hom vanishing condition. -/
theorem localizationAwayT_isZero_iff
    (f : A) (K : DMod) :
    IsZero (localizationAwayT H f K) ↔
      localizationAwayDerivedHomVanishingCondition f K := sorry

/-- Rewriting the owner-independent vanishing condition in terms of the source-facing object
`T(K, f)`. -/
theorem localizationAwayDerivedHomVanishingCondition_iff
    (f : A) (K : DMod) :
    localizationAwayDerivedHomVanishingCondition f K ↔
      IsZero (localizationAwayT H f K) := by
  simpa using (localizationAwayT_isZero_iff H f K).symm

end Monoidal

end

end CategoryTheory.DerivedCategory

namespace ModuleCat

section

variable {A : Type u} [CommRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)

/-- The module-level vanishing condition `T(M, f) = 0`, expressed by specializing the derived
owner from Lemma `15.92.1` to the degree-zero object `M[0]`. -/
def moduleLocalizationAwayTVanishing (M : ModuleCat A) (f : A) : Prop :=
  CategoryTheory.DerivedCategory.localizationAwayDerivedHomVanishingCondition f ((single₀).obj M)

section Monoidal

variable [MonoidalCategory (DerivedCategory (ModuleCat A))]
  (H : MonoidalClosed (DerivedCategory (ModuleCat A)))

/-- The module-level vanishing condition is exactly the vanishing of the degree-zero specialization
of `T(K, f)`. -/
theorem moduleLocalizationAwayTVanishing_iff (M : ModuleCat A) (f : A) :
    moduleLocalizationAwayTVanishing M f ↔
      IsZero (CategoryTheory.DerivedCategory.localizationAwayT H f ((single₀).obj M)) := by
  simpa [moduleLocalizationAwayTVanishing] using
    CategoryTheory.DerivedCategory.localizationAwayDerivedHomVanishingCondition_iff
      H f ((single₀).obj M)

end Monoidal

end

end ModuleCat
