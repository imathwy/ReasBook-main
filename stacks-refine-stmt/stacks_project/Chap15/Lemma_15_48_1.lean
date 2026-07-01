import Mathlib.Algebra.Regular.Defs
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.Away.Basic

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [CommRing R]

/-
Domain-style sampling for Lemma 15.48.1:
- primary domain: commutative algebra of derivations under adic completion and localization;
- sampled owner declarations of the same kind:
  `Derivation`,
  `Derivation.compAlgebraMap`,
  `LinearMap.compDer`,
  `AdicCompletion.liftAlgHom`,
  `IsLocalization.liftAlgHom`,
  `Localization.awayMapₐ`;
- best owner abstraction: the target of clauses `(1)` and `(2)` is a canonical `Derivation` on the
  completion/localization itself, while the extension property along the structural map is the
  derived source-facing view of the owner-level equality on restricted derivations. For clause
  `(3)`, the chapter's canonical owner for comparison maps between away localizations is
  `Localization.awayMapₐ`, but the source hypothesis is only the existence of an `R`-algebra
  isomorphism between the two away localizations, so the main theorem keeps that source-facing
  shape instead of strengthening it to a statement about the canonical map;
- primitive data: the source derivation `D`, the ideal `I` for completion, and the target
  localization algebra `A`;
- derived API: pointwise restriction-to-`R` formulas, uniqueness lemmas, and the companion `∃!`
  reformulations built from the owner-level restriction equation.

Layer triage:
- `source-facing`: the canonical extensions `D.adicCompletionExtension I` and
  `D.localizationExtension S A`, together with the finite-type existential statement in clause
  `(3)`;
- `core/canonical`: the owner type `Derivation ℤ _ _` on the target algebra;
- `bridge/view`: the companion existence-uniqueness theorems and the restriction formulas along the
  canonical maps `R → AdicCompletion I R` and `R → A`.
-/

namespace Derivation

variable (D : Derivation ℤ R R)

section AdicCompletion

variable (I : Ideal R)

local notation "R̂" => AdicCompletion I R

private theorem existsUnique_adicCompletionExtension_aux :
    ∃! Dhat : Derivation ℤ R̂ R̂,
      Dhat.compAlgebraMap R = (Algebra.linearMap R R̂).compDer D := by
  sorry

-- Proof sketch: for `n ≥ 1`, the Leibniz rule implies `D (I ^ (n + 1)) ⊆ I ^ n`, so `D`
-- induces compatible derivations on the quotient system `R ⧸ I ^ (n + 1) → R ⧸ I ^ n`. Passing to
-- the inverse limit yields a derivation on the `I`-adic completion, and uniqueness is checked on
-- the dense image of `R`.
/-- Lemma 15.48.1 (1): for any ideal `I` of a commutative ring `R`, a derivation `D : R → R`
extends canonically to a derivation of the `I`-adic completion `AdicCompletion I R`. -/
noncomputable def adicCompletionExtension : Derivation ℤ R̂ R̂ :=
  (existsUnique_adicCompletionExtension_aux D I).choose

theorem adicCompletionExtension_compAlgebraMap :
    (D.adicCompletionExtension I).compAlgebraMap R = (Algebra.linearMap R R̂).compDer D :=
  (existsUnique_adicCompletionExtension_aux D I).choose_spec.left

@[simp]
theorem adicCompletionExtension_algebraMap (r : R) :
    D.adicCompletionExtension I (algebraMap R R̂ r) = algebraMap R R̂ (D r) :=
  congr_fun (D.adicCompletionExtension_compAlgebraMap I) r

theorem adicCompletionExtension_unique
    (Dhat : Derivation ℤ R̂ R̂)
    (hDhat : Dhat.compAlgebraMap R = (Algebra.linearMap R R̂).compDer D) :
    Dhat = D.adicCompletionExtension I := by
  exact (existsUnique_adicCompletionExtension_aux D I).choose_spec.right Dhat hDhat

/-- Existence and uniqueness of the canonical extension of a derivation to the `I`-adic
completion. -/
theorem existsUnique_adicCompletionExtension :
    ∃! Dhat : Derivation ℤ R̂ R̂,
      Dhat.compAlgebraMap R = (Algebra.linearMap R R̂).compDer D :=
  ⟨D.adicCompletionExtension I, D.adicCompletionExtension_compAlgebraMap I,
    fun Dhat hDhat ↦ D.adicCompletionExtension_unique I Dhat hDhat⟩

end AdicCompletion

section Localization

private theorem existsUnique_localizationExtension_aux
    (D : Derivation ℤ R R) (S : Submonoid R) (A : Type v)
    [CommRing A] [Algebra R A] [IsLocalization S A]
    : ∃! Dloc : Derivation ℤ A A,
        Dloc.compAlgebraMap R = (Algebra.linearMap R A).compDer D := by
  sorry

-- Proof sketch: define the candidate by the quotient rule on fractions,
-- `D(r / s) = D(r) / s - r D(s) / s^2`, and prove it is well defined using the localization
-- relation. The derivation axioms follow from direct computation, and uniqueness is forced by the
-- fact that every element of the localization is represented by a fraction.
/-- Lemma 15.48.1 (2): for any multiplicative subset `S` of `R`, a derivation `D : R → R`
extends canonically to any localization `A` of `R` at `S`. -/
noncomputable def localizationExtension (D : Derivation ℤ R R) (S : Submonoid R) (A : Type v)
    [CommRing A] [Algebra R A] [IsLocalization S A] :
    Derivation ℤ A A :=
  (existsUnique_localizationExtension_aux D S A).choose

theorem localizationExtension_compAlgebraMap
    (D : Derivation ℤ R R) (S : Submonoid R) (A : Type v)
    [CommRing A] [Algebra R A] [IsLocalization S A] :
    (D.localizationExtension S A).compAlgebraMap R =
      (Algebra.linearMap R A).compDer D :=
  (existsUnique_localizationExtension_aux D S A).choose_spec.left

@[simp]
theorem localizationExtension_algebraMap
    (D : Derivation ℤ R R) (S : Submonoid R) (A : Type v)
    [CommRing A] [Algebra R A] [IsLocalization S A] (r : R) :
    D.localizationExtension S A (algebraMap R A r) = algebraMap R A (D r) :=
  congr_fun (D.localizationExtension_compAlgebraMap S A) r

theorem localizationExtension_unique
    (D : Derivation ℤ R R) (S : Submonoid R) (A : Type v)
    [CommRing A] [Algebra R A] [IsLocalization S A]
    (Dloc : Derivation ℤ A A)
    (hDloc : Dloc.compAlgebraMap R = (Algebra.linearMap R A).compDer D) :
    Dloc = D.localizationExtension S A := by
  exact (existsUnique_localizationExtension_aux D S A).choose_spec.right Dloc hDloc

/-- Existence and uniqueness of the canonical extension of a derivation to a localization. -/
theorem existsUnique_localizationExtension
    (D : Derivation ℤ R R) (S : Submonoid R) (A : Type v)
    [CommRing A] [Algebra R A] [IsLocalization S A] :
    ∃! Dloc : Derivation ℤ A A,
        Dloc.compAlgebraMap R = (Algebra.linearMap R A).compDer D :=
  ⟨D.localizationExtension S A, D.localizationExtension_compAlgebraMap S A,
    fun Dloc hDloc ↦ D.localizationExtension_unique S A Dloc hDloc⟩

end Localization

section FiniteType

variable {R' : Type v} [CommRing R'] [Algebra R R'] [Algebra.FiniteType R R']

-- Proof sketch: choose finitely many `R`-algebra generators of `R'` and clear denominators after
-- transporting them across an isomorphism between the two away localizations where `g` becomes
-- invertible. For sufficiently large `N`, the scaled derivation `g ^ N • D` carries each
-- generator into `R'`, hence by the Leibniz rule it extends from `R` to an `R'`-valued derivation
-- on the finite type algebra `R'`.
/-- Canonical-owner reformulation of Lemma 15.48.1 (3): if the canonical comparison
`Localization.awayMapₐ (Algebra.ofId R R') g` is bijective and `algebraMap R R' g` is a
nonzerodivisor in `R'`, then some multiple `g ^ N • D` extends to a derivation of `R'`. -/
theorem exists_pow_smul_extension_of_finiteType_of_bijective_awayMap (g : R)
    (hAway : Function.Bijective (Localization.awayMapₐ (Algebra.ofId R R') g))
    (hg : IsRegular (algebraMap R R' g)) :
    ∃ N : ℕ, ∃ D' : Derivation ℤ R' R',
      D'.compAlgebraMap R = (Algebra.linearMap R R').compDer (g ^ N • D) := sorry

/-- Lemma 15.48.1 (3): let `R → R'` be a finite type extension and let `g : R` be such that
`Localization.Away g` and `Localization.Away (algebraMap R R' g)` are isomorphic as `R`-algebras
and `algebraMap R R' g` is a nonzerodivisor in `R'`. Equivalently, the canonical comparison map
`Localization.awayMapₐ (Algebra.ofId R R') g` is bijective. Then some multiple `g ^ N • D`
extends to a derivation of `R'`. -/
theorem exists_pow_smul_extension_of_finiteType_of_away_iso (g : R)
    (eAway : Localization.Away g ≃ₐ[R] Localization.Away (algebraMap R R' g))
    (hg : IsRegular (algebraMap R R' g)) :
    ∃ N : ℕ, ∃ D' : Derivation ℤ R' R',
      D'.compAlgebraMap R = (Algebra.linearMap R R').compDer (g ^ N • D) :=
  D.exists_pow_smul_extension_of_finiteType_of_bijective_awayMap g
    (by
      have hEq : Localization.awayMapₐ (Algebra.ofId R R') g = eAway.toAlgHom := by
        apply Localization.algHom_ext (Submonoid.powers g)
        ext
      simpa [hEq] using eAway.bijective)
    hg

end FiniteType

end Derivation

end
