import Mathlib
import StacksProject_2024.Chap15.«15_60_1_1»
import StacksProject_2024.Chap15.Lemma_15_75_3
import StacksProject_2024.Chap15.Lemma_15_82_10

noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]
variable (f : R) [Algebra R A] [Algebra (Localization.Away f) A]
variable [IsScalarTower R (Localization.Away f) A]
variable [Algebra.FiniteType (Localization.Away f) A]

local notation "DModA" => DerivedCategory (ModuleCat A)

/- Domain-style sampling for Lemma 15.82.11:
- primary domain: relative pseudo-coherence in `D(A)` under localization of the target algebra;
- sampled owner declarations:
  `DerivedCategory.IsMPseudoCoherentRelativeTo`,
  `DerivedCategory.IsPseudoCoherentRelativeTo`,
  `derivedTensorWithAlgebra_isMPseudoCoherentRelativeTo_of_isPseudoCoherentRingMap`,
  `derivedTensorWithAlgebra_isPseudoCoherentRelativeTo_of_torIndependent`;
- best owner abstraction: the chapter owner is the derived-category predicate
  `DerivedCategory.IsMPseudoCoherentRelativeTo` / `IsPseudoCoherentRelativeTo`, with the ambient
  finite-type algebra inferred from the derived object;
- primitive vs. derived:
  primitive data are the localized derived object `K ⊗[A]^L[Localization.Away g]` and the
  finite-type descent from `R_f → A` to `R → A`;
  derived API is the relative pseudo-coherence statement for that localized object;
- source/core/bridge triage:
  `source-facing`: Lemma `15.82.11` itself;
  `core/canonical`: the derived-category relative pseudo-coherence owners;
  `bridge/view`: the finite-type descent `R_f → A` to `R → A`, after which the localized target
    uses the canonical finite-type localization instance.
- layer: source-facing statement using the canonical owner, with the localized target handled by
  the canonical localization API rather than a parallel local finite-type bridge.
-/

include f in
private theorem finiteType_base_over_base : Algebra.FiniteType R A :=
  Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType R (Localization.Away f))
    (inferInstance : Algebra.FiniteType (Localization.Away f) A)

/-- Helper for Lemma 15.82.11: if a polynomial is annihilated by the inverse-adjoining relation
`C t * X - 1`, then it is zero. -/
private theorem polynomial_eq_zero_of_mul_inverse_relation_eq_zero
    {S : Type*} [CommRing S] (t : S) {p : Polynomial S}
    (h : p * (Polynomial.C t * Polynomial.X - 1) = 0) :
    p = 0 := by
  have hshift_zero : p * (Polynomial.C t * Polynomial.X) - p = 0 := by
    -- Proof comment: rewrite the annihilating relation so that multiplication by `X` shifts the
    -- coefficients of `p` recursively.
    simpa [sub_eq_add_neg, mul_add, mul_neg, mul_one] using h
  have hshift : p * (Polynomial.C t * Polynomial.X) = p := sub_eq_zero.mp hshift_zero
  ext n
  induction' n with n ih
  · have hcoeff := congrArg (fun q : Polynomial S ↦ q.coeff 0) hshift
    -- Proof comment: the product with `X` has zero constant term, so the constant coefficient of
    -- `p` must vanish.
    rw [mul_assoc, Polynomial.coeff_mul_X] at hcoeff
    simpa using hcoeff.symm
  · have hcoeff := congrArg (fun q : Polynomial S ↦ q.coeff (n + 1)) hshift
    -- Proof comment: after the constant term is known to vanish, the shifted coefficient
    -- identity forces every higher coefficient to vanish inductively.
    rw [mul_assoc, Polynomial.coeff_mul_X, Polynomial.coeff_mul_C, ih, zero_mul] at hcoeff
    simpa using hcoeff.symm

/-- Helper for Lemma 15.82.11: multiplication by `C t * X - 1` on `S[X]` is injective. -/
private theorem inverse_relation_mul_injective
    {S : Type*} [CommRing S] (t : S) :
    Function.Injective (fun p : Polynomial S ↦ p * (Polynomial.C t * Polynomial.X - 1)) := by
  intro p q hpq
  have hsub : (p - q) * (Polynomial.C t * Polynomial.X - 1) = 0 := by
    -- Proof comment: subtract the two equal products to reduce injectivity to the zero-kernel
    -- statement proved above.
    rw [sub_mul, hpq, sub_self]
  have hzero : p - q = 0 :=
    polynomial_eq_zero_of_mul_inverse_relation_eq_zero t hsub
  exact sub_eq_zero.mp hzero

/-- Helper for Lemma 15.82.11: the one-relation quotient `S[X]/(C t * X - 1)` is a perfect
`S[X]`-module. -/
private theorem quotient_by_inverse_relation_regularModule_isPerfect
    {S : Type*} [CommRing S] (t : S) :
    (ModuleCat.of (Polynomial S)
      ((Polynomial S) ⧸
        Ideal.span ({Polynomial.C t * Polynomial.X - 1} : Set (Polynomial S)))).IsPerfect := by
  let P₀ : FiniteProjectiveModuleCat (Polynomial S) :=
    ⟨ModuleCat.of (Polynomial S) (Polynomial S), inferInstance⟩
  let I : Ideal (Polynomial S) :=
    Ideal.span ({Polynomial.C t * Polynomial.X - 1} : Set (Polynomial S))
  let δ₀ : P₀.obj ⟶ P₀.obj :=
    { toFun := fun p ↦ p * (Polynomial.C t * Polynomial.X - 1)
      map_add' := fun p q ↦ by
        simp [add_mul]
      map_smul' := fun a p ↦ by
        -- Proof comment: scalar multiplication on the regular module is ring multiplication, so
        -- linearity is just associativity.
        change (a * p) * (Polynomial.C t * Polynomial.X - 1) =
          a * (p * (Polynomial.C t * Polynomial.X - 1))
        rw [mul_assoc] }
  let π : P₀.obj ⟶
      ModuleCat.of (Polynomial S) ((Polynomial S) ⧸ I) :=
    (Ideal.Quotient.mk I).toLinearMap
  -- Proof comment: the source-proof quotient has the explicit length-one free resolution
  -- `S[X] --(·(C t * X - 1))→ S[X] → S[X]/(C t * X - 1) → 0`.
  rw [ModuleCat.isPerfect_iff_exists_finiteProjectiveResolutionLengthLEWithFiniteTerms]
  refine ⟨1, ?_⟩
  refine ⟨fun _ ↦ P₀, fun _ ↦ δ₀, π, ?_, ?_, ?_, ?_⟩
  · -- Proof comment: the quotient map is surjective by definition of the ideal quotient.
    simpa [π] using
      (Ideal.Quotient.mk_surjective :
        Function.Surjective (Ideal.Quotient.mk I))
  · -- Proof comment: the kernel of the quotient map is exactly the principal ideal generated by
    -- `C t * X - 1`, hence the image of the multiplication map `δ₀`.
    intro p
    constructor
    · intro hp
      rw [Ideal.Quotient.eq_zero_iff_mem] at hp
      rcases Ideal.mem_span_singleton.mp hp with ⟨q, hq⟩
      exact ⟨q, by simpa [δ₀] using hq⟩
    · rintro ⟨q, rfl⟩
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact Ideal.mul_mem_left I q (Ideal.subset_span (by simp))
  · -- Proof comment: there is no higher exactness condition in length `1`.
    intro i
    exact Fin.elim0 i
  · -- Proof comment: injectivity of `δ₀` is exactly the polynomial identity proved above.
    simpa [δ₀] using inverse_relation_mul_injective t

/-- Helper for Lemma 15.82.11: adjoining one inverse to `t` presents the away localization as a
single-relation quotient. -/
private theorem away_adjoin_inverse_quotient_algEquiv
    {S : Type*} [CommRing S] (t : S) :
    ((MvPolynomial Unit S) ⧸
      Ideal.span ({MvPolynomial.C t * MvPolynomial.X () - 1} : Set (MvPolynomial Unit S))) ≃ₐ[S]
        Localization.Away t := by
  -- Proof comment: this is the canonical quotient-to-localization equivalence already provided by
  -- mathlib for away localizations.
  simpa using
    (IsLocalization.Away.mvPolynomialQuotientEquiv (S := Localization.Away t) t)

/-- Helper for Lemma 15.82.11: the quotient model `S[X]/(C t * X - 1)` is already
pseudo-coherent as an `S[X]`-module. -/
private theorem quotient_by_inverse_relation_regularModule_isPseudoCoherent
    {S : Type*} [CommRing S] (t : S) :
    (ModuleCat.of (Polynomial S)
      ((Polynomial S) ⧸
        Ideal.span ({Polynomial.C t * Polynomial.X - 1} : Set (Polynomial S)))).IsPseudoCoherent := by
  -- Proof comment: once the one-step free resolution is available, pseudo-coherence is the
  -- pseudo-coherent half of perfectness.
  exact
    (ModuleCat.isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension _).1
      (quotient_by_inverse_relation_regularModule_isPerfect t) |>.1

/-- Helper for Lemma 15.82.11: pseudo-coherence is preserved by module isomorphisms. -/
private theorem moduleCat_isPseudoCoherent_of_iso_local
    {S : Type*} [CommRing S] {M N : ModuleCat S} (e : M ≅ N)
    (hM : M.IsPseudoCoherent) :
    N.IsPseudoCoherent := by
  -- Proof comment: the module owner is the degree-zero derived object, so the module
  -- isomorphism may be pushed through `single0Functor`.
  rw [ModuleCat.IsPseudoCoherent] at hM ⊢
  exact
    isPseudoCoherent_of_iso
      ((ModuleCat.single0Functor : ModuleCat S ⥤ DerivedCategory (ModuleCat S)).mapIso e) hM

/-- Helper for Lemma 15.82.11: restricting the regular module along a ring equivalence preserves
absolute pseudo-coherence. -/
private theorem restrictScalars_regularModule_isPseudoCoherent_of_ringEquiv_local
    {S T : Type*} [CommRing S] [CommRing T] (e : S ≃+* T) :
    ((ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of T T)).IsPseudoCoherent := by
  let eₗ :
      ModuleCat.of S S ≃ₗ[S]
        ((ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of T T)) :=
    { __ := e.toAddEquiv
      map_smul' := fun r s ↦ e.map_mul r s }
  have hPerfect :
      ((ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of T T)).IsPerfect := by
    -- Proof comment: after restriction along a ring equivalence, the regular `T`-module is still
    -- the free rank-one module over `S`.
    rw [ModuleCat.isPerfect_iff_exists_finiteProjectiveResolutionLengthLEWithFiniteTerms]
    refine ⟨0, ?_⟩
    rw [ModuleCat.hasFiniteProjectiveResolutionLengthLEWithFiniteTerms_zero_iff]
    constructor
    · exact Module.Projective.of_equiv eₗ
    · exact Module.Finite.equiv eₗ
  exact
    (ModuleCat.isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension _).1 hPerfect |>.1

/-- Helper for Lemma 15.82.11: a ring equivalence whose composite with a source map equals a
target map identifies the corresponding restricted regular modules. -/
private theorem restrictScalars_regularModule_iso_of_ringEquiv_comp_eq
    {P B B' : Type*} [CommRing P] [CommRing B] [CommRing B']
    (e : B ≃+* B') (β : P →+* B) (γ : P →+* B')
    (hcomp : e.toRingHom.comp β = γ) :
    ((ModuleCat.restrictScalars β).obj (ModuleCat.of B B)) ≅
      ((ModuleCat.restrictScalars γ).obj (ModuleCat.of B' B')) := by
  let eₗ :
      ((ModuleCat.restrictScalars β).obj (ModuleCat.of B B)) ≃ₗ[P]
        ((ModuleCat.restrictScalars γ).obj (ModuleCat.of B' B')) :=
    { __ := e.toAddEquiv
      map_smul' := fun p b ↦ by
        -- Proof comment: the compatibility hypothesis identifies the two `P`-actions after
        -- transporting scalars through the ring equivalence `e`.
        change e (β p * b) = γ p * e b
        rw [e.map_mul, hcomp] }
  exact eₗ.toModuleIso

/-- Helper for Lemma 15.82.11: the one-variable quotient presentation of `S[1/t]` matches the
standard away localization model. -/
private noncomputable theorem polynomial_inverse_relation_quotient_algEquiv_away
    {S : Type*} [CommRing S] (t : S) :
    ((Polynomial S) ⧸
      Ideal.span ({Polynomial.C t * Polynomial.X - 1} : Set (Polynomial S))) ≃ₐ[S]
        Localization.Away t := by
  -- Proof comment: this is the canonical one-variable specialization of mathlib's away
  -- localization quotient presentation.
  simpa using (IsLocalization.Away.polynomialQuotientEquiv (S := Localization.Away t) t)

/-- Helper for Lemma 15.82.11: the quotient-to-away equivalence sends the quotient map to the
standard localization map `S[X] → S[1/t]`. -/
private theorem polynomial_inverse_relation_quotient_comp_mk_eq_standardAwayMap
    {S : Type*} [CommRing S] (t : S) :
    let I : Ideal (Polynomial S) :=
      Ideal.span ({Polynomial.C t * Polynomial.X - 1} : Set (Polynomial S))
    let βt : Polynomial S →+* Localization.Away t :=
      Polynomial.aeval (IsLocalization.Away.invSelf t)
    (polynomial_inverse_relation_quotient_algEquiv_away (S := S) t).toRingEquiv.toRingHom.comp
        (Ideal.Quotient.mk I) = βt := by
  -- Proof comment: both ring maps are the canonical presentation morphism that fixes
  -- coefficients and sends `X` to the chosen inverse of `t`.
  ext p
  simp [polynomial_inverse_relation_quotient_algEquiv_away]

/-- Helper for Lemma 15.82.11: the standard one-variable polynomial presentation of the away
localization is surjective. -/
private theorem standard_away_polynomial_map_surjective
    {S : Type*} [CommRing S] (t : S) :
    Function.Surjective
      (Polynomial.aeval (IsLocalization.Away.invSelf t) :
        Polynomial S →+* Localization.Away t) := by
  let I : Ideal (Polynomial S) :=
    Ideal.span ({Polynomial.C t * Polynomial.X - 1} : Set (Polynomial S))
  let q : Polynomial S →+*
      ((Polynomial S) ⧸ I) := Ideal.Quotient.mk I
  let βt : Polynomial S →+* Localization.Away t :=
    Polynomial.aeval (IsLocalization.Away.invSelf t)
  let e := polynomial_inverse_relation_quotient_algEquiv_away (S := S) t
  have hcomp : e.toRingEquiv.toRingHom.comp q = βt := by
    -- Proof comment: the quotient map followed by the quotient-to-away equivalence is exactly the
    -- standard presentation morphism.
    simpa [I, q, βt] using
      polynomial_inverse_relation_quotient_comp_mk_eq_standardAwayMap (S := S) t
  -- Proof comment: surjectivity follows because both the quotient map and the quotient-to-away
  -- equivalence are surjective.
  simpa [hcomp] using
    Function.Surjective.comp e.surjective
      (show Function.Surjective q by
        simpa [q] using (Ideal.Quotient.mk_surjective : Function.Surjective (Ideal.Quotient.mk I)))

/-- Helper for Lemma 15.82.11: the canonical quotient-to-away equivalence is linear over the
presentation ring `S[X]`. -/
private theorem polynomial_inverse_relation_quotient_algEquiv_away_map_smul
    {S : Type*} [CommRing S] (t : S)
    (p : Polynomial S)
    (q : (Polynomial S) ⧸
      Ideal.span ({Polynomial.C t * Polynomial.X - 1} : Set (Polynomial S))) :
    (polynomial_inverse_relation_quotient_algEquiv_away (S := S) t)
        (((Ideal.Quotient.mk
          (Ideal.span ({Polynomial.C t * Polynomial.X - 1} : Set (Polynomial S)))) p) * q) =
      (Polynomial.aeval (IsLocalization.Away.invSelf t)) p *
        (polynomial_inverse_relation_quotient_algEquiv_away (S := S) t) q := by
  have hmk :
      (polynomial_inverse_relation_quotient_algEquiv_away (S := S) t)
          ((Ideal.Quotient.mk
            (Ideal.span ({Polynomial.C t * Polynomial.X - 1} : Set (Polynomial S)))) p) =
        (Polynomial.aeval (IsLocalization.Away.invSelf t)) p := by
    let I : Ideal (Polynomial S) :=
      Ideal.span ({Polynomial.C t * Polynomial.X - 1} : Set (Polynomial S))
    let βt : Polynomial S →+* Localization.Away t :=
      Polynomial.aeval (IsLocalization.Away.invSelf t)
    -- Proof comment: evaluate the ring-map identity from the quotient presentation on `p`.
    change
      (((polynomial_inverse_relation_quotient_algEquiv_away (S := S) t).toRingEquiv.toRingHom.comp
        (Ideal.Quotient.mk I)) p = βt p)
    simpa [I, βt] using
      congrArg
        (fun φ : Polynomial S →+* Localization.Away t ↦ φ p)
        (polynomial_inverse_relation_quotient_comp_mk_eq_standardAwayMap (S := S) t)
  -- Proof comment: after identifying the image of the quotient generator map, linearity is just
  -- multiplicativity of the quotient-to-away algebra equivalence.
  calc
    (polynomial_inverse_relation_quotient_algEquiv_away (S := S) t)
        (((Ideal.Quotient.mk
          (Ideal.span ({Polynomial.C t * Polynomial.X - 1} : Set (Polynomial S)))) p) * q) =
      (polynomial_inverse_relation_quotient_algEquiv_away (S := S) t)
          ((Ideal.Quotient.mk
            (Ideal.span ({Polynomial.C t * Polynomial.X - 1} : Set (Polynomial S)))) p) *
        (polynomial_inverse_relation_quotient_algEquiv_away (S := S) t) q := by
          rw [map_mul]
    _ = (Polynomial.aeval (IsLocalization.Away.invSelf t)) p *
        (polynomial_inverse_relation_quotient_algEquiv_away (S := S) t) q := by
          rw [hmk]

/-- Helper for Lemma 15.82.11: the quotient presentation of `S[1/t]` identifies the quotient
regular module with the exact restricted regular module seen by `Lemma 15.65.11`. -/
private noncomputable def away_regular_module_restrictScalars_iso_of_quotient_presentation
    {S : Type*} [CommRing S] (t : S) :
    let I : Ideal (Polynomial S) :=
      Ideal.span ({Polynomial.C t * Polynomial.X - 1} : Set (Polynomial S))
    let βt : Polynomial S →+* Localization.Away t :=
      Polynomial.aeval (IsLocalization.Away.invSelf t)
    ModuleCat.of (Polynomial S) ((Polynomial S) ⧸ I) ≅
      ((ModuleCat.restrictScalars βt).obj
        (ModuleCat.of (Localization.Away t) (Localization.Away t))) := by
  let I : Ideal (Polynomial S) :=
    Ideal.span ({Polynomial.C t * Polynomial.X - 1} : Set (Polynomial S))
  let βt : Polynomial S →+* Localization.Away t :=
    Polynomial.aeval (IsLocalization.Away.invSelf t)
  let e :
      ModuleCat.of (Polynomial S) ((Polynomial S) ⧸ I) ≃ₗ[Polynomial S]
        ((ModuleCat.restrictScalars βt).obj
          (ModuleCat.of (Localization.Away t) (Localization.Away t))) :=
    { __ := (polynomial_inverse_relation_quotient_algEquiv_away (S := S) t).toAddEquiv
      map_smul' := polynomial_inverse_relation_quotient_algEquiv_away_map_smul (S := S) t }
  -- Proof comment: the quotient model and the restricted regular away-localization module have
  -- the same underlying additive group, and the previous lemma identifies their `S[X]`-actions.
  exact e.toModuleIso

/-- Helper for Lemma 15.82.11: the regular module of the away localization is pseudo-coherent
after restricting scalars along the standard one-variable presentation map. -/
private theorem quotient_model_to_away_restrictScalars_isPseudoCoherent
    {S : Type*} [CommRing S] (t : S) :
    ((ModuleCat.restrictScalars
      (Polynomial.aeval (IsLocalization.Away.invSelf t))).obj
        (ModuleCat.of (Localization.Away t) (Localization.Away t))).IsPseudoCoherent := by
  let e :=
    away_regular_module_restrictScalars_iso_of_quotient_presentation (S := S) t
  -- Proof comment: transport the explicit one-relation quotient witness across the exact module
  -- isomorphism to the restricted regular away-localization module.
  exact
    moduleCat_isPseudoCoherent_of_iso_local e
      (quotient_by_inverse_relation_regularModule_isPseudoCoherent t)

/-- Helper for Lemma 15.82.11: a relative `m`-pseudo-coherent derived object may be tested on one
chosen surjective polynomial presentation of the finite type base algebra. -/
private theorem exists_polynomialPresentation_of_relative_isMPseudoCoherent
    {S : Type*} {B : Type*} [CommRing S] [CommRing B] [Algebra S B] [Algebra.FiniteType S B]
    (K : DerivedCategory (ModuleCat B)) (m : ℤ)
    (hK : K.IsMPseudoCoherentRelativeTo S m) :
    ∃ (n : ℕ) (α : MvPolynomial (Fin n) S →ₐ[S] B),
      Function.Surjective α ∧
        ((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj K).IsMPseudoCoherent m := by
  -- Proof comment: choose the standard finite-type polynomial presentation of `B` over `S` and
  -- evaluate the relative hypothesis on that one presentation.
  obtain ⟨n, α, hα⟩ :=
    Algebra.FiniteType.iff_quotient_mvPolynomial''.1 (inferInstance : Algebra.FiniteType S B)
  exact ⟨n, α, hα, hK n α hα⟩

-- Proof sketch: first replace each surjective polynomial presentation over `Localization.Away f`
-- by one over `R` with one extra variable inverting `f`, which shows `K` is already
-- `m`-pseudo-coherent relative to `R`. Then apply derived scalar extension along `A → A_g`, and
-- use that `A_g` is finite type over `R`.
/-- Lemma 15.82.11: if `R_f → A` is finite type and a derived `A`-complex `K` is
`m`-pseudo-coherent relative to `Localization.Away f`, then its localization
`K ⊗_A A_g` is `m`-pseudo-coherent relative to `R`. -/
@[stacks 0679]
theorem isMPseudoCoherentRelativeTo_localizationAway_from_localizedBase
    (g : A) (K : DModA) (m : ℤ)
    (hK : K.IsMPseudoCoherentRelativeTo (Localization.Away f) m) :
    by
      letI : Algebra.FiniteType R (Localization.Away g) :=
        Algebra.FiniteType.trans
          (finiteType_base_over_base f)
          (inferInstance : Algebra.FiniteType A (Localization.Away g))
      -- Proof comment: the source-faithful route first proves `K` is already relative
      -- `m`-pseudo-coherent over `R` by replacing a polynomial presentation over `R_f` with one
      -- extra variable inverting `f`, then localizes at a lift of `g` and adjoins one more
      -- inverse.
      rcases exists_polynomialPresentation_of_relative_isMPseudoCoherent
          (K := K) (m := m) hK with
        ⟨n, α, hα, hKα⟩
      -- Route correction: the tempting later-file shortcut through `Lemma_15_82_15` and
      -- `Lemma_15_83_4` is unusable here because its prerequisite `Lemma_15_81_6` currently does
      -- not compile in this workspace, so the proof must stay on the original presentation
      -- descent route.
      -- Proof comment: the generic one-variable away-localization bridge is now closed: the
      -- quotient model and the exact restricted regular module for `S[1/t]` are identified and
      -- the resulting regular module is pseudo-coherent. The remaining blocker is the first
      -- source-proof specialization from localization away from `C f` in
      -- `MvPolynomial (Fin n) R` to the coefficient-localized ring
      -- `MvPolynomial (Fin n) (Localization.Away f)`.
      -- TODO: construct the `MvPolynomial` coefficient-localization algebra equivalence
      -- `Localization.Away (MvPolynomial.C f) ≃ₐ[MvPolynomial (Fin n) R]
      --   MvPolynomial (Fin n) (Localization.Away f)`,
      -- transport `quotient_model_to_away_restrictScalars_isPseudoCoherent (t := MvPolynomial.C f)`
      -- across that equivalence to obtain the exact `hB` input for the first `Lemma_15_65_11`
      -- descent, and then reuse the already-closed generic one-variable bridge for the later
      -- localization at the chosen lift `g'`.
      let _ := n
      let _ := α
      let _ := hα
      let _ := hKα
      exact (K ⊗[A]^L[Localization.Away g]).IsMPseudoCoherentRelativeTo R m := sorry

-- Proof sketch: pseudo-coherence is relative `m`-pseudo-coherence for all integers `m`, so apply
-- the preceding theorem to each degree bound after unfolding the hypothesis.
/-- Localization away from `g` carries pseudo-coherent derived `A`-complexes relative to
`Localization.Away f` to pseudo-coherent complexes relative to `R`. -/
theorem isPseudoCoherentRelativeTo_localizationAway_from_localizedBase
    (g : A) (K : DModA)
    (hK : K.IsPseudoCoherentRelativeTo (Localization.Away f)) :
    by
      letI : Algebra.FiniteType R (Localization.Away g) :=
        Algebra.FiniteType.trans
          (finiteType_base_over_base f)
          (inferInstance : Algebra.FiniteType A (Localization.Away g))
      -- Proof comment: pseudo-coherence is the degreewise version of the previous theorem, so
      -- once the bounded source-proof route is fixed, the unbounded statement follows
      -- immediately degreewise.
      intro m
      exact
        isMPseudoCoherentRelativeTo_localizationAway_from_localizedBase
          (f := f) (g := g) (K := K) (m := m) (hK := hK m)

end

end CategoryTheory
