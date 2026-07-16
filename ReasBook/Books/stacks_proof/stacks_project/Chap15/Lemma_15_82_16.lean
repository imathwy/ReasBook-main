import Mathlib
import stacks_proof.stacks_project.Chap15.«15_60_1_1»
import stacks_proof.stacks_project.Chap15.Definition_15_33_2
import stacks_proof.stacks_project.Chap15.Lemma_15_65_14
import stacks_proof.stacks_project.Chap15.Lemma_15_82_10
import stacks_proof.stacks_project.Chap15.Lemma_15_82_11
import stacks_proof.stacks_project.Chap15.Lemma_15_82_15

noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable [Algebra.FiniteType R A]
variable {ι : Type*} [Finite ι]

local notation "DModA" => DerivedCategory (ModuleCat A)

/- Domain-style sampling for Lemma 15.82.16:
- primary domain: relative pseudo-coherence in `D(A)` and its locality on a finite principal-open
  cover of `Spec A`;
- sampled owner declarations:
  `DerivedCategory.IsMPseudoCoherentRelativeTo`,
  `DerivedCategory.IsPseudoCoherentRelativeTo`,
  `isMPseudoCoherent_iff_localizationAway_unitIdeal`,
  `derivedTensorWithAlgebra_isMPseudoCoherentRelativeTo_of_isPseudoCoherentRingMap`;
- best owner abstraction: this item is `source-facing`, while the core/canonical owners are the
  relative pseudo-coherence predicates `K.IsMPseudoCoherentRelativeTo R m` and
  `K.IsPseudoCoherentRelativeTo R` on derived `A`-complexes;
- primitive vs. derived:
  primitive data are the finite family `f : ι → A`, the unit-ideal hypothesis, and the localized
  derived objects `K ⊗[A]^L[Localization.Away (f i)]`;
  derived API is the relative pseudo-coherence conclusion on `K`, so the file should not keep a
  parallel coordinate-level `Fin r` interface or explicit functor application as the public
  surface;
- source/core/bridge triage:
  `source-facing`: the local-global equivalences below;
  `core/canonical`: the owner predicates `IsMPseudoCoherentRelativeTo` and
    `IsPseudoCoherentRelativeTo`;
  `bridge/view`: the localized derived scalar-extension objects
    `K ⊗[A]^L[Localization.Away (f i)]`.
-/

-- Proof sketch: for `←`, restrict the complex along any surjective polynomial presentation
-- `P → A`; the hypotheses identify each localization over `A_{f i}` with the corresponding
-- localization of the restricted `P`-complex, and Lemma `15.65.14` descends `m`-pseudo-coherence
-- from the principal-open cover because the images of the `f i` still generate the unit ideal.
-- For `→`, localize a relative `m`-pseudo-coherent approximation; this is the relative
-- localization statement proved earlier in the chapter.
/-- Helper for Lemma 15.82.16: restricting the regular module along a ring equivalence preserves
absolute pseudo-coherence. -/
private theorem restrictScalars_regularModule_isPseudoCoherent_of_ringEquiv
    {S T : Type*} [CommRing S] [CommRing T] (e : S ≃+* T) :
    ((ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of T T)).IsPseudoCoherent := by
  let eₗ :
      ModuleCat.of S S ≃ₗ[S]
        ((ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of T T)) :=
    { __ := e.toAddEquiv
      map_smul' := fun r s ↦ e.map_mul r s }
  have hPerfect :
      ((ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of T T)).IsPerfect := by
    -- Proof comment: after restricting along a ring equivalence, the regular `T`-module is
    -- still the free rank-one module over `S`.
    rw [ModuleCat.isPerfect_iff_exists_finiteProjectiveResolutionLengthLEWithFiniteTerms]
    refine ⟨0, ?_⟩
    rw [ModuleCat.hasFiniteProjectiveResolutionLengthLEWithFiniteTerms_zero_iff]
    constructor
    · exact Module.Projective.of_equiv eₗ
    · exact Module.Finite.equiv eₗ
  -- Proof comment: pseudo-coherence is the pseudo-coherent half of perfectness.
  exact
    (ModuleCat.isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension _).1 hPerfect |>.1

/-- Helper for Lemma 15.82.16: relative `m`-pseudo-coherence of a derived `A`-complex can be
checked on one surjective polynomial presentation of `A` over `R`. -/
private theorem derived_isMPseudoCoherentRelativeTo_iff_overSomePolynomialPresentation
    (K : DModA) (m : ℤ) :
    K.IsMPseudoCoherentRelativeTo R m ↔
      ∃ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A),
        Function.Surjective α ∧
          ((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj K).IsMPseudoCoherent
            m := by
  let E := DerivedCategory.Q.objPreimage K
  let eK : DerivedCategory.Q.obj E ≅ K := DerivedCategory.Q.objObjPreimageIso K
  let presentationIso := fun {n : ℕ} (α : MvPolynomial (Fin n) R →ₐ[R] A) ↦
    (((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory).mapIso eK.symm) ≪≫
      (ModuleCat.restrictScalars α.toRingHom).mapDerivedCategoryFactors.app E
  have hrel :
      K.IsMPseudoCoherentRelativeTo R m ↔ E.IsMPseudoCoherentRelativeTo R m := by
    constructor
    · intro hK n α hα
      -- Proof comment: move the restricted derived object to the chosen strict representative
      -- and evaluate the relative hypothesis there.
      exact isMPseudoCoherent_of_iso (presentationIso α) m (hK n α hα)
    · intro hE n α hα
      -- Proof comment: the same canonical comparison runs backwards via the inverse
      -- isomorphism.
      exact isMPseudoCoherent_of_iso (presentationIso α).symm m (hE n α hα)
  calc
    K.IsMPseudoCoherentRelativeTo R m ↔ E.IsMPseudoCoherentRelativeTo R m := hrel
    _ ↔
        ∃ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A),
          Function.Surjective α ∧ (E.polynomialPresentationRestriction α).IsMPseudoCoherent m :=
      CochainComplex.isMPseudoCoherentRelativeTo_iff_overSomePolynomialPresentation E m
    _ ↔
        ∃ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A),
          Function.Surjective α ∧
            ((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj K).IsMPseudoCoherent
              m := by
      constructor
      · rintro ⟨n, α, hα, hEα⟩
        -- Proof comment: transport the strict restricted complex back to the restricted derived
        -- object.
        exact ⟨n, α, hα, isMPseudoCoherent_of_iso (presentationIso α).symm m hEα⟩
      · rintro ⟨n, α, hα, hKα⟩
        -- Proof comment: conversely, move the derived-side hypothesis onto the strict
        -- polynomial-presentation restriction.
        exact ⟨n, α, hα, isMPseudoCoherent_of_iso (presentationIso α) m hKα⟩

/-- Helper for Lemma 15.82.16: the localization of the base ring away from `1` is already
pseudo-coherent relative to the original base. -/
private theorem localizationAwayOne_regularModule_isPseudoCoherentRelativeTo :
    (ModuleCat.of (Localization.Away (1 : R)) (Localization.Away (1 : R))).IsPseudoCoherentRelativeTo
      R := by
  let eZero : MvPolynomial (Fin 0) R ≃ₐ[R] R :=
    RingHom.IsLocalCompleteIntersection.empty_polynomial_algEquiv R
  let eAway : R ≃ₐ[R] Localization.Away (1 : R) :=
    IsLocalization.atUnit R (Localization.Away (1 : R)) 1 isUnit_one
  let e : MvPolynomial (Fin 0) R ≃ₐ[R] Localization.Away (1 : R) := eZero.trans eAway
  have hReg :
      ((ModuleCat.restrictScalars e.toRingHom).obj
        (ModuleCat.of (Localization.Away (1 : R)) (Localization.Away (1 : R)))).IsPseudoCoherent := by
    -- Proof comment: the chosen empty presentation is a ring equivalence, so the restricted
    -- regular module is still the free rank-one module.
    simpa using restrictScalars_regularModule_isPseudoCoherent_of_ringEquiv e.toRingEquiv
  -- Proof comment: relative pseudo-coherence can be checked on one surjective polynomial
  -- presentation, and the empty presentation above is exactly such a presentation.
  rw [ModuleCat.IsPseudoCoherentRelativeTo,
    CochainComplex.isPseudoCoherentRelativeTo_iff_overSomePolynomialPresentation]
  refine ⟨0, e.toAlgHom, e.surjective, ?_⟩
  simpa [ModuleCat.IsPseudoCoherent, CochainComplex.polynomialPresentationRestriction] using hReg

/-- Helper for Lemma 15.82.16: replacing `R` by `R[1⁻¹]` does not change relative
`m`-pseudo-coherence. -/
private theorem isMPseudoCoherentRelativeTo_iff_localizationAway_one
    (K : DModA) (m : ℤ) :
    by
      let eAway : R ≃ₐ[R] Localization.Away (1 : R) :=
        IsLocalization.atUnit R (Localization.Away (1 : R)) 1 isUnit_one
      letI : Algebra (Localization.Away (1 : R)) R := eAway.symm.toAlgHom.toAlgebra
      letI : Algebra (Localization.Away (1 : R)) A :=
        ((algebraMap R A).comp eAway.symm.toRingHom).toAlgebra
      letI : IsScalarTower R (Localization.Away (1 : R)) A :=
        IsScalarTower.of_algebraMap_eq' <| by
          ext r
          have hcomm : eAway r = algebraMap R (Localization.Away (1 : R)) r := by
            simpa using eAway.commutes r
          calc
            (algebraMap R A) (eAway.symm (algebraMap R (Localization.Away (1 : R)) r)) =
                (algebraMap R A) (eAway.symm (eAway r)) := by rw [hcomm]
            _ = algebraMap R A r := by rw [AlgEquiv.apply_symm_apply]
      letI : Algebra.FiniteType (Localization.Away (1 : R)) R :=
        Algebra.FiniteType.of_surjective (algebraMap (Localization.Away (1 : R)) R)
          eAway.symm.surjective
      letI : Algebra.FiniteType (Localization.Away (1 : R)) A :=
        Algebra.FiniteType.trans
          (inferInstance : Algebra.FiniteType (Localization.Away (1 : R)) R)
          (inferInstance : Algebra.FiniteType R A)
      exact K.IsMPseudoCoherentRelativeTo (Localization.Away (1 : R)) m ↔
        K.IsMPseudoCoherentRelativeTo R m := by
          -- Proof comment: use the intermediate-ring comparison with the regular
          -- `R[1⁻¹]`-module from the previous helper.
          simpa using
            (isMPseudoCoherentRelativeTo_iff_of_intermediate_isPseudoCoherentRelativeTo
              (R := R) (A := Localization.Away (1 : R)) (B := A) K m
              localizationAwayOne_regularModule_isPseudoCoherentRelativeTo)

/-- Helper for Lemma 15.82.16: if one surjective algebra map `P → A` already makes the
restricted derived `A`-complex absolutely `m`-pseudo-coherent, then the original complex is
`m`-pseudo-coherent relative to `P`. -/
private theorem isMPseudoCoherentRelativeTo_of_surjective_algebraMap
    {P : Type*} [CommRing P] [Algebra P A] [Algebra.FiniteType P A]
    (hsurj : Function.Surjective (algebraMap P A)) (K : DModA) (m : ℤ)
    (hK :
      ((ModuleCat.restrictScalars (algebraMap P A)).mapDerivedCategory.obj K).IsMPseudoCoherent
        m) :
    K.IsMPseudoCoherentRelativeTo P m := by
  let e : MvPolynomial (Fin 0) P ≃ₐ[P] P :=
    RingHom.IsLocalCompleteIntersection.empty_polynomial_algEquiv P
  let α : MvPolynomial (Fin 0) P →ₐ[P] A := (algebraMap P A).comp e.toAlgHom
  have hReg :
      ((ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of P P)).IsPseudoCoherent := by
    -- Proof comment: the empty polynomial presentation is a ring equivalence, so restricting the
    -- regular `P`-module along it keeps absolute pseudo-coherence unchanged.
    simpa using restrictScalars_regularModule_isPseudoCoherent_of_ringEquiv e.toRingEquiv
  have hα :
      ((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj K).IsMPseudoCoherent m := by
    -- Proof comment: the chosen presentation differs from `algebraMap P A` only by the empty
    -- polynomial ring equivalence, so the restriction comparison is the canonical one from
    -- Lemma `15.82.15`.
    simpa [α] using
      (isMPseudoCoherent_iff_restrictScalars_local e.toRingHom
        ((ModuleCat.restrictScalars (algebraMap P A)).mapDerivedCategory.obj K) m hReg).2 hK
  -- Proof comment: relative `m`-pseudo-coherence can be checked on one surjective polynomial
  -- presentation, and the empty presentation composed with `P → A` is exactly such a cover.
  exact
    (isMPseudoCoherentRelativeTo_iff_overSomePolynomialPresentation
      (R := P) (A := A) K m).2
      ⟨0, α, Function.Surjective.comp hsurj e.surjective, hα⟩

/-- Helper for Lemma 15.82.16: over a surjective finite type map `B → A`, relative
`m`-pseudo-coherence over `B` is equivalent to absolute `m`-pseudo-coherence of the restricted
derived `A`-complex. -/
private theorem isMPseudoCoherentRelativeTo_base_iff_restrictScalars_of_surjective
    {B : Type*} [CommRing B] [Algebra B A]
    (K : DModA) (m : ℤ) (hφ : Function.Surjective (algebraMap B A)) :
    by
      letI : Algebra.FiniteType B A := Algebra.FiniteType.of_surjective (algebraMap B A) hφ
      exact
        K.IsMPseudoCoherentRelativeTo B m ↔
          (((ModuleCat.restrictScalars (algebraMap B A)).mapDerivedCategory.obj K)).IsMPseudoCoherent
            m := by
  letI : Algebra.FiniteType B A := Algebra.FiniteType.of_surjective (algebraMap B A) hφ
  let KB : DerivedCategory (ModuleCat B) :=
    ((ModuleCat.restrictScalars (algebraMap B A)).mapDerivedCategory.obj K)
  let e : MvPolynomial (Fin 0) B ≃ₐ[B] B :=
    RingHom.IsLocalCompleteIntersection.empty_polynomial_algEquiv B
  let α₀ : MvPolynomial (Fin 0) B →ₐ[B] A := (Algebra.ofId B A).comp e.toAlgHom
  have hα₀ : Function.Surjective α₀ := by
    intro a
    rcases hφ a with ⟨b, rfl⟩
    refine ⟨e.symm b, ?_⟩
    simp [α₀]
  have hrestricted_regular :
      ((ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of B B)).IsPseudoCoherent := by
    -- Proof comment: restricting the regular `B`-module along the empty polynomial equivalence
    -- keeps the free rank-one module.
    simpa using restrictScalars_regularModule_isPseudoCoherent_of_ringEquiv e.toRingEquiv
  have hchange :
      KB.IsMPseudoCoherent m ↔
        (((ModuleCat.restrictScalars e.toRingHom).mapDerivedCategory.obj KB)).IsMPseudoCoherent m := by
    -- Proof comment: absolute pseudo-coherence is invariant under restricting scalars along a
    -- ring equivalence.
    simpa using isMPseudoCoherent_iff_restrictScalars_local e.toRingHom KB m hrestricted_regular
  constructor
  · intro hK
    have hα :
        (((ModuleCat.restrictScalars α₀.toRingHom).mapDerivedCategory.obj K)).IsMPseudoCoherent m :=
      hK 0 α₀ hα₀
    -- Proof comment: evaluate the relative hypothesis on the empty polynomial presentation of
    -- `A` over `B`.
    exact hchange.mpr (by simpa [KB, α₀, e] using hα)
  · intro hKB
    -- Proof comment: the surjective empty presentation already witnesses relative
    -- `m`-pseudo-coherence over `B`.
    refine
      (derived_isMPseudoCoherentRelativeTo_iff_overSomePolynomialPresentation
        (R := B) (A := A) K m).2 ?_
    refine ⟨0, α₀, hα₀, ?_⟩
    exact hchange.mp (by simpa [KB, α₀, e] using hKB)

/-- Helper for Lemma 15.82.16: once an intermediate `R`-algebra `P` carries the source-faithful
principal-open cover on which the restricted complex is absolutely `m`-pseudo-coherent, the
global relative `m`-pseudo-coherence over `R` follows. -/
private theorem isMPseudoCoherentRelativeTo_of_intermediate_localizationAway_unitIdeal
    {P : Type*} [CommRing P] [Algebra R P] [Algebra P A] [IsScalarTower R P A]
    [Algebra.FiniteType R P] [Algebra.FiniteType P A]
    (hP : (ModuleCat.of P P).IsPseudoCoherentRelativeTo R)
    (hsurj : Function.Surjective (algebraMap P A))
    (p : ι → P) (hunitP : Ideal.span (Set.range p) = ⊤)
    (K : DModA) (m : ℤ)
    (hloc :
      ∀ i,
        (((ModuleCat.restrictScalars (algebraMap P A)).mapDerivedCategory.obj K)
          ⊗[P]^L[Localization.Away (p i)]).IsMPseudoCoherent) :
    K.IsMPseudoCoherentRelativeTo R m := by
  let K_P : DerivedCategory (ModuleCat P) :=
    (ModuleCat.restrictScalars (algebraMap P A)).mapDerivedCategory.obj K
  have hK_P :
      K_P.IsMPseudoCoherent m := by
    -- Proof comment: apply the absolute local-global theorem over the intermediate ring `P` to
    -- the restricted complex.
    exact isMPseudoCoherent_of_localizationAway_unitIdeal p hunitP K_P m hloc
  have hK_rel_P : K.IsMPseudoCoherentRelativeTo P m := by
    -- Proof comment: the surjective map `P → A` turns the absolute statement on the restricted
    -- `P`-complex into the relative statement over `P`.
    exact isMPseudoCoherentRelativeTo_of_surjective_algebraMap hsurj K m hK_P
  -- Proof comment: the regular `P`-module is pseudo-coherent relative to `R`, so
  -- Lemma `15.82.15` compares relative pseudo-coherence over `P` and over `R`.
  exact
    (isMPseudoCoherentRelativeTo_iff_of_intermediate_isPseudoCoherentRelativeTo
      (R := R) (A := P) (B := A) K m hP).2 hK_rel_P

/-- Helper for Lemma 15.82.16: a finite family whose span is the unit ideal admits explicit
coefficients summing to `1`. -/
private theorem unitIdeal_exists_coefficients
    (f : ι → A) (hunit : Ideal.span (Set.range f) = ⊤) :
    by
      let _ : Fintype ι := Fintype.ofFinite ι
      exact ∃ g : ι → A, ∑ i, f i * g i = 1 := by
  let _ : Fintype ι := Fintype.ofFinite ι
  have hone : (1 : A) ∈ Ideal.span (Set.range f) := by
    -- Proof comment: `1` belongs to the span exactly because the family generates the unit ideal.
    simpa [hunit] using show (1 : A) ∈ (⊤ : Ideal A) from by trivial
  obtain ⟨g, hg⟩ := Ideal.mem_span_range_iff_exists_fun.mp hone
  refine ⟨g, ?_⟩
  -- Proof comment: commutativity lets us rewrite the standard span certificate into the source
  -- textbook form `∑ f_i g_i = 1`.
  simpa [mul_comm] using hg

/-- Helper for Lemma 15.82.16: imposing one indexed unit relation on chosen lifts of the cover
generators forces their quotient images to span the unit ideal. -/
private theorem span_top_of_indexed_single_relation_quotient_lifts
    {σ : Type*} [Fintype σ] {S : Type*} [CommRing S]
    (aLift cLift : σ → S) :
    let u : S := (∑ i, aLift i * cLift i) - 1
    let I : Ideal S := Ideal.span ({u} : Set S)
    let B := S ⧸ I
    let gLift : σ → B := fun i ↦ Ideal.Quotient.mk I (aLift i)
    Ideal.span (Set.range gLift) = ⊤ := by
  classical
  let u : S := (∑ i, aLift i * cLift i) - 1
  let I : Ideal S := Ideal.span ({u} : Set S)
  let B := S ⧸ I
  let gLift : σ → B := fun i ↦ Ideal.Quotient.mk I (aLift i)
  rw [Ideal.eq_top_iff_one]
  have hu_zero : (Ideal.Quotient.mk I u : B) = 0 := by
    -- Proof comment: the defining hypersurface relation vanishes in the quotient by construction.
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp [u]))
  have hsum_eq :
      ∑ i, gLift i * (Ideal.Quotient.mk I (cLift i) : B) = 1 := by
    -- Proof comment: rewriting the quotient image of the defining relation isolates the desired
    -- unit combination of the quotient lifts.
    have hu_sum :
        (Ideal.Quotient.mk I u : B) =
          (∑ i, gLift i * (Ideal.Quotient.mk I (cLift i) : B)) - 1 := by
      simp [u, gLift, map_sum, mul_comm, mul_left_comm, mul_assoc]
    rw [hu_sum] at hu_zero
    exact sub_eq_zero.mp hu_zero
  -- Proof comment: each summand belongs to the ideal generated by the quotient lifts, so their
  -- sum gives the unit.
  refine hsum_eq ▸ Submodule.sum_mem _ ?_
  intro i hi
  have hg : gLift i ∈ Ideal.span (Set.range gLift) := Ideal.subset_span (Set.mem_range_self i)
  exact Ideal.mul_mem_right _ _ hg

/-- Helper for Lemma 15.82.16: a one-relation quotient of a finitely generated polynomial ring
is finitely presented over the base ring. -/
private theorem finitePresentation_of_single_relation_mvPolynomial_quotient
    {σ : Type*} [Finite σ] (u : MvPolynomial σ R) :
    Algebra.FinitePresentation R
      (MvPolynomial σ R ⧸ Ideal.span ({u} : Set (MvPolynomial σ R))) := by
  let _ : Fintype σ := Fintype.ofFinite σ
  let P := MvPolynomial σ R
  let I : Ideal P := Ideal.span ({u} : Set P)
  letI : Algebra.FinitePresentation R P := by
    -- Proof comment: a polynomial ring in finitely many variables over `R` is finitely
    -- presented over `R`.
    simpa [P] using
      (Algebra.FinitePresentation.mvPolynomial_of_finitePresentation (R := R) (A := R) σ)
  have hI : I.FG := by
    -- Proof comment: the defining hypersurface ideal is generated by a single polynomial.
    simpa [I] using (Submodule.fg_span (Set.finite_singleton u) : I.FG)
  -- Proof comment: quotient finite presentation along the singly generated relation ideal.
  simpa [P, I] using
    (Algebra.FinitePresentation.quotient (R := R) (A := P) (I := I) hI)

/-- Helper for Lemma 15.82.16: if a one-relation quotient polynomial has unit constant term, then
the quotient regular module should be pseudo-coherent over the source polynomial ring. -/
private theorem mvPolynomial_eq_zero_of_mul_eq_zero_of_isUnit_constantCoeff
    {σ : Type*} [Fintype σ] (u p : MvPolynomial σ R)
    (hu : IsUnit (MvPolynomial.constantCoeff u))
    (h : p * u = 0) :
    p = 0 := by
  classical
  let weight : (σ →₀ ℕ) → ℕ := fun d ↦ d.sum fun _ n ↦ n
  have hweight_add : ∀ a b : σ →₀ ℕ, weight (a + b) = weight a + weight b := by
    intro a b
    simp [weight, Finsupp.sum_add_index]
  have hweight_pos : ∀ {a : σ →₀ ℕ}, a ≠ 0 → 0 < weight a := by
    intro a ha
    rcases Finsupp.support_nonempty_iff.mpr ha with ⟨i, hi⟩
    have hi' : a i ≠ 0 := Finsupp.mem_support_iff.mp hi
    have hle : a i ≤ weight a := by
      classical
      simpa [weight] using
        (Finset.single_le_sum
          (fun j _ ↦ Nat.zero_le (a j))
          hi)
    exact lt_of_lt_of_le (Nat.pos_of_ne_zero hi') hle
  have hcoeff_zero : ∀ n : ℕ, ∀ d : σ →₀ ℕ, weight d = n → MvPolynomial.coeff d p = 0 := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ihn d hd
    have hcoeff_mul : MvPolynomial.coeff d (p * u) = 0 := by
      simpa [h]
    rw [MvPolynomial.coeff_mul] at hcoeff_mul
    rw [Finset.sum_eq_single (d, 0)] at hcoeff_mul
    · have hunit_term : MvPolynomial.coeff d p * MvPolynomial.constantCoeff u = 0 := by
        simpa [MvPolynomial.constantCoeff] using hcoeff_mul
      rcases hu with ⟨c, hc⟩
      rw [hc] at hunit_term
      have hmul :=
        congrArg (fun x : R ↦ x * ↑c⁻¹) hunit_term
      simpa [mul_assoc] using hmul
    · intro de hde hne
      have hsum : de.1 + de.2 = d := by
        simpa using (Finset.mem_antidiagonal.mp hde)
      have hright_ne_zero : de.2 ≠ 0 := by
        intro hzero
        apply hne
        ext <;> simp [hsum, hzero]
      have hlt : weight de.1 < weight d := by
        have hpos : 0 < weight de.2 := hweight_pos hright_ne_zero
        have hwt : weight d = weight de.1 + weight de.2 := by
          simpa [hsum] using hweight_add de.1 de.2
        omega
      have hleft_zero : MvPolynomial.coeff de.1 p = 0 := by
        exact ihn (weight de.1) hlt de.1 rfl
      simp [hleft_zero]
    · have hmem : ((d, 0) : (σ →₀ ℕ) × (σ →₀ ℕ)) ∈ Finset.antidiagonal d := by
        simpa using (Finset.mem_antidiagonal.mpr (add_zero d))
      simpa using hmem
  ext d
  exact hcoeff_zero (weight d) d rfl

/-- Helper for Lemma 15.82.16: multiplication by a multivariable polynomial with unit constant
coefficient is injective. -/
private theorem mvPolynomial_mul_right_injective_of_isUnit_constantCoeff
    {σ : Type*} [Fintype σ] (u : MvPolynomial σ R)
    (hu : IsUnit (MvPolynomial.constantCoeff u)) :
    Function.Injective (fun p : MvPolynomial σ R ↦ p * u) := by
  intro p q hpq
  have hsub : (p - q) * u = 0 := by
    rw [sub_mul, hpq, sub_self]
  have hzero :
      p - q = 0 :=
    mvPolynomial_eq_zero_of_mul_eq_zero_of_isUnit_constantCoeff (R := R) u (p - q) hu hsub
  exact sub_eq_zero.mp hzero

private theorem indexed_single_relation_quotient_regularModule_isPseudoCoherent
    {σ : Type*} [Finite σ] (u : MvPolynomial σ R)
    (hu : IsUnit (MvPolynomial.constantCoeff u)) :
    (ModuleCat.of (MvPolynomial σ R)
      (MvPolynomial σ R ⧸ Ideal.span ({u} : Set (MvPolynomial σ R)))).IsPseudoCoherent := by
  let _ : Fintype σ := Fintype.ofFinite σ
  let P₀ : FiniteProjectiveModuleCat (MvPolynomial σ R) :=
    ⟨ModuleCat.of (MvPolynomial σ R) (MvPolynomial σ R), inferInstance⟩
  let I : Ideal (MvPolynomial σ R) :=
    Ideal.span ({u} : Set (MvPolynomial σ R))
  let δ₀ : P₀.obj ⟶ P₀.obj :=
    { toFun := fun p ↦ p * u
      map_add' := fun p q ↦ by
        simp [add_mul]
      map_smul' := fun a p ↦ by
        -- Proof comment: scalar multiplication on the regular module is ring multiplication, so
        -- linearity is just associativity.
        change (a * p) * u = a * (p * u)
        rw [mul_assoc] }
  let π : P₀.obj ⟶
      ModuleCat.of (MvPolynomial σ R) ((MvPolynomial σ R) ⧸ I) :=
    (Ideal.Quotient.mk I).toLinearMap
  have hPerfect :
      (ModuleCat.of (MvPolynomial σ R)
        ((MvPolynomial σ R) ⧸ Ideal.span ({u} : Set (MvPolynomial σ R)))).IsPerfect := by
    -- Proof comment: the hypersurface quotient has the explicit length-one free resolution
    -- `P --(·u)→ P → P/(u) → 0`.
    rw [ModuleCat.isPerfect_iff_exists_finiteProjectiveResolutionLengthLEWithFiniteTerms]
    refine ⟨1, ?_⟩
    refine ⟨fun _ ↦ P₀, fun _ ↦ δ₀, π, ?_, ?_, ?_, ?_⟩
    · -- Proof comment: the quotient map is surjective by definition of the ideal quotient.
      simpa [π] using
        (Ideal.Quotient.mk_surjective :
          Function.Surjective (Ideal.Quotient.mk I))
    · -- Proof comment: the kernel of the quotient map is the principal ideal generated by `u`,
      -- hence the image of multiplication by `u`.
      intro p
      constructor
      · intro hp
        rw [Ideal.Quotient.eq_zero_iff_mem] at hp
        rcases Ideal.mem_span_singleton.mp hp with ⟨q, hq⟩
        exact ⟨q, by simpa [δ₀, mul_comm] using hq.symm⟩
      · rintro ⟨q, rfl⟩
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        exact Ideal.mul_mem_right I q (Ideal.subset_span (by simp))
    · -- Proof comment: there is no higher exactness condition in length `1`.
      intro i
      exact Fin.elim0 i
    · -- Proof comment: injectivity of multiplication by `u` follows from the unit constant term.
      simpa [δ₀] using mvPolynomial_mul_right_injective_of_isUnit_constantCoeff (R := R) u hu
  -- Proof comment: pseudo-coherence is the pseudo-coherent half of perfectness.
  exact
    (ModuleCat.isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension _).1
      hPerfect |>.1

/-- Helper for Lemma 15.82.16: the source hypersurface construction yields a finite type
intermediate algebra `P` surjecting onto `A` whose chosen lifts of the `f_i` already generate the
unit ideal. -/
private theorem exists_hypersurface_cover_with_unit_ideal_lifts
    (f : ι → A) (hunit : Ideal.span (Set.range f) = ⊤) :
    ∃ (P : Type (max u v)) (_ : CommRing P) (_ : Algebra R P) (_ : Algebra P A)
      (_ : IsScalarTower R P A) (_ : Algebra.FiniteType R P) (_ : Algebra.FiniteType P A),
      Function.Surjective (algebraMap P A) ∧
        ∃ p : ι → P, (∀ i, algebraMap P A (p i) = f i) ∧ Ideal.span (Set.range p) = ⊤ := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  obtain ⟨g, hg⟩ := unitIdeal_exists_coefficients (A := A) f hunit
  obtain ⟨n, α, hα⟩ :=
    Algebra.FiniteType.iff_quotient_mvPolynomial''.1 (inferInstance : Algebra.FiniteType R A)
  let Vars := (Fin n) ⊕ (ι ⊕ ι)
  let S : Type (max u v) := MvPolynomial Vars R
  let aLift : ι → S := fun i ↦ MvPolynomial.X (Sum.inr (Sum.inl i))
  let cLift : ι → S := fun i ↦ MvPolynomial.X (Sum.inr (Sum.inr i))
  let v : Vars → A
    | Sum.inl j => α (MvPolynomial.X j)
    | Sum.inr (Sum.inl i) => f i
    | Sum.inr (Sum.inr i) => g i
  let β : S →ₐ[R] A := MvPolynomial.eval₂AlgHom (algebraMap R A) v
  let u : S := (∑ i, aLift i * cLift i) - 1
  let I : Ideal S := Ideal.span ({u} : Set S)
  let P : Type (max u v) := S ⧸ I
  have hIker : I ≤ RingHom.ker β.toRingHom := by
    -- Proof comment: evaluating the hypersurface relation in `A` recovers the chosen identity
    -- `∑ f_i g_i = 1`, so the quotient map descends.
    refine Ideal.span_le.2 ?_
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    simpa [RingHom.mem_ker, u, β, v, aLift, cLift, map_sum, map_sub, mul_comm, mul_left_comm,
      mul_assoc] using hg
  let φ : P →ₐ[R] A :=
    Ideal.Quotient.liftₐ I β <| by
      intro z hz
      simpa [RingHom.mem_ker] using hIker hz
  have hφ_surj : Function.Surjective φ := by
    -- Proof comment: the enlarged polynomial ring still surjects onto `A` because the original
    -- presentation `α` is recovered by forgetting the new variables.
    intro a
    rcases hα a with ⟨q, rfl⟩
    refine ⟨Ideal.Quotient.mk I (MvPolynomial.rename Sum.inl q), ?_⟩
    change β (MvPolynomial.rename Sum.inl q) = α q
    simp [β, v]
  letI : Algebra P A := φ.toAlgebra
  letI : IsScalarTower R P A := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra.FiniteType R S := by infer_instance
  letI : Algebra.FiniteType S P :=
    Algebra.FiniteType.of_surjective (algebraMap S P) Ideal.Quotient.mk_surjective
  letI : Algebra.FiniteType R P :=
    Algebra.FiniteType.trans
      (inferInstance : Algebra.FiniteType R S)
      (inferInstance : Algebra.FiniteType S P)
  letI : Algebra.FiniteType P A :=
    Algebra.FiniteType.of_surjective (algebraMap P A) hφ_surj
  let p : ι → P := fun i ↦ Ideal.Quotient.mk I (aLift i)
  have hp : ∀ i, algebraMap P A (p i) = f i := by
    -- Proof comment: the quotient lift sends the distinguished `y_i` variable to the original
    -- cover element `f_i`.
    intro i
    change β (aLift i) = f i
    simp [β, v, aLift]
  have hspan : Ideal.span (Set.range p) = ⊤ := by
    -- Proof comment: the quotient still satisfies the unit relation witnessed by the `z_i`
    -- variables, so the images of the `y_i` generate the unit ideal.
    simpa [u, I, P, p, aLift, cLift] using
      span_top_of_indexed_single_relation_quotient_lifts (aLift := aLift) (cLift := cLift)
  exact ⟨P, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, hφ_surj, p, hp, hspan⟩

/-- Helper for Lemma 15.82.16: localizing a surjective algebra map along a chosen element remains
surjective on the corresponding principal-open chart. -/
private theorem localized_awayMap_surjective_of_surjective
    {B : Type*} [CommRing B] [Algebra R B] (φ : B →ₐ[R] A)
    (hφ : Function.Surjective φ) (g : B) :
    Function.Surjective (Localization.awayMapₐ φ g) := by
  intro z
  rcases (IsLocalization.mk'_surjective (Submonoid.powers (φ g)) z) with ⟨⟨a, y⟩, rfl⟩
  rcases hφ a with ⟨b, rfl⟩
  rcases y with ⟨y, hy⟩
  rcases hy with ⟨n, rfl⟩
  let hyMap :
      Submonoid.powers g ≤ Submonoid.comap φ.toRingHom (Submonoid.powers (φ g)) := by
    -- Proof comment: powers of `g` map to powers of `φ g`, so the away map is defined on the
    -- chosen denominator.
    intro x hx
    rcases hx with ⟨m, rfl⟩
    exact ⟨m, by simp⟩
  refine ⟨IsLocalization.mk' (Localization.Away g) b
      ⟨g ^ n, show g ^ n ∈ Submonoid.powers g from ⟨n, rfl⟩⟩, ?_⟩
  -- Proof comment: on standard fraction representatives, the localized away map acts by applying
  -- `φ` to the numerator and leaving the denominator power unchanged.
  simpa [Localization.awayMapₐ, hyMap] using
    (IsLocalization.map_mk' (Q := Localization.Away (φ g)) hyMap b
      ⟨g ^ n, show g ^ n ∈ Submonoid.powers g from ⟨n, rfl⟩⟩)

/-- Helper for Lemma 15.82.16: the source-faithful hypersurface presentation should package the
given local relative hypotheses into an intermediate finite type `R`-algebra with a principal-open
cover on which the restricted complex is absolutely `m`-pseudo-coherent. -/
private theorem exists_hypersurface_localization_cover
    (f : ι → A) (hunit : Ideal.span (Set.range f) = ⊤) (K : DModA) (m : ℤ)
    (hloc : ∀ i, (K ⊗[A]^L[Localization.Away (f i)]).IsMPseudoCoherentRelativeTo R m) :
    ∃ (P : Type (max u v)) (_ : CommRing P) (_ : Algebra R P) (_ : Algebra P A)
      (_ : IsScalarTower R P A) (_ : Algebra.FiniteType R P) (_ : Algebra.FiniteType P A),
      Function.Surjective (algebraMap P A) ∧
        (ModuleCat.of P P).IsPseudoCoherentRelativeTo R ∧
          ∃ p : ι → P, Ideal.span (Set.range p) = ⊤ ∧
            ∀ i,
              (((ModuleCat.restrictScalars (algebraMap P A)).mapDerivedCategory.obj K)
                ⊗[P]^L[Localization.Away (p i)]).IsMPseudoCoherent := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  obtain ⟨g, hg⟩ := unitIdeal_exists_coefficients (A := A) f hunit
  obtain ⟨n, α, hα⟩ :=
    Algebra.FiniteType.iff_quotient_mvPolynomial''.1 (inferInstance : Algebra.FiniteType R A)
  let Vars := (Fin n) ⊕ (ι ⊕ ι)
  let S : Type (max u v) := MvPolynomial Vars R
  let aLift : ι → S := fun i ↦ MvPolynomial.X (Sum.inr (Sum.inl i))
  let cLift : ι → S := fun i ↦ MvPolynomial.X (Sum.inr (Sum.inr i))
  let v : Vars → A
    | Sum.inl j => α (MvPolynomial.X j)
    | Sum.inr (Sum.inl i) => f i
    | Sum.inr (Sum.inr i) => g i
  let β : S →ₐ[R] A := MvPolynomial.eval₂AlgHom (algebraMap R A) v
  let rel : S := (∑ i, aLift i * cLift i) - 1
  let I : Ideal S := Ideal.span ({rel} : Set S)
  let P : Type (max u v) := S ⧸ I
  have hIker : I ≤ RingHom.ker β.toRingHom := by
    -- Proof comment: evaluating the hypersurface relation in `A` recovers the chosen identity
    -- `∑ f_i g_i = 1`, so the quotient map to `A` is well defined.
    refine Ideal.span_le.2 ?_
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    simpa [RingHom.mem_ker, rel, β, v, aLift, cLift, map_sum, map_sub, mul_comm, mul_left_comm,
      mul_assoc] using hg
  let φ : P →ₐ[R] A :=
    Ideal.Quotient.liftₐ I β <| by
      intro z hz
      simpa [RingHom.mem_ker] using hIker hz
  have hφ_surj : Function.Surjective φ := by
    -- Proof comment: the original polynomial presentation of `A` factors through the enlarged
    -- hypersurface presentation after forgetting the added `y` and `z` variables.
    intro a
    rcases hα a with ⟨q, rfl⟩
    refine ⟨Ideal.Quotient.mk I (MvPolynomial.rename Sum.inl q), ?_⟩
    change β (MvPolynomial.rename Sum.inl q) = α q
    simp [β, v]
  letI : CommRing P := Ideal.Quotient.commRing I
  letI : Algebra R P := (Ideal.Quotient.mkₐ R I).toAlgebra
  letI : Algebra P A := φ.toAlgebra
  letI : IsScalarTower R P A := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra.FiniteType R S := by infer_instance
  letI : Algebra.FiniteType S P :=
    Algebra.FiniteType.of_surjective (algebraMap S P) Ideal.Quotient.mk_surjective
  letI : Algebra.FiniteType R P :=
    Algebra.FiniteType.trans
      (inferInstance : Algebra.FiniteType R S)
      (inferInstance : Algebra.FiniteType S P)
  letI : Algebra.FiniteType P A :=
    Algebra.FiniteType.of_surjective (algebraMap P A) hφ_surj
  let p : ι → P := fun i ↦ Ideal.Quotient.mk I (aLift i)
  have hp : ∀ i, algebraMap P A (p i) = f i := by
    -- Proof comment: the quotient lift sends the distinguished `y_i` variable to the original
    -- cover element `f_i`.
    intro i
    change β (aLift i) = f i
    simp [β, v, aLift]
  have hunitP : Ideal.span (Set.range p) = ⊤ := by
    -- Proof comment: the defining relation still witnesses a unit combination of the quotient
    -- lifts of the `y_i`.
    simpa [rel, I, P, p, aLift, cLift] using
      span_top_of_indexed_single_relation_quotient_lifts (aLift := aLift) (cLift := cLift)
  have hPfp : Algebra.FinitePresentation R P := by
    -- Proof comment: the fixed hypersurface algebra is already a one-relation quotient of a
    -- finitely generated polynomial ring over `R`.
    simpa [S, I, P] using
      finitePresentation_of_single_relation_mvPolynomial_quotient (R := R) (σ := Vars) rel
  have hP : (ModuleCat.of P P).IsPseudoCoherentRelativeTo R := by
    let _ : Fintype Vars := Fintype.ofFinite Vars
    let eVars : MvPolynomial (Fin (Fintype.card Vars)) R ≃ₐ[R] S :=
      (MvPolynomial.renameEquiv R (Fintype.equivFin Vars).symm)
    have hrelUnit : IsUnit (MvPolynomial.constantCoeff rel) := by
      -- Proof comment: every product `aLift i * cLift i` has zero constant term, so the
      -- hypersurface relation has constant coefficient `-1`.
      simpa [rel, aLift, cLift] using (isUnit_one.neg : IsUnit (-(1 : R)))
    let αP : MvPolynomial (Fin (Fintype.card Vars)) R →ₐ[R] P :=
      (algebraMap S P).comp eVars.toAlgHom
    have hαP : Function.Surjective αP := by
      intro x
      rcases Ideal.Quotient.mk_surjective x with ⟨s, rfl⟩
      rcases eVars.surjective s with ⟨q, rfl⟩
      exact ⟨q, rfl⟩
    have hSP :
        ((ModuleCat.restrictScalars (algebraMap S P)).obj
          (ModuleCat.of P P)).IsPseudoCoherent := by
      -- Proof comment: the one-relation quotient over the ambient polynomial ring has the
      -- explicit two-term free resolution proved above.
      simpa [S, P, I] using
        indexed_single_relation_quotient_regularModule_isPseudoCoherent
          (R := R) (σ := Vars) rel hrelUnit
    have hαPreg :
        ((ModuleCat.restrictScalars αP.toRingHom).obj
          (ModuleCat.of P P)).IsPseudoCoherent := by
      -- Proof comment: reindex the finite variable set `Vars` by `Fin (card Vars)` and transport
      -- pseudo-coherence across that polynomial-ring equivalence.
      rw [moduleCat_isPseudoCoherent_iff_forall_isMPseudoCoherent] at hSP ⊢
      intro m
      -- Proof comment: the restriction comparison along a ring equivalence is the canonical local
      -- change-of-rings theorem from Lemma `15.82.15`.
      simpa [ModuleCat.IsMPseudoCoherent, αP, eVars] using
        (isMPseudoCoherent_iff_restrictScalars_local eVars.toRingHom
          ((DerivedCategory.singleFunctor (ModuleCat P) (0 : ℤ)).obj (ModuleCat.of P P))
          m
          (restrictScalars_regularModule_isPseudoCoherent_of_ringEquiv eVars.toRingEquiv)).2
          (hSP m)
    -- Proof comment: the reindexed quotient map is a surjective polynomial presentation of `P`
    -- over `R`, so it witnesses relative pseudo-coherence of the regular `P`-module.
    rw [ModuleCat.IsPseudoCoherentRelativeTo,
      CochainComplex.isPseudoCoherentRelativeTo_iff_overSomePolynomialPresentation]
    refine ⟨Fintype.card Vars, αP, hαP, ?_⟩
    simpa [ModuleCat.IsPseudoCoherent, CochainComplex.polynomialPresentationRestriction] using hαPreg
  have hploc :
      ∀ i,
        (((ModuleCat.restrictScalars (algebraMap P A)).mapDerivedCategory.obj K)
          ⊗[P]^L[Localization.Away (p i)]).IsMPseudoCoherent := by
    intro i
    let Pᵢ : Type (max u v) := Localization.Away (p i)
    let Aᵢ : Type v := Localization.Away (f i)
    let φᵢ : Pᵢ →ₐ[R] Aᵢ := Localization.awayMapₐ φ (p i)
    have hφᵢ_surj : Function.Surjective φᵢ := by
      -- Proof comment: the localized hypersurface chart still surjects onto the localized
      -- `A`-chart because the original quotient map `φ : P → A` is surjective.
      exact localized_awayMap_surjective_of_surjective (R := R) (A := A) φ hφ_surj (p i)
    have hφᵢp :
        φᵢ (algebraMap P Pᵢ (p i)) = algebraMap A Aᵢ (f i) := by
      -- Proof comment: the distinguished lifted generator `p i` maps to `f i`, so the localized
      -- chart morphism carries the inverted element to the inverted target generator.
      simpa [φᵢ, hp i]
    -- Route correction: the remaining local chart step is now isolated to one source-faithful
    -- comparison. It needs:
    -- 1. the localized regular-module bridge giving `Pᵢ` pseudo-coherent relative to `R`; and
    -- 2. the derived tensor/restriction iso identifying the target object with the restriction of
    --    `K ⊗[A]^L Aᵢ` along `φᵢ`.
    let _ : Function.Surjective φᵢ := hφᵢ_surj
    let _ := hφᵢp
    let _ := hloc i
    sorry
  exact ⟨P, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, hφ_surj, hP, p, hunitP, hploc⟩

/-- Lemma 15.82.16 (1): for a finite type ring map `R → A`, a derived `A`-complex `K^•`, an
integer `m`, and finitely many elements `f i : A` generating the unit ideal, `K^•` is
`m`-pseudo-coherent relative to `R` if and only if each principal localization
`K^• \otimes_A^{\mathbf L} A_{f i}` is `m`-pseudo-coherent relative to `R`. -/
@[stacks 067E]
theorem isMPseudoCoherentRelativeTo_iff_localizationAway_unitIdeal
    (f : ι → A) (hunit : Ideal.span (Set.range f) = ⊤) (K : DModA) (m : ℤ) :
    (∀ i, (K ⊗[A]^L[Localization.Away (f i)]).IsMPseudoCoherentRelativeTo R m) ↔
      K.IsMPseudoCoherentRelativeTo R m := by
  constructor
  · intro hloc
    rcases exists_hypersurface_localization_cover (R := R) (A := A) f hunit K m hloc with
      ⟨P, _instCommRingP, _instAlgRP, _instAlgPA, _instTower, _instFiniteTypeRP,
        _instFiniteTypePA, hsurj, hP, p, hunitP, hploc⟩
    -- Proof comment: once the source-faithful hypersurface package exists, the remaining descent
    -- is exactly the generic intermediate-ring local-global argument above.
    exact
      isMPseudoCoherentRelativeTo_of_intermediate_localizationAway_unitIdeal
        (R := R) (A := A) (ι := ι) (P := P) hP hsurj p hunitP K m hploc
  · intro hK i
    let eAway : R ≃ₐ[R] Localization.Away (1 : R) :=
      IsLocalization.atUnit R (Localization.Away (1 : R)) 1 isUnit_one
    letI : Algebra (Localization.Away (1 : R)) R := eAway.symm.toAlgHom.toAlgebra
    letI : Algebra (Localization.Away (1 : R)) A :=
      ((algebraMap R A).comp eAway.symm.toRingHom).toAlgebra
    letI : IsScalarTower R (Localization.Away (1 : R)) A :=
      IsScalarTower.of_algebraMap_eq' <| by
        ext r
        have hcomm : eAway r = algebraMap R (Localization.Away (1 : R)) r := by
          simpa using eAway.commutes r
        calc
          (algebraMap R A) (eAway.symm (algebraMap R (Localization.Away (1 : R)) r)) =
              (algebraMap R A) (eAway.symm (eAway r)) := by rw [hcomm]
          _ = algebraMap R A r := by rw [AlgEquiv.apply_symm_apply]
    letI : Algebra.FiniteType (Localization.Away (1 : R)) R :=
      Algebra.FiniteType.of_surjective (algebraMap (Localization.Away (1 : R)) R)
        eAway.symm.surjective
    letI : Algebra.FiniteType (Localization.Away (1 : R)) A :=
      Algebra.FiniteType.trans
        (inferInstance : Algebra.FiniteType (Localization.Away (1 : R)) R)
        (inferInstance : Algebra.FiniteType R A)
    have hKAway : K.IsMPseudoCoherentRelativeTo (Localization.Away (1 : R)) m := by
      -- Proof comment: first replace the base ring by the equivalent localization `R[1⁻¹]`.
      exact (isMPseudoCoherentRelativeTo_iff_localizationAway_one K m).2 hK
    -- Proof comment: after the base change to `R[1⁻¹]`, the localization statement is exactly
    -- Lemma `15.82.11` with `f = 1`.
    exact
      isMPseudoCoherentRelativeTo_localizationAway_from_localizedBase
        (R := R) (A := A) (f := (1 : R)) (g := f i) K m hKAway

-- Proof sketch: combine part `(1)` for every integer `m` with the definitions of relative
-- pseudo-coherence and ordinary pseudo-coherence as `m`-pseudo-coherence in all degrees.
/-- Lemma 15.82.16 (2): under the same hypotheses, `K^•` is pseudo-coherent relative to `R` if
and only if each principal localization `K^• \otimes_A^{\mathbf L} A_{f i}` is pseudo-coherent
relative to `R`. -/
@[stacks 067E]
theorem isPseudoCoherentRelativeTo_iff_localizationAway_unitIdeal
    (f : ι → A) (hunit : Ideal.span (Set.range f) = ⊤) (K : DModA) :
    (∀ i, (K ⊗[A]^L[Localization.Away (f i)]).IsPseudoCoherentRelativeTo R) ↔
      K.IsPseudoCoherentRelativeTo R := by
  constructor
  · intro hK m
    exact (isMPseudoCoherentRelativeTo_iff_localizationAway_unitIdeal f hunit K m).mp
      (fun i ↦ hK i m)
  · intro hK i m
    exact ((isMPseudoCoherentRelativeTo_iff_localizationAway_unitIdeal f hunit K m).mpr
      (hK m)) i

end

end CategoryTheory
