import Mathlib
import StacksProject_2024.Chap15.«15_60_1_1»
import StacksProject_2024.Chap15.«15_61_0_1»
import StacksProject_2024.Chap15.Definition_15_83_1
import StacksProject_2024.Chap15.Lemma_15_65_12
import StacksProject_2024.Chap15.Lemma_15_65_11
import StacksProject_2024.Chap15.Lemma_15_81_6
import StacksProject_2024.Chap15.Lemma_15_82_10

noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R A B : Type u}
variable [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
variable [Algebra.FiniteType R A]
variable [(algebraMap A B).IsPseudoCoherentRingMap]

local notation "DModA" => DerivedCategory (ModuleCat A)

/- Domain-style sampling for Lemma 15.82.13:
- primary domain: relative pseudo-coherence in derived categories under derived scalar extension
  along a pseudo-coherent ring map;
- sampled owner declarations:
  `DerivedCategory.IsMPseudoCoherentRelativeTo`,
  `DerivedCategory.IsPseudoCoherentRelativeTo`,
  `derivedTensorWithAlgebra`,
  `RingHom.IsPseudoCoherentRingMap`;
- best owner abstraction: this file is `source-facing`, while the canonical owners are the
  relative pseudo-coherence predicates on `DerivedCategory (ModuleCat A)` together with the
  derived scalar-extension owner `derivedTensorWithAlgebra`;
- primitive vs. derived:
  primitive data are the finite-type hypothesis on `R → A` and the pseudo-coherent ring-map
  hypothesis on `A → B`;
  the finite-type structure on `R → B` is derived by transitivity and should not remain primitive
  public data.
-/

-- Proof sketch: fix a surjective polynomial presentation of `A` over `R`, adjoin finitely many
-- variables to obtain a polynomial presentation of `B`, and use the pseudo-coherent ring-map
-- hypothesis to choose a finite free resolution of `B` over that intermediate polynomial algebra.
-- Rewrite derived tensor product with `B` as the total complex of tensoring `K` with this
-- resolution, then combine Lemma `15.82.12` with the distinguished-triangle closure of relative
-- `m`-pseudo-coherence from Lemma `15.82.6`.
/-- Helper for Lemma 15.82.13: relative `m`-pseudo-coherence of a derived `A`-complex can be
checked on one surjective polynomial presentation of `A` over `R`. -/
lemma derived_isMPseudoCoherentRelativeTo_iff_overSomePolynomialPresentation
    (K : DModA) (m : ℤ) :
    K.IsMPseudoCoherentRelativeTo R m ↔
      ∃ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A),
        Function.Surjective α ∧
          ((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj K).IsMPseudoCoherent m := by
  let E := DerivedCategory.Q.objPreimage K
  let eK : DerivedCategory.Q.obj E ≅ K := DerivedCategory.Q.objObjPreimageIso K
  let presentationIso := fun {n : ℕ} (α : MvPolynomial (Fin n) R →ₐ[R] A) ↦
    (((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory).mapIso eK.symm) ≪≫
      (ModuleCat.restrictScalars α.toRingHom).mapDerivedCategoryFactors.app E
  have hrel :
      K.IsMPseudoCoherentRelativeTo R m ↔ E.IsMPseudoCoherentRelativeTo R m := by
    constructor
    · intro hK n α hα
      -- Proof comment: compare the restricted derived object with the chosen restricted cochain
      -- representative and transport `m`-pseudo-coherence across that canonical isomorphism.
      exact isMPseudoCoherent_of_iso (presentationIso α) m (hK n α hα)
    · intro hE n α hα
      -- Proof comment: the same comparison runs in the reverse direction via the inverse
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
            ((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj K).IsMPseudoCoherent m := by
      constructor
      · rintro ⟨n, α, hα, hEα⟩
        -- Proof comment: turn the strict restricted complex back into the restricted derived
        -- object using the same `Q.objPreimage` comparison.
        exact ⟨n, α, hα, isMPseudoCoherent_of_iso (presentationIso α).symm m hEα⟩
      · rintro ⟨n, α, hα, hKα⟩
        -- Proof comment: conversely, move the derived hypothesis onto the strict restricted
        -- representative.
        exact ⟨n, α, hα, isMPseudoCoherent_of_iso (presentationIso α) m hKα⟩

/-- Helper for Lemma 15.82.13: above degree `0`, the homology of a degree-zero complex vanishes. -/
lemma single_zero_complex_homology_isZero_of_pos
    {S : Type u} [CommRing S] (M : ModuleCat S) (i : ℤ) (hi : 0 < i) :
    IsZero (((CochainComplex.singleFunctor (ModuleCat S) (0 : ℤ)).obj M).homology i) := by
  -- Proof comment: in positive degree the single complex has zero middle term, so its homology
  -- vanishes by the defining short-complex computation.
  simpa using
    (ShortComplex.isZero_homology_of_isZero_X₂
      (S := ((CochainComplex.singleFunctor (ModuleCat S) (0 : ℤ)).obj M).sc i)
      (by simpa using
        ((CochainComplex.singleFunctor (ModuleCat S) (0 : ℤ)).obj M).isZero_of_isStrictlyLE
          0 i hi))

/-- Helper for Lemma 15.82.13: restricting the regular module along a ring equivalence preserves
absolute pseudo-coherence. -/
private lemma restrictScalars_regularModule_isPseudoCoherent_of_ringEquiv
    {S T : Type u} [CommRing S] [CommRing T] (e : S ≃+* T) :
    ((ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of T T)).IsPseudoCoherent := by
  let eₗ :
      ModuleCat.of S S ≃ₗ[S]
        ((ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of T T)) :=
    { __ := e.toAddEquiv
      map_smul' := fun r s ↦ e.map_mul r s }
  have hPerfect :
      ((ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of T T)).IsPerfect := by
    -- Proof comment: after restricting along a ring equivalence, the regular `T`-module is still
    -- the free rank-one module over `S`.
    rw [ModuleCat.isPerfect_iff_exists_finiteProjectiveResolutionLengthLEWithFiniteTerms]
    refine ⟨0, ?_⟩
    rw [ModuleCat.hasFiniteProjectiveResolutionLengthLEWithFiniteTerms_zero_iff]
    constructor
    · exact Module.Projective.of_equiv eₗ
    · exact Module.Finite.equiv eₗ
  exact
    (ModuleCat.isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension _).1 hPerfect |>.1

/-- Helper for Lemma 15.82.13: exact restriction of scalars commutes with derived tensor
products. -/
private noncomputable def restrict_scalars_derivedTensorProduct_iso
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T]
    (K L : DerivedCategory (ModuleCat T)) :
    (((ModuleCat.restrictScalars (algebraMap S T)).mapDerivedCategory).obj
      (K ⊗[T]^L L)) ≅
      ((((ModuleCat.restrictScalars (algebraMap S T)).mapDerivedCategory).obj K) ⊗[S]^L
        (((ModuleCat.restrictScalars (algebraMap S T)).mapDerivedCategory).obj L)) := by
  let res : DerivedCategory (ModuleCat T) ⥤ DerivedCategory (ModuleCat S) :=
    (ModuleCat.restrictScalars (algebraMap S T)).mapDerivedCategory
  -- Proof comment: rewrite both derived tensor products through the monoidal tensor on the
  -- derived category, then insert the monoidal comparison for exact restriction of scalars.
  exact
    (res.mapIso (derivedCategory_tensorObj_iso_derivedTensorProduct K L).symm) ≪≫
      (Functor.Monoidal.μIso res K L).symm ≪≫
      (derivedCategory_tensorObj_iso_derivedTensorProduct (res.obj K) (res.obj L))

/-- Helper for Lemma 15.82.13: restricting scalars commutes with the degree-zero derived embedding
of a module. -/
private noncomputable def restrictScalars_single0_iso
    {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T) (M : ModuleCat T) :
    ((ModuleCat.restrictScalars f).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor (ModuleCat T) (0 : ℤ)).obj M)) ≅
      (DerivedCategory.singleFunctor (ModuleCat S) (0 : ℤ)).obj
        ((ModuleCat.restrictScalars f).obj M) :=
  -- Proof comment: compute exact restriction on the strict single complex, then return to the
  -- canonical degree-zero object in the derived category.
  (((ModuleCat.restrictScalars f).mapDerivedCategory).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat T) (0 : ℤ)).app M)) ≪≫
    (ModuleCat.restrictScalars f).mapDerivedCategoryFactors.app
      ((CochainComplex.singleFunctor (ModuleCat T) (0 : ℤ)).obj M) ≪≫
    DerivedCategory.Q.mapIso
      ((Functor.mapCochainComplexSingleFunctor
          (ModuleCat.restrictScalars f)
          (0 : ℤ)).app M) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat S) (0 : ℤ)).app
      ((ModuleCat.restrictScalars f).obj M)).symm

/-- Helper for Lemma 15.82.13: a quasi-isomorphism from a strict complex to a degree-zero complex
identifies its image in the derived category with the corresponding degree-zero object. -/
private noncomputable def quasiIso_single0_iso
    {S : Type u} [CommRing S]
    (E : CochainComplex (ModuleCat S) ℤ) (M : ModuleCat S)
    (η : E ⟶ (CochainComplex.singleFunctor (ModuleCat S) (0 : ℤ)).obj M)
    [QuasiIso η] :
    DerivedCategory.Q.obj E ≅
      (DerivedCategory.singleFunctor (ModuleCat S) (0 : ℤ)).obj M :=
  -- Proof comment: `DerivedCategory.Q` inverts the given quasi-isomorphism, and the target strict
  -- single complex is the usual degree-zero derived object.
  asIso (DerivedCategory.Q.map η) ≪≫
    (DerivedCategory.singleFunctorIsoCompQ (ModuleCat S) (0 : ℤ)).app M

/-- Helper for Lemma 15.82.13: the chosen finite-free resolution of the restricted regular
`B`-module becomes the corresponding restricted degree-zero derived object. -/
private noncomputable def resolution_restrictScalars_single0_iso
    {t : ℕ}
    (β : MvPolynomial (Fin t) A →ₐ[A] B)
    (E : CochainComplex (ModuleCat (MvPolynomial (Fin t) A)) ℤ)
    (η : E ⟶
      (CochainComplex.singleFunctor (ModuleCat (MvPolynomial (Fin t) A)) (0 : ℤ)).obj
        ((ModuleCat.restrictScalars β.toRingHom).obj (ModuleCat.of B B)))
    (hη : QuasiIso η) :
    DerivedCategory.Q.obj E ≅
      ((ModuleCat.restrictScalars β.toRingHom).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat B) (0 : ℤ)).obj (ModuleCat.of B B))) := by
  letI := hη
  -- Proof comment: first identify `Q.obj E` with the degree-zero object of the restricted regular
  -- module, then commute restriction of scalars with that degree-zero embedding.
  exact
    quasiIso_single0_iso E ((ModuleCat.restrictScalars β.toRingHom).obj (ModuleCat.of B B)) η ≪≫
      (restrictScalars_single0_iso β.toRingHom (ModuleCat.of B B)).symm

/-- Helper for Lemma 15.82.13: after restricting the chosen `A[y]`-resolution along a further
polynomial-ring map, the restricted degree-zero regular `B`-module comparison becomes the
corresponding restricted strict complex. -/
private noncomputable def restricted_resolution_restrictScalars_single0_iso
    {P : Type u} [CommRing P] [Algebra P A] [Algebra P B] [IsScalarTower P A B]
    {t : ℕ}
    (q : MvPolynomial (Fin t) P →ₐ[P] MvPolynomial (Fin t) A)
    (β : MvPolynomial (Fin t) A →ₐ[A] B)
    (E : CochainComplex (ModuleCat (MvPolynomial (Fin t) A)) ℤ)
    (η : E ⟶
      (CochainComplex.singleFunctor (ModuleCat (MvPolynomial (Fin t) A)) (0 : ℤ)).obj
        ((ModuleCat.restrictScalars β.toRingHom).obj (ModuleCat.of B B)))
    (hη : QuasiIso η) :
    (((ModuleCat.restrictScalars q.toRingHom).mapDerivedCategory).obj
      ((ModuleCat.restrictScalars β.toRingHom).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat B) (0 : ℤ)).obj (ModuleCat.of B B)))) ≅
      DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars q.toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj E) := by
  letI := hη
  -- Proof comment: first restrict the already chosen `A[y]`-level comparison, then normalize
  -- the restricted `Q.obj` back to the `Q`-image of the restricted strict complex.
  exact
    (((ModuleCat.restrictScalars q.toRingHom).mapDerivedCategory).mapIso
      (resolution_restrictScalars_single0_iso (A := A) (B := B) β E η hη).symm) ≪≫
      (ModuleCat.restrictScalars q.toRingHom).mapDerivedCategoryFactors.app E

/-- Helper for Lemma 15.82.13: the pseudo-coherent ring-map hypothesis provides one surjective
polynomial presentation of `B` over `A` together with a bounded-above finite-free resolution of
the restricted degree-zero complex. -/
lemma exists_polynomialPresentation_with_finiteFree_resolution_of_isPseudoCoherentRingMap :
    ∃ (t : ℕ) (β : MvPolynomial (Fin t) A →ₐ[A] B),
      Function.Surjective β ∧
        let P := MvPolynomial (Fin t) A
        let M : ModuleCat P := (ModuleCat.restrictScalars β.toRingHom).obj (ModuleCat.of B B)
        ∃ E : CochainComplex.MinusWithTermsIn
            (fun N : ModuleCat P ↦ Module.Free P N ∧ Module.Finite P N),
          (E : CochainComplex (ModuleCat P) ℤ).IsStrictlyLE 0 ∧
            ∃ η : (E : CochainComplex (ModuleCat P) ℤ) ⟶
                (CochainComplex.singleFunctor (ModuleCat P) (0 : ℤ)).obj M,
              QuasiIso η := by
  let hBrel : (ModuleCat.of B B).IsPseudoCoherentRelativeTo A := inferInstance
  rw [ModuleCat.IsPseudoCoherentRelativeTo] at hBrel
  rcases (CochainComplex.isPseudoCoherentRelativeTo_iff_overSomePolynomialPresentation
      ((CochainComplex.singleFunctor (ModuleCat B) (0 : ℤ)).obj (ModuleCat.of B B))).1 hBrel with
    ⟨t, β, hβ, hβpc⟩
  let P := MvPolynomial (Fin t) A
  let F : ModuleCat B ⥤ ModuleCat P := ModuleCat.restrictScalars β.toRingHom
  let M : ModuleCat P := F.obj (ModuleCat.of B B)
  have hsingle : ((CochainComplex.singleFunctor (ModuleCat P) (0 : ℤ)).obj M).IsPseudoCoherent := by
    -- Proof comment: the restricted degree-zero complex is definitionally the polynomial
    -- presentation restriction of `B[0]`.
    simpa [M, F, CochainComplex.polynomialPresentationRestriction] using hβpc
  have hvanish :
      ∀ i : ℤ, (0 : ℤ) < i →
        IsZero (((CochainComplex.singleFunctor (ModuleCat P) (0 : ℤ)).obj M).homology i) := by
    intro i hi
    -- Proof comment: a single complex has no positive-degree homology.
    exact single_zero_complex_homology_isZero_of_pos M i hi
  rcases exists_boundedAbove_termwiseFiniteFree_quasiIso
      (R := P) (K := (CochainComplex.singleFunctor (ModuleCat P) (0 : ℤ)).obj M)
      hsingle hvanish with ⟨E, hEle, η, hη⟩
  exact ⟨t, β, hβ, E, hEle, η, hη⟩

/-- Helper for Lemma 15.82.13: once one polynomial presentation of `A` over `R` and one
polynomial presentation of `B` over `A` have been fixed, together with a bounded-above finite-free
resolution of `B` over that intermediate polynomial algebra, the restricted target
`K^• \otimes_A^{\mathbf L} B` becomes absolutely `m`-pseudo-coherent over a single induced
polynomial presentation of `B` over `R`. -/
/-- Helper for Lemma 15.82.13: the chosen polynomial presentations of `A` over `R` and `B` over
`A` combine into a single polynomial presentation of `B` over `R`. -/
lemma iterated_polynomial_cover_to_single_cover_surjective
    {n t : ℕ}
    (α : MvPolynomial (Fin n) R →ₐ[R] A) (hα : Function.Surjective α)
    (β : MvPolynomial (Fin t) A →ₐ[A] B) (hβ : Function.Surjective β) :
    ∃ (l : ℕ) (ρ : MvPolynomial (Fin l) R →ₐ[R] B), Function.Surjective ρ := by
  let P : Type u := MvPolynomial (Fin n) R
  let _ : Algebra P A := α.toAlgebra
  let _ : Algebra P B := ((algebraMap A B).comp α.toRingHom).toAlgebra
  let _ : IsScalarTower P A B := IsScalarTower.of_algebraMap_eq' rfl
  let Q : Type u := MvPolynomial (Fin t) P
  let qR : Q →ₐ[P] MvPolynomial (Fin t) A := MvPolynomial.mapAlgHom (Algebra.ofId P A)
  let δ : Q →ₐ[P] B := (β.restrictScalars P).comp qR
  let ePoly : MvPolynomial (Fin (t + n)) R ≃ₐ[R] Q :=
    (MvPolynomial.renameEquiv R (finSumFinEquiv.symm)).trans
      (MvPolynomial.sumAlgEquiv R (Fin t) (Fin n))
  let ρ : MvPolynomial (Fin (t + n)) R →ₐ[R] B := (δ.restrictScalars R).comp ePoly.toAlgHom
  refine ⟨t + n, ρ, ?_⟩
  -- Proof comment: first lift through the iterated presentation `Q → B`, then collapse the
  -- iterated polynomial ring back to a single polynomial algebra via `ePoly`.
  refine Function.Surjective.comp ?_ ePoly.surjective
  simpa [ρ, δ] using
    (CategoryTheory.iterated_polynomial_tensor_cover_surjective
      (R := R) (A := A) (A' := B) α hα β hβ : Function.Surjective δ)

/-- Helper for Lemma 15.82.13: once a surjective algebra map `P → A` already makes the
restricted derived `A`-complex absolutely `m`-pseudo-coherent, the original complex is relative
`m`-pseudo-coherent over `P`. -/
private theorem isMPseudoCoherentRelativeTo_of_surjective_algebraMap
    {P : Type u} [CommRing P] [Algebra P A] [Algebra.FiniteType P A]
    (hsurj : Function.Surjective (algebraMap P A))
    (K : DerivedCategory (ModuleCat A)) (m : ℤ)
    (hK :
      ((ModuleCat.restrictScalars (algebraMap P A)).mapDerivedCategory.obj K).IsMPseudoCoherent
        m) :
    K.IsMPseudoCoherentRelativeTo P m := by
  let e : MvPolynomial (Fin 0) P ≃ₐ[P] P := RingHom.emptyPolynomialPresentation P
  let α₀ : MvPolynomial (Fin 0) P →ₐ[P] A := (Algebra.ofId P A).comp e.toAlgHom
  have hReg :
      ((ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of P P)).IsPseudoCoherent := by
    -- Proof comment: the empty polynomial presentation is a ring equivalence, so its restricted
    -- regular module is still the free rank-one module.
    simpa using restrictScalars_regularModule_isPseudoCoherent_of_ringEquiv e.toRingEquiv
  have hα₀ :
      ((ModuleCat.restrictScalars α₀.toRingHom).mapDerivedCategory.obj K).IsMPseudoCoherent m := by
    -- Proof comment: the chosen empty presentation differs from the plain restriction to `P`
    -- only by the polynomial-ring equivalence `e`.
    simpa [α₀] using
      (isMPseudoCoherent_iff_restrictScalars
        (f := e.toRingHom)
        (K := ((ModuleCat.restrictScalars (algebraMap P A)).mapDerivedCategory.obj K))
        (m := m)
        hReg).2 hK
  -- Proof comment: relative `m`-pseudo-coherence can be checked on one surjective polynomial
  -- presentation, and the empty presentation composed with `P → A` is exactly such a cover.
  refine
    (derived_isMPseudoCoherentRelativeTo_iff_overSomePolynomialPresentation
      (R := P) (A := A) K m).2 ?_
  refine ⟨0, α₀, ?_, hα₀⟩
  exact Function.Surjective.comp hsurj e.surjective

/-- Helper for Lemma 15.82.13: if the structure map `P → A` is surjective, then relative
`m`-pseudo-coherence over `P` immediately yields absolute `m`-pseudo-coherence after restricting
scalars to `P`. -/
private theorem restrictScalars_isMPseudoCoherent_of_relative_of_surjective_algebraMap
    {P : Type u} [CommRing P] [Algebra P A] [Algebra.FiniteType P A]
    (hsurj : Function.Surjective (algebraMap P A))
    (K : DerivedCategory (ModuleCat A)) (m : ℤ)
    (hK : K.IsMPseudoCoherentRelativeTo P m) :
    ((ModuleCat.restrictScalars (algebraMap P A)).mapDerivedCategory.obj K).IsMPseudoCoherent
      m := by
  let e : MvPolynomial (Fin 0) P ≃ₐ[P] P := RingHom.emptyPolynomialPresentation P
  let α₀ : MvPolynomial (Fin 0) P →ₐ[P] A := (Algebra.ofId P A).comp e.toAlgHom
  have hReg :
      ((ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of P P)).IsPseudoCoherent := by
    -- Proof comment: the empty polynomial presentation is a ring equivalence, so the restricted
    -- regular module is still the free rank-one module.
    simpa using restrictScalars_regularModule_isPseudoCoherent_of_ringEquiv e.toRingEquiv
  have hα₀ :
      ((ModuleCat.restrictScalars α₀.toRingHom).mapDerivedCategory.obj K).IsMPseudoCoherent m := by
    -- Proof comment: evaluate the relative hypothesis on the empty polynomial presentation
    -- composed with the surjective structure map `P → A`.
    exact hK 0 α₀ (Function.Surjective.comp hsurj e.surjective)
  -- Proof comment: restriction along `α₀` is just restriction to `P` followed by the polynomial
  -- equivalence `e`, so the absolute statement transports back along Lemma `15.65.11`.
  simpa [α₀] using
    (isMPseudoCoherent_iff_restrictScalars
      (f := e.toRingHom)
      (K := ((ModuleCat.restrictScalars (algebraMap P A)).mapDerivedCategory.obj K))
      (m := m)
      hReg).2 hα₀

/-- Helper for Lemma 15.82.13: if `P → A` is surjective, then the induced coefficientwise map on
iterated polynomial algebras is also surjective. -/
private theorem iterated_polynomial_map_surjective_of_surjective_algebraMap
    {P : Type u} [CommRing P] {A : Type u} [CommRing A] [Algebra P A]
    {t : ℕ}
    (hsurj : Function.Surjective (algebraMap P A)) :
    Function.Surjective
      (MvPolynomial.mapAlgHom (Algebra.ofId P A) :
        MvPolynomial (Fin t) P →ₐ[P] MvPolynomial (Fin t) A) := by
  -- Proof comment: `MvPolynomial.map_surjective` promotes coefficientwise surjectivity of the
  -- base ring map to surjectivity on the whole polynomial algebra.
  simpa using MvPolynomial.map_surjective (Algebra.ofId P A).toRingHom hsurj

/-- Helper for Lemma 15.82.13: before rewriting the intermediate polynomial ring `A[y]` as an
iterated polynomial algebra over the presentation ring, the left tensor factor is the standard
derived base-change object over `Q ⊗[P] A`. -/
private noncomputable def iterated_polynomial_base_change_left_factor_iso
    {n t : ℕ}
    (α : MvPolynomial (Fin n) R →ₐ[R] A)
    (K : DModA) :
    let P : Type u := MvPolynomial (Fin n) R
    let _ : Algebra P A := α.toAlgebra
    let Q : Type u := MvPolynomial (Fin t) P
    let T : Type u := Q ⊗[P] A
    (((ModuleCat.restrictScalars (algebraMap Q T)).mapDerivedCategory).obj
      (K ⊗[A]^L[T])) ≅
      ((((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory).obj K) ⊗[P]^L[Q]) := by
  let P : Type u := MvPolynomial (Fin n) R
  let _ : Algebra P A := α.toAlgebra
  let Q : Type u := MvPolynomial (Fin t) P
  let T : Type u := Q ⊗[P] A
  -- Proof comment: this is exactly the Chapter 15 base-change comparison for the tower
  -- `P → A` and `P → Q`, specialized to the chosen polynomial presentation of `A`.
  exact
    derivedTensorBaseChangeIso
      (A := P) (R := A) (Aprime := Q) K

/-- Helper for Lemma 15.82.13: the raw tensor-base-change left factor over `Q ⊗[P] A` is already
absolutely `m`-pseudo-coherent over `Q`. -/
private theorem iterated_polynomial_base_change_left_factor_isMPseudoCoherent
    {n t : ℕ}
    (α : MvPolynomial (Fin n) R →ₐ[R] A)
    (K : DModA) (m : ℤ)
    (hKα :
      ((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj K).IsMPseudoCoherent m) :
    let P : Type u := MvPolynomial (Fin n) R
    let _ : Algebra P A := α.toAlgebra
    let Q : Type u := MvPolynomial (Fin t) P
    let T : Type u := Q ⊗[P] A
    (((ModuleCat.restrictScalars (algebraMap Q T)).mapDerivedCategory).obj
      (K ⊗[A]^L[T])).IsMPseudoCoherent m := by
  let P : Type u := MvPolynomial (Fin n) R
  let _ : Algebra P A := α.toAlgebra
  let Q : Type u := MvPolynomial (Fin t) P
  let T : Type u := Q ⊗[P] A
  have hQ :
      ((((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory).obj K) ⊗[P]^L[Q]).IsMPseudoCoherent
        m := by
    -- Proof comment: polynomial extension preserves absolute `m`-pseudo-coherence over the
    -- presentation ring.
    exact
      derivedTensorWithAlgebra_isMPseudoCoherent
        (((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory).obj K) m hKα
  -- Proof comment: transport the absolute statement back through the derived base-change
  -- comparison before identifying `Q ⊗[P] A` with `A[y]`.
  exact
    isMPseudoCoherent_of_iso
      (iterated_polynomial_base_change_left_factor_iso (R := R) (A := A) α (t := t) K).symm
      m hQ

/-- Helper for Lemma 15.82.13: once one polynomial presentation of `A` over `R` and one
polynomial presentation of `B` over `A` have been fixed, together with a bounded-above finite-free
resolution of `B` over that intermediate polynomial algebra, the restricted target
`K^• \otimes_A^{\mathbf L} B` becomes absolutely `m`-pseudo-coherent over a single induced
polynomial presentation of `B` over `R`. -/
lemma exists_iterated_presentation_of_tensor_isMPseudoCoherent
    {n t : ℕ}
    (α : MvPolynomial (Fin n) R →ₐ[R] A) (hα : Function.Surjective α)
    (K : DModA) (m : ℤ)
    (hKα : ((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj K).IsMPseudoCoherent m)
    (β : MvPolynomial (Fin t) A →ₐ[A] B) (hβ : Function.Surjective β)
    (E : CochainComplex.MinusWithTermsIn
      (fun N : ModuleCat (MvPolynomial (Fin t) A) ↦
        Module.Free (MvPolynomial (Fin t) A) N ∧
          Module.Finite (MvPolynomial (Fin t) A) N))
    (hEle : (E : CochainComplex (ModuleCat (MvPolynomial (Fin t) A)) ℤ).IsStrictlyLE 0)
    (η : (E : CochainComplex (ModuleCat (MvPolynomial (Fin t) A)) ℤ) ⟶
      (CochainComplex.singleFunctor (ModuleCat (MvPolynomial (Fin t) A)) (0 : ℤ)).obj
        ((ModuleCat.restrictScalars β.toRingHom).obj (ModuleCat.of B B)))
    (hη : QuasiIso η) :
    ∃ (l : ℕ) (ρ : MvPolynomial (Fin l) R →ₐ[R] B),
      Function.Surjective ρ ∧
        ((ModuleCat.restrictScalars ρ.toRingHom).mapDerivedCategory.obj
          (K ⊗[A]^L[B])).IsMPseudoCoherent m := by
  -- Route correction: the previous attempt restricted all the way to the iterated presentation
  -- ring before using the finite-free resolution, which destroys the source proof's finite-free
  -- filtration. We now fix the combined polynomial presentation first and leave only the final
  -- comparison from the restricted target to the `A[y]`-resolution tensor object.
  let S : Type u := MvPolynomial (Fin t) A
  rcases
      iterated_polynomial_cover_to_single_cover_surjective
        (R := R) (A := A) (B := B) α hα β hβ with
    ⟨l, ρ, hρ⟩
  refine ⟨l, ρ, hρ, ?_⟩
  let P : Type u := MvPolynomial (Fin n) R
  let _ : Algebra P A := α.toAlgebra
  let _ : Algebra P B := ((algebraMap A B).comp α.toRingHom).toAlgebra
  let _ : IsScalarTower P A B := IsScalarTower.of_algebraMap_eq' rfl
  let Q : Type u := MvPolynomial (Fin t) P
  let qR : Q →ₐ[P] S := MvPolynomial.mapAlgHom (Algebra.ofId P A)
  let δ : Q →ₐ[P] B := (β.restrictScalars P).comp qR
  let ePoly : MvPolynomial (Fin (t + n)) R ≃ₐ[R] Q :=
    (MvPolynomial.renameEquiv R (finSumFinEquiv.symm)).trans
      (MvPolynomial.sumAlgEquiv R (Fin t) (Fin n))
  have hαP : Function.Surjective (algebraMap P A) := by
    -- Proof comment: after installing `α` as the ambient `P`-algebra structure on `A`, the
    -- structure map is exactly the chosen polynomial presentation.
    simpa using hα
  have hqR : Function.Surjective qR := by
    -- Proof comment: surjectivity of the chosen presentation `P → A` extends coefficientwise to
    -- the iterated polynomial presentation `Q → S`.
    exact
      iterated_polynomial_map_surjective_of_surjective_algebraMap
        (P := P) (A := A) (t := t) hαP
  have hEqReg :
      ((ModuleCat.restrictScalars ePoly.toRingHom).obj (ModuleCat.of Q Q)).IsPseudoCoherent := by
    -- Proof comment: the single polynomial cover `ρ` differs from the iterated cover `δ` only by
    -- the explicit polynomial-ring equivalence `ePoly`.
    exact restrictScalars_regularModule_isPseudoCoherent_of_ringEquiv ePoly
  have hKP : K.IsMPseudoCoherentRelativeTo P m := by
    -- Proof comment: the chosen surjection `P → A` already gives the required absolute witness
    -- over the base ring `P`.
    exact
      isMPseudoCoherentRelativeTo_of_surjective_algebraMap
        (P := P) hαP K m hKα
  have hTensorBaseChange :
      let T : Type u := Q ⊗[P] A
      (((ModuleCat.restrictScalars (algebraMap Q T)).mapDerivedCategory).obj
        (K ⊗[A]^L[T])).IsMPseudoCoherent m := by
    -- Proof comment: the first open step of the source proof is now reduced to the canonical
    -- tensor-base-change comparison over `Q ⊗[P] A`.
    exact
      iterated_polynomial_base_change_left_factor_isMPseudoCoherent
        (R := R) (A := A) (n := n) (t := t) α K m hKα
  let eResolution :
      DerivedCategory.Q.obj (E : CochainComplex (ModuleCat S) ℤ) ≅
        ((ModuleCat.restrictScalars β.toRingHom).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor (ModuleCat B) (0 : ℤ)).obj (ModuleCat.of B B))) :=
    resolution_restrictScalars_single0_iso (A := A) (B := B) β
      (E := (E : CochainComplex (ModuleCat S) ℤ)) η hη
  let eRestrictedResolution :
      (((ModuleCat.restrictScalars qR.toRingHom).mapDerivedCategory).obj
        ((ModuleCat.restrictScalars β.toRingHom).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor (ModuleCat B) (0 : ℤ)).obj (ModuleCat.of B B)))) ≅
        DerivedCategory.Q.obj
          (((ModuleCat.restrictScalars qR.toRingHom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (E : CochainComplex (ModuleCat S) ℤ)) :=
    restricted_resolution_restrictScalars_single0_iso
      (A := A) (B := B) (P := P) qR β
      (E := (E : CochainComplex (ModuleCat S) ℤ)) η hη
  -- Proof comment: at this point the remaining work is exactly the source-faithful transport:
  -- identify the raw tensor-base-change object over `Q ⊗[P] A` with the concrete polynomial
  -- algebra `S = A[y]`, transport the resulting absolute `Q`-level left-factor statement to
  -- `((ModuleCat.restrictScalars qR.toRingHom).mapDerivedCategory.obj (K ⊗[A]^L[S]))`, and then
  -- compare the `δ`-restricted target with the corresponding tensor-resolution object. The first
  -- of those two transports is now isolated by `hTensorBaseChange`; the remaining blocker is the
  -- passage from `Q ⊗[P] A` to `S` plus the final resolution closure.
  let _ := hEle
  let _ := qR
  let _ := δ
  let _ := ePoly
  let _ := hEqReg
  let _ := hKP
  let _ := hTensorBaseChange
  let _ := hqR
  let _ := eResolution
  let _ := eRestrictedResolution
  let _ := η
  let _ := hη
  let _ := E
  -- TODO(Lemma 15.82.13): first transport `hTensorBaseChange` across the canonical tensor /
  -- polynomial-ring equivalence `Q ⊗[P] A ≃ S` to obtain the absolute `Q`-level statement for
  -- `((ModuleCat.restrictScalars qR.toRingHom).mapDerivedCategory.obj (K ⊗[A]^L[S]))`; then
  -- identify the `δ`-restricted target with the resulting left factor tensored with the
  -- restricted resolution `Q.obj (((ModuleCat.restrictScalars qR.toRingHom).mapHomologicalComplex
  -- _).obj E)` and close that bounded-above tensor-resolution object by the finite-free stage
  -- filtration from the source proof.
  have hδK :
      ((ModuleCat.restrictScalars δ.toRingHom).mapDerivedCategory.obj
        (K ⊗[A]^L[B])).IsMPseudoCoherent m := sorry
  -- Proof comment: once the iterated polynomial presentation `δ` is handled, the final passage
  -- to the single presentation `ρ` is exactly restriction of scalars along the polynomial-ring
  -- equivalence `ePoly`.
  simpa [ρ, δ] using
    (isMPseudoCoherent_iff_restrictScalars
      (f := ePoly.toRingHom)
      (K := ((ModuleCat.restrictScalars δ.toRingHom).mapDerivedCategory.obj
        (K ⊗[A]^L[B])))
      (m := m)
      hEqReg).1 hδK

/-- Lemma 15.82.13 (1): if `R → A` is finite type, `A → B` is a pseudo-coherent ring map, and a
derived `A`-complex `K^•` is `m`-pseudo-coherent relative to `R`, then
`K^• \otimes_A^{\mathbf L} B` is `m`-pseudo-coherent relative to `R`. -/
@[stacks 067B]
theorem derivedTensorWithAlgebra_isMPseudoCoherentRelativeTo_of_isPseudoCoherentRingMap
    (K : DModA) (m : ℤ) (hK : K.IsMPseudoCoherentRelativeTo R m) :
    by
      letI : Algebra.FiniteType R B :=
        Algebra.FiniteType.trans
          (inferInstance : Algebra.FiniteType R A)
          (inferInstance : Algebra.FiniteType A B)
      exact (K ⊗[A]^L[B]).IsMPseudoCoherentRelativeTo R m := by
        -- Proof comment: first choose one polynomial presentation of `A` over `R` on which `K`
        -- is already absolutely `m`-pseudo-coherent.
        rcases
            (derived_isMPseudoCoherentRelativeTo_iff_overSomePolynomialPresentation
              (R := R) (A := A) K m).1 hK with
          ⟨n, α, hα, hKα⟩
        -- Proof comment: next choose one polynomial presentation of `B` over `A` together with
        -- the bounded-above finite-free resolution supplied by the pseudo-coherent ring-map
        -- hypothesis.
        rcases
            exists_polynomialPresentation_with_finiteFree_resolution_of_isPseudoCoherentRingMap
            (A := A) (B := B) with
          ⟨t, β, hβ, E, hEle, η, hη⟩
        -- Proof comment: the remaining source-faithful work is exactly to combine these two
        -- presentations into one presentation of `B` over `R` and to prove absolute
        -- `m`-pseudo-coherence there.
        rcases
            exists_iterated_presentation_of_tensor_isMPseudoCoherent
              (R := R) (A := A) (B := B) α hα K m hKα β hβ E hEle η hη with
          ⟨l, ρ, hρ, hρK⟩
        exact
          (derived_isMPseudoCoherentRelativeTo_iff_overSomePolynomialPresentation
            (R := R) (A := B) (K := K ⊗[A]^L[B]) m).2
            ⟨l, ρ, hρ, hρK⟩

-- Proof sketch: unfold relative pseudo-coherence as relative `m`-pseudo-coherence for every
-- integer `m`, and apply part `(1)` to each bound.
/-- Lemma 15.82.13 (2): if `R → A` is finite type, `A → B` is a pseudo-coherent ring map, and a
derived `A`-complex `K^•` is pseudo-coherent relative to `R`, then
`K^• \otimes_A^{\mathbf L} B` is pseudo-coherent relative to `R`. -/
@[stacks 067B]
theorem derivedTensorWithAlgebra_isPseudoCoherentRelativeTo_of_isPseudoCoherentRingMap
    (K : DModA) (hK : K.IsPseudoCoherentRelativeTo R) :
    by
      letI : Algebra.FiniteType R B :=
        Algebra.FiniteType.trans
          (inferInstance : Algebra.FiniteType R A)
          (inferInstance : Algebra.FiniteType A B)
      exact (K ⊗[A]^L[B]).IsPseudoCoherentRelativeTo R := by
        intro m
        exact
          derivedTensorWithAlgebra_isMPseudoCoherentRelativeTo_of_isPseudoCoherentRingMap
            K m (hK m)

end

end CategoryTheory
