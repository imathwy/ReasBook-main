import Mathlib
import StacksProject_2024.stacks_project.Chap15.Lemma_15_65_11
import StacksProject_2024.stacks_project.Chap15.Lemma_15_75_3
import StacksProject_2024.stacks_project.Chap15.Lemma_15_82_10

noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R A B : Type u}
variable [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
variable [Algebra.FiniteType R A] [Module.Finite A B]

local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "DModB" => DerivedCategory (ModuleCat B)
local notation "restrictScalarsDerived" =>
  CategoryTheory.Functor.mapDerivedCategory (ModuleCat.restrictScalars (algebraMap A B))

private theorem finiteType_over_base
    (R A B : Type u)
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.FiniteType R A] [Module.Finite A B] :
    Algebra.FiniteType R B := by
  exact
    Algebra.FiniteType.trans
      (inferInstance : Algebra.FiniteType R A)
      (inferInstance : Algebra.FiniteType A B)

/-- Helper for Lemma 15.82.5: adjoining a root of a monic polynomial yields a pseudo-coherent
regular module over the coefficient ring. -/
private theorem monic_adjoinRoot_regularModule_isPseudoCoherent
    {S : Type u} [CommRing S] (f : Polynomial S) (hf : f.Monic) :
    ((ModuleCat.restrictScalars (algebraMap S (AdjoinRoot f))).obj
      (ModuleCat.of (AdjoinRoot f) (AdjoinRoot f))).IsPseudoCoherent := by
  letI : Module.Finite S (AdjoinRoot f) := hf.finite_adjoinRoot
  letI : Module.Free S (AdjoinRoot f) := hf.free_adjoinRoot
  have hPerfect : (ModuleCat.of S (AdjoinRoot f)).IsPerfect := by
    -- The monic `AdjoinRoot` is finite free over the coefficient ring, so it is already a
    -- length-zero finite projective resolution witness.
    rw [ModuleCat.isPerfect_iff_exists_finiteProjectiveResolutionLengthLEWithFiniteTerms]
    refine ⟨0, ?_⟩
    rw [ModuleCat.hasFiniteProjectiveResolutionLengthLEWithFiniteTerms_zero_iff]
    constructor
    · exact Module.Projective.of_free
    · infer_instance
  -- Perfect modules are pseudo-coherent, and the restricted regular module is definitionally this
  -- coefficient-ring module.
  simpa using
    (ModuleCat.isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension
      (ModuleCat.of S (AdjoinRoot f))).1 hPerfect |>.1

/-- Helper for Lemma 15.82.5: multiplication by a monic polynomial on the source polynomial ring
is injective. -/
private theorem monic_polynomial_mul_injective
    {S : Type u} [CommRing S] (f : Polynomial S) (hf : f.Monic) :
    Function.Injective (fun p : Polynomial S ↦ p * f) := by
  intro p q hpq
  have hsub : (p - q) * f = 0 := by
    -- Proof comment: subtract the equal products to reduce injectivity to the zero-kernel case.
    simpa [sub_mul, hpq]
  by_contra hpq_ne
  have hsub_ne : p - q ≠ 0 := sub_ne_zero.mpr hpq_ne
  have hdeg : ((p - q) * f).natDegree = (p - q).natDegree + f.natDegree :=
    hf.natDegree_mul hsub_ne
  rw [hsub] at hdeg
  have hsum_zero : (p - q).natDegree + f.natDegree = 0 := by
    simpa using hdeg
  have hsub_deg_zero : (p - q).natDegree = 0 := (Nat.add_eq_zero.mp hsum_zero).1
  have hf_deg_zero : f.natDegree = 0 := (Nat.add_eq_zero.mp hsum_zero).2
  have hf_one : f = 1 := hf.natDegree_eq_zero.mp hf_deg_zero
  have hzero : p - q = 0 := by
    simpa [hf_one] using hsub
  exact hpq_ne (sub_eq_zero.mp hzero)

/-- Helper for Lemma 15.82.5: the quotient by one monic polynomial is a perfect module over the
source polynomial ring. -/
private theorem monic_polynomial_quotient_regularModule_isPerfect_over_source
    {S : Type u} [CommRing S] (f : Polynomial S) (hf : f.Monic) :
    (ModuleCat.of (Polynomial S)
      ((Polynomial S) ⧸ Ideal.span ({f} : Set (Polynomial S)))).IsPerfect := by
  let P₀ : FiniteProjectiveModuleCat (Polynomial S) :=
    ⟨ModuleCat.of (Polynomial S) (Polynomial S), inferInstance⟩
  let I : Ideal (Polynomial S) := Ideal.span ({f} : Set (Polynomial S))
  let δ₀ : P₀.obj ⟶ P₀.obj :=
    { toFun := fun p ↦ p * f
      map_add' := fun p q ↦ by
        simp [add_mul]
      map_smul' := fun a p ↦ by
        -- Proof comment: scalar multiplication on the regular module is ring multiplication, so
        -- linearity reduces to associativity.
        change (a * p) * f = a * (p * f)
        rw [mul_assoc] }
  let π : P₀.obj ⟶
      ModuleCat.of (Polynomial S) ((Polynomial S) ⧸ I) :=
    (Ideal.Quotient.mk I).toLinearMap
  -- Proof comment: the quotient by `(f)` has the explicit length-one free resolution
  -- `S[X] --(·f)→ S[X] → S[X]/(f) → 0`.
  rw [ModuleCat.isPerfect_iff_exists_finiteProjectiveResolutionLengthLEWithFiniteTerms]
  refine ⟨1, ?_⟩
  refine ⟨fun _ ↦ P₀, fun _ ↦ δ₀, π, ?_, ?_, ?_, ?_⟩
  · -- Proof comment: the quotient map is surjective by definition of the ideal quotient.
    simpa [π] using
      (Ideal.Quotient.mk_surjective :
        Function.Surjective (Ideal.Quotient.mk I))
  · -- Proof comment: the kernel of the quotient map is exactly the principal ideal `(f)`, hence
    -- it is the image of multiplication by `f`.
    intro p
    constructor
    · intro hp
      rw [Ideal.Quotient.eq_zero_iff_mem] at hp
      rcases Ideal.mem_span_singleton.mp hp with ⟨q, hq⟩
      exact ⟨q, by simpa [δ₀] using hq⟩
    · rintro ⟨q, rfl⟩
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact Ideal.mul_mem_left I q (Ideal.subset_span (by simp))
  · -- Proof comment: there are no higher exactness conditions in a length-one resolution.
    intro i
    exact Fin.elim0 i
  · -- Proof comment: injectivity of the first differential is exactly injectivity of
    -- multiplication by the monic polynomial `f`.
    simpa [δ₀] using monic_polynomial_mul_injective f hf

/-- Helper for Lemma 15.82.5: the quotient by one monic polynomial is a pseudo-coherent regular
module over the source polynomial ring. -/
private theorem single_monic_polynomial_quotient_regularModule_isPseudoCoherent_over_source
    {S : Type u} [CommRing S] (f : Polynomial S) (hf : f.Monic) :
    (ModuleCat.of (Polynomial S)
      ((Polynomial S) ⧸ Ideal.span ({f} : Set (Polynomial S)))).IsPseudoCoherent := by
  -- Proof comment: the explicit length-one finite free resolution upgrades perfectness to
  -- pseudo-coherence immediately.
  exact
    (ModuleCat.isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension _).1
      (monic_polynomial_quotient_regularModule_isPerfect_over_source f hf) |>.1

/-- Helper for Lemma 15.82.5: a monic polynomial over `A` lifts through a surjective polynomial
presentation to a monic polynomial over the presentation ring. -/
private theorem lift_monic_polynomial_through_surjective_presentation
    {n : ℕ} (α : MvPolynomial (Fin n) R →ₐ[R] A) (hα : Function.Surjective α)
    (g : Polynomial A) (hg : g.Monic) :
    ∃ G : Polynomial (MvPolynomial (Fin n) R),
      G.Monic ∧ Polynomial.map α.toRingHom G = g := by
  have hg_lifts : g ∈ Polynomial.lifts α.toRingHom := by
    -- Proof comment: surjectivity of `α` gives a coefficientwise lift of `g`.
    rw [Polynomial.mem_lifts]
    exact Polynomial.map_surjective α.toRingHom hα g
  obtain ⟨G, hG, -, hG_monic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hg_lifts hg
  -- Proof comment: the canonical lift theorem preserves the monic leading coefficient.
  exact ⟨G, hG_monic, hG⟩

/-- Helper for Lemma 15.82.5: over any surjective polynomial presentation of `A`, a finite
`A`-algebra `B` admits finitely many generators satisfying monic polynomial relations whose
coefficients lift to the presentation ring. -/
private theorem exists_generators_with_lifted_monic_relations_of_finite
    {n : ℕ} (α : MvPolynomial (Fin n) R →ₐ[R] A) (hα : Function.Surjective α) :
    ∃ (l : ℕ) (y : Fin l → B) (G : Fin l → Polynomial (MvPolynomial (Fin n) R)),
      Submodule.span A (Set.range y) = ⊤ ∧
        (∀ i, (G i).Monic) ∧
        ∀ i, Polynomial.aeval (y i) (Polynomial.map α.toRingHom (G i)) = 0 := by
  rcases (Module.Finite.iff_exists_surjective_free A B).1
      (inferInstance : Module.Finite A B) with ⟨l, f, hf⟩
  let y : Fin l → B := fun i ↦ f (Pi.single i (1 : A))
  have hy_span : Submodule.span A (Set.range y) = ⊤ := by
    -- Proof comment: the images of the standard basis vectors of `A^l` generate `B` because the
    -- chosen linear map `f` is surjective.
    exact (top_le_iff.mp <| by
      intro b hb
      rcases hf b with ⟨x, rfl⟩
      have hx : x = ∑ i, x i • (Pi.single i (1 : A) : Fin l → A) := by
        ext i
        simp [Pi.single_apply]
      rw [hx, LinearMap.map_sum]
      refine Submodule.sum_mem _ ?_
      intro i hi
      have hterm :
          f (x i • (Pi.single i (1 : A) : Fin l → A)) = x i • y i := by
        simpa [y] using (f.map_smul (x i) (Pi.single i (1 : A)))
      rw [hterm]
      exact
        Submodule.smul_mem (Submodule.span A (Set.range y)) (x i)
          (Submodule.subset_span ⟨i, rfl⟩))
  have hIntegral :
      ∀ i : Fin l, ∃ g : Polynomial A, g.Monic ∧ Polynomial.aeval (y i) g = 0 := by
    intro i
    -- Proof comment: every chosen generator is integral because finite algebras are integral.
    exact IsIntegral.of_finite A (y i)
  choose g hgmonic hgy using hIntegral
  have hLift :
      ∀ i : Fin l, ∃ G : Polynomial (MvPolynomial (Fin n) R),
        G.Monic ∧ Polynomial.map α.toRingHom G = g i := by
    intro i
    -- Proof comment: surjectivity of the presentation map lifts each monic annihilating
    -- polynomial coefficientwise.
    exact lift_monic_polynomial_through_surjective_presentation α hα (g i) (hgmonic i)
  choose G hGmonic hGmap using hLift
  refine ⟨l, y, G, hy_span, hGmonic, ?_⟩
  intro i
  -- Proof comment: after substituting the lifted polynomial identity, the original monic
  -- annihilating relation for `y i` gives the desired vanishing.
  simpa [hGmap i] using hgy i

/-- Helper for Lemma 15.82.5: restricting a chosen derived representative along a polynomial
presentation agrees with first restricting a chosen cochain preimage and then applying `Q`. -/
private noncomputable def derived_polynomialPresentationRestriction_preimageIso
    {S : Type u} [CommRing S] [Algebra R S]
    (K : DerivedCategory (ModuleCat S)) {n : ℕ}
    (α : MvPolynomial (Fin n) R →ₐ[R] S) :
    ((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj K) ≅
      DerivedCategory.Q.obj
        (CochainComplex.polynomialPresentationRestriction (DerivedCategory.Q.objPreimage K) α) :=
  (((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory).mapIso
      (DerivedCategory.Q.objObjPreimageIso K)).symm ≪≫
    ((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategoryFactors.app
      (DerivedCategory.Q.objPreimage K))

/-- Helper for Lemma 15.82.5: relative derived `m`-pseudo-coherence can be checked on some
surjective polynomial presentation. -/
private theorem derived_isMPseudoCoherentRelativeTo_iff_overSomePolynomialPresentation
    {S : Type u} [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (K : DerivedCategory (ModuleCat S)) (m : ℤ) :
    K.IsMPseudoCoherentRelativeTo R m ↔
      ∃ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] S),
        Function.Surjective α ∧
          ((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj K).IsMPseudoCoherent m := by
  let E := DerivedCategory.Q.objPreimage K
  have hrelative :
      K.IsMPseudoCoherentRelativeTo R m ↔ E.IsMPseudoCoherentRelativeTo R m := by
    constructor
    · intro hK
      intro n α hα
      -- Pass to the chosen cochain representative of `K` over the same presentation ring.
      let e := derived_polynomialPresentationRestriction_preimageIso (R := R) K α
      simpa [E] using isMPseudoCoherent_of_iso e m (hK n α hα)
    · intro hE
      intro n α hα
      -- Return from the cochain representative to the original derived object.
      let e := derived_polynomialPresentationRestriction_preimageIso (R := R) K α
      simpa [E] using isMPseudoCoherent_of_iso e.symm m (hE n α hα)
  calc
    K.IsMPseudoCoherentRelativeTo R m ↔ E.IsMPseudoCoherentRelativeTo R m := hrelative
    _ ↔
        ∃ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] S),
          Function.Surjective α ∧
            (CochainComplex.polynomialPresentationRestriction E α).IsMPseudoCoherent m :=
      CochainComplex.isMPseudoCoherentRelativeTo_iff_overSomePolynomialPresentation E m
    _ ↔
        ∃ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] S),
          Function.Surjective α ∧
            ((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj K).IsMPseudoCoherent m := by
      constructor
      · rintro ⟨n, α, hα, hEα⟩
        -- Move the absolute `m`-pseudo-coherence witness back to the original derived restriction.
        let e := derived_polynomialPresentationRestriction_preimageIso (R := R) K α
        exact ⟨n, α, hα, by simpa [E] using isMPseudoCoherent_of_iso e.symm m hEα⟩
      · rintro ⟨n, α, hα, hKα⟩
        -- Transport the absolute statement to the restricted cochain representative.
        let e := derived_polynomialPresentationRestriction_preimageIso (R := R) K α
        exact ⟨n, α, hα, by simpa [E] using isMPseudoCoherent_of_iso e m hKα⟩

/-- Helper for Lemma 15.82.5: relative derived pseudo-coherence can be checked on some surjective
polynomial presentation. -/
private theorem derived_isPseudoCoherentRelativeTo_iff_overSomePolynomialPresentation
    {S : Type u} [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (K : DerivedCategory (ModuleCat S)) :
    K.IsPseudoCoherentRelativeTo R ↔
      ∃ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] S),
        Function.Surjective α ∧
          ((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj K).IsPseudoCoherent := by
  let E := DerivedCategory.Q.objPreimage K
  have hrelative :
      K.IsPseudoCoherentRelativeTo R ↔ E.IsPseudoCoherentRelativeTo R := by
    constructor
    · intro hK
      intro m n α hα
      -- Pass to the chosen cochain representative presentationwise in every degree bound.
      let e := derived_polynomialPresentationRestriction_preimageIso (R := R) K α
      simpa [E] using isMPseudoCoherent_of_iso e m (hK m n α hα)
    · intro hE
      intro m n α hα
      -- Transport back from the cochain representative to the original derived object.
      let e := derived_polynomialPresentationRestriction_preimageIso (R := R) K α
      simpa [E] using isMPseudoCoherent_of_iso e.symm m (hE m n α hα)
  have habs :
      (∃ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] S),
        Function.Surjective α ∧
          (CochainComplex.polynomialPresentationRestriction E α).IsPseudoCoherent) ↔
      (∃ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] S),
        Function.Surjective α ∧
          ((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj K).IsPseudoCoherent) := by
    constructor
    · rintro ⟨n, α, hα, hEα⟩
      let e := derived_polynomialPresentationRestriction_preimageIso (R := R) K α
      rw [isPseudoCoherent_iff_forall_isMPseudoCoherent] at hEα ⊢
      refine ⟨n, α, hα, ?_⟩
      intro m
      simpa [E] using isMPseudoCoherent_of_iso e.symm m (hEα m)
    · rintro ⟨n, α, hα, hKα⟩
      let e := derived_polynomialPresentationRestriction_preimageIso (R := R) K α
      rw [isPseudoCoherent_iff_forall_isMPseudoCoherent] at hKα ⊢
      refine ⟨n, α, hα, ?_⟩
      intro m
      simpa [E] using isMPseudoCoherent_of_iso e m (hKα m)
  calc
    K.IsPseudoCoherentRelativeTo R ↔ E.IsPseudoCoherentRelativeTo R := hrelative
    _ ↔
        ∃ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] S),
          Function.Surjective α ∧
            (CochainComplex.polynomialPresentationRestriction E α).IsPseudoCoherent :=
      CochainComplex.isPseudoCoherentRelativeTo_iff_overSomePolynomialPresentation E
    _ ↔
        ∃ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] S),
          Function.Surjective α ∧
            ((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj K).IsPseudoCoherent :=
      habs

/-- Helper for Lemma 15.82.5: restricting the regular module along a ring equivalence preserves
pseudo-coherence. -/
private theorem restrictScalars_regularModule_isPseudoCoherent_of_ringEquiv
    {S T : Type u} [CommRing S] [CommRing T] (e : S ≃+* T) :
    ((ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of T T)).IsPseudoCoherent := by
  let eₗ :
      ModuleCat.of S S ≃ₗ[S]
        ((ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of T T)) :=
    { __ := e.toAddEquiv
      map_smul' := fun r s ↦ e.map_mul r s }
  let M : ModuleCat S := (ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of T T)
  letI : Module.Free S M := Module.Free.of_equiv eₗ
  letI : Module.Finite S M := Module.Finite.equiv eₗ
  -- Proof comment: the restricted regular module is finite free of rank one, so its degree-zero
  -- complex already gives a bounded-above finite-free witness.
  rw [ModuleCat.IsPseudoCoherent]
  refine
    ⟨(CochainComplex.singleFunctor (ModuleCat S) (0 : ℤ)).obj M, ⟨0, inferInstance⟩, ?_, ?_, ?_⟩
  · exact
      CategoryTheory.single_zero_complex_isTermwiseFiniteFree
        (R := S) M
  · exact ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat S) (0 : ℤ)).app M).symm.hom
  · infer_instance

/-- Helper for Lemma 15.82.5: module pseudo-coherence is preserved by module isomorphisms. -/
private theorem moduleCat_isPseudoCoherent_of_iso
    {S : Type u} [CommRing S] {M N : ModuleCat S} (e : M ≅ N)
    (hM : M.IsPseudoCoherent) :
    N.IsPseudoCoherent := by
  -- Proof comment: transport the chosen bounded-above finite-free witness for `M` across the
  -- degree-zero derived isomorphism induced by `e`.
  rw [ModuleCat.IsPseudoCoherent] at hM ⊢
  rcases hM with ⟨E, hEbounded, hEfree, α, hα⟩
  refine ⟨E, hEbounded, hEfree, α ≫ ((ModuleCat.single0Functor : ModuleCat S ⥤
    DerivedCategory (ModuleCat S)).mapIso e).hom, ?_⟩
  simpa using
    (show IsIso
      (α ≫
        ((ModuleCat.single0Functor : ModuleCat S ⥤ DerivedCategory (ModuleCat S)).mapIso e).hom) by
      infer_instance)

/-- Helper for Lemma 15.82.5: if `T` is pseudo-coherent over `S`, then restricting any
pseudo-coherent `T`-module to `S` preserves pseudo-coherence. -/
private theorem moduleCat_restrictScalars_isPseudoCoherent
    {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)
    (hT : ((ModuleCat.restrictScalars f).obj (ModuleCat.of T T)).IsPseudoCoherent)
    {M : ModuleCat T} (hM : M.IsPseudoCoherent) :
    ((ModuleCat.restrictScalars f).obj M).IsPseudoCoherent := by
  let K : DerivedCategory (ModuleCat T) :=
    (ModuleCat.single0Functor : ModuleCat T ⥤ DerivedCategory (ModuleCat T)).obj M
  have hK : K.IsPseudoCoherent := by
    simpa [K, ModuleCat.IsPseudoCoherent] using hM
  have hRestricted :
      (((ModuleCat.restrictScalars f).mapDerivedCategory).obj K).IsPseudoCoherent := by
    exact (isPseudoCoherent_iff_restrictScalars (f := f) (K := K) hT).1 hK
  let e :
      (ModuleCat.single0Functor : ModuleCat S ⥤ DerivedCategory (ModuleCat S)).obj
          ((ModuleCat.restrictScalars f).obj M) ≅
        ((ModuleCat.restrictScalars f).mapDerivedCategory).obj K :=
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat S) (0 : ℤ)).app
      ((ModuleCat.restrictScalars f).obj M)) ≪≫
      DerivedCategory.Q.mapIso
        (((Functor.mapCochainComplexSingleFunctor
          (ModuleCat.restrictScalars f) (0 : ℤ)).app M).symm)
  -- Proof comment: the restricted derived single complex is canonically the single complex of the
  -- restricted module, so the derived restriction statement descends to modules.
  simpa [ModuleCat.IsPseudoCoherent] using isPseudoCoherent_of_iso e.symm hRestricted

/-- Helper for Lemma 15.82.5: if finitely many `A`-linear generators span `B`, then evaluating
polynomials in those generators gives a surjective polynomial cover. -/
private theorem mvPolynomial_aevalAlgHom_surjective_of_span_top
    {l : ℕ} (y : Fin l → B) (hy : Submodule.span A (Set.range y) = ⊤) :
    Function.Surjective
      (MvPolynomial.aevalAlgHom y :
        MvPolynomial (Fin l) A →ₐ[A] B) := by
  intro b
  have hb_mem : b ∈ Submodule.span A (Set.range y) := by
    simpa [hy]
  obtain ⟨c, hc⟩ :=
    (Submodule.mem_span_range_iff_exists_fun (R := A) (v := y) (x := b)).1 hb_mem
  refine ⟨∑ i, MvPolynomial.C (c i) * MvPolynomial.X i, ?_⟩
  -- Proof comment: the evaluation map sends `C (c i) * X i` to the corresponding scalar multiple
  -- `c i • y i`, so the chosen spanning expression lifts coefficientwise.
  calc
    MvPolynomial.aeval y (∑ i, MvPolynomial.C (c i) * MvPolynomial.X i)
        = ∑ i, MvPolynomial.aeval y (MvPolynomial.C (c i) * MvPolynomial.X i) := by
            simp
    _ = ∑ i, c i • y i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [smul_eq_mul]
    _ = b := hc

/-- Helper for Lemma 15.82.5: a spanning family over `A` still spans after restricting scalars
to a surjective polynomial presentation of `A`. -/
private theorem span_top_restrictScalars_of_surjective_presentation
    {n l : ℕ} (α : MvPolynomial (Fin n) R →ₐ[R] A) (hα : Function.Surjective α)
    (y : Fin l → B) (hy : Submodule.span A (Set.range y) = ⊤) :
    Submodule.span (MvPolynomial (Fin n) R) (Set.range y) = ⊤ := by
  -- Proof comment: lift the `A`-coefficients in a spanning expression for `b` through the
  -- surjective presentation map `α`, then reuse the same finite linear combination over the
  -- polynomial ring.
  refine top_le_iff.mp ?_
  intro b hb
  have hbA : b ∈ Submodule.span A (Set.range y) := by
    simpa [hy]
  obtain ⟨c, hc⟩ :=
    (Submodule.mem_span_range_iff_exists_fun (R := A) (v := y) (x := b)).1 hbA
  choose cLift hcLift using fun i : Fin l ↦ hα (c i)
  rw [hc]
  refine Submodule.sum_mem _ ?_
  intro i hi
  have hsmul : c i • y i = cLift i • y i := by
    change algebraMap A B (c i) * y i = algebraMap (MvPolynomial (Fin n) R) B (cLift i) * y i
    rw [show algebraMap (MvPolynomial (Fin n) R) B (cLift i) =
        algebraMap A B (α (cLift i)) by
          rfl]
    simp [hcLift i, mul_comm]
  rw [hsmul]
  exact
    Submodule.smul_mem (Submodule.span (MvPolynomial (Fin n) R) (Set.range y)) (cLift i)
      (Submodule.subset_span ⟨i, rfl⟩)

/-- Helper for Lemma 15.82.5: a finite `A`-algebra over a fixed surjective polynomial
presentation admits the source-faithful quotient cover by monic relations. -/
private theorem monic_relation_quotient_cover_of_finite_extension
    {n : ℕ} (α : MvPolynomial (Fin n) R →ₐ[R] A) (hα : Function.Surjective α) :
    ∃ (l : ℕ) (G : Fin l → Polynomial (MvPolynomial (Fin n) R))
      (β : MvPolynomial (Fin l) (MvPolynomial (Fin n) R) →ₐ[MvPolynomial (Fin n) R] B)
      (π :
        (MvPolynomial (Fin l) (MvPolynomial (Fin n) R) ⧸
          Ideal.span (Set.range fun i : Fin l ↦
            Polynomial.aeval (MvPolynomial.X i) (G i))) →ₐ[MvPolynomial (Fin n) R] B),
      Function.Surjective β ∧
        Function.Surjective π ∧
        (∀ i, (G i).Monic) ∧
        (∀ i,
          β (Polynomial.aeval (MvPolynomial.X i) (G i)) = 0) ∧
        π.comp
            (Ideal.Quotient.mkₐ (MvPolynomial (Fin n) R)
              (Ideal.span (Set.range fun i : Fin l ↦
                Polynomial.aeval (MvPolynomial.X i) (G i)))
              : MvPolynomial (Fin l) (MvPolynomial (Fin n) R) →ₐ[MvPolynomial (Fin n) R]
                  (MvPolynomial (Fin l) (MvPolynomial (Fin n) R) ⧸
                    Ideal.span (Set.range fun i : Fin l ↦
                      Polynomial.aeval (MvPolynomial.X i) (G i)))) =
          β := by
  obtain ⟨l, y, G, hy, hGmonic, hGy⟩ :=
    exists_generators_with_lifted_monic_relations_of_finite (R := R) (A := A) (B := B) α hα
  let P := MvPolynomial (Fin n) R
  letI : Algebra P A := α.toAlgebra
  letI : Algebra P B := ((algebraMap A B).comp α).toAlgebra
  letI : IsScalarTower R P B := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change algebraMap R B r = algebraMap A B (α (algebraMap R P r))
    rw [α.commutes, IsScalarTower.algebraMap_apply R A B r]
  let hyP : Submodule.span P (Set.range y) = ⊤ :=
    span_top_restrictScalars_of_surjective_presentation (R := R) (A := A) (B := B) α hα y hy
  let β : MvPolynomial (Fin l) P →ₐ[P] B := MvPolynomial.aevalAlgHom y
  have hβ_surj : Function.Surjective β := by
    -- Proof comment: once the generators span after restriction to `P`, coefficientwise
    -- polynomial evaluation becomes surjective.
    simpa [P, β] using
      mvPolynomial_aevalAlgHom_surjective_of_span_top (A := P) (B := B) y hyP
  have hβ_rel :
      ∀ i : Fin l,
        β (Polynomial.aeval (MvPolynomial.X i) (G i)) = 0 := by
    intro i
    -- Proof comment: the chosen lifted monic relation already vanishes after evaluating the
    -- coefficients through `α` and the variable through `y i`.
    change Polynomial.aeval (y i) (Polynomial.map (algebraMap P B) (G i)) = 0
    simpa [P] using hGy i
  let I : Ideal (MvPolynomial (Fin l) P) :=
    Ideal.span (Set.range fun i : Fin l ↦ Polynomial.aeval (MvPolynomial.X i) (G i))
  let π :
      (MvPolynomial (Fin l) P ⧸ I) →ₐ[P] B :=
    Ideal.Quotient.liftₐ I β <| by
      intro z hz
      have hIker : I ≤ RingHom.ker β.toRingHom := by
        refine Ideal.span_le.2 ?_
        intro z hz
        rcases hz with ⟨i, rfl⟩
        simpa [RingHom.mem_ker] using hβ_rel i
      simpa [RingHom.mem_ker] using hIker hz
  have hπ_surj : Function.Surjective π := by
    -- Proof comment: surjectivity descends through the quotient because `π` was built by lifting
    -- the already surjective map `β`.
    intro b
    rcases hβ_surj b with ⟨z, rfl⟩
    exact ⟨Ideal.Quotient.mk I z, rfl⟩
  refine ⟨l, G, β, π, hβ_surj, hπ_surj, hGmonic, hβ_rel, ?_⟩
  -- Proof comment: the quotient map was defined by `Ideal.Quotient.liftₐ`, so its composite with
  -- the quotient projection is literally `β`.
  ext z
  rfl

/-- Helper for Lemma 15.82.5: an iterated polynomial presentation over
`MvPolynomial (Fin n) R` can be flattened to a single polynomial presentation over `R`. -/
private theorem flatten_iterated_polynomial_presentation_surjective
    {n l : ℕ}
    (β : MvPolynomial (Fin l) (MvPolynomial (Fin n) R) →ₐ[MvPolynomial (Fin n) R] B)
    (hβ : Function.Surjective β) :
    ∃ ρ : MvPolynomial (Fin (l + n)) R →ₐ[R] B, Function.Surjective ρ := by
  let ePoly :
      MvPolynomial (Fin (l + n)) R ≃ₐ[R] MvPolynomial (Fin l) (MvPolynomial (Fin n) R) :=
    (MvPolynomial.renameEquiv R (finSumFinEquiv.symm)).trans
      (MvPolynomial.sumAlgEquiv R (Fin l) (Fin n))
  let ρ : MvPolynomial (Fin (l + n)) R →ₐ[R] B :=
    (β.restrictScalars R).comp ePoly.toAlgHom
  -- Proof comment: the flattening equivalence is bijective, so surjectivity is inherited from the
  -- original iterated polynomial cover.
  exact ⟨ρ, Function.Surjective.comp hβ ePoly.surjective⟩

/-
Domain-style sampling for Lemma 15.82.5:
- primary domain: relative pseudo-coherence in derived categories under restriction of scalars
  along a finite algebra map;
- sampled owner declarations:
  `DerivedCategory.IsMPseudoCoherentRelativeTo`,
  `DerivedCategory.IsPseudoCoherentRelativeTo`,
  `isMPseudoCoherent_iff_restrictScalars`,
  `isPseudoCoherent_iff_restrictScalars`;
- best owner abstraction: the source-facing content is the pair of comparison theorems below,
  while the canonical owner predicates are
  `DerivedCategory.IsMPseudoCoherentRelativeTo` and
  `DerivedCategory.IsPseudoCoherentRelativeTo`; the restriction construction itself is owned by
  `(ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory`;
- primitive vs. derived:
  primitive data are the relative pseudo-coherence owners, the finite-type structure on `A` over
  `R`, and the finite map hypothesis `[Module.Finite A B]`;
  the induced finite-type structure on `B` over `R` is derived internally by the canonical
  transitivity instance for finite type algebras;
- source/core/bridge triage:
  `source-facing`: the two comparison theorems below;
  `core/canonical`: `DerivedCategory.IsMPseudoCoherentRelativeTo`,
    `DerivedCategory.IsPseudoCoherentRelativeTo`, and `Functor.mapDerivedCategory`;
  `bridge/view`: restriction of scalars along `algebraMap A B`, together with the internal
    finite-type witness on `R → B`.
-/

/-- Helper for Lemma 15.82.5: the regular module of the monic-relation quotient is
pseudo-coherent over the source polynomial ring. -/
private theorem monic_relation_quotient_regularModule_isPseudoCoherent_over_source
    {n l : ℕ}
    (G : Fin l → Polynomial (MvPolynomial (Fin n) R))
    (hGmonic : ∀ i, (G i).Monic) :
    ((ModuleCat.restrictScalars
        (Ideal.Quotient.mkₐ (MvPolynomial (Fin n) R)
          (Ideal.span (Set.range fun i : Fin l ↦
            Polynomial.aeval (MvPolynomial.X i) (G i)))).toRingHom).obj
      (ModuleCat.of
        ((MvPolynomial (Fin l) (MvPolynomial (Fin n) R)) ⧸
          Ideal.span (Set.range fun i : Fin l ↦
            Polynomial.aeval (MvPolynomial.X i) (G i)))
        ((MvPolynomial (Fin l) (MvPolynomial (Fin n) R)) ⧸
          Ideal.span (Set.range fun i : Fin l ↦
            Polynomial.aeval (MvPolynomial.X i) (G i))))).IsPseudoCoherent := by
  -- TODO: source-side endpoint. The source-faithful route is to resolve the quotient regular
  -- module over `P[y]` by the finite free complex coming from the monic relations.
  let _ := hGmonic
  sorry

/-- Helper for Lemma 15.82.5: splitting off the first monic relation identifies the full quotient
with an `AdjoinRoot` over the quotient by the remaining relations. -/
private theorem monic_relation_quotient_succ_adjoinRoot_algEquiv
    {n l : ℕ}
    (G : Fin (l + 1) → Polynomial (MvPolynomial (Fin n) R)) :
    let P : Type u := MvPolynomial (Fin n) R
    let S : Type u := MvPolynomial (Fin l) P
    let Iprev : Ideal S :=
      Ideal.span (Set.range fun i : Fin l ↦
        Polynomial.aeval (MvPolynomial.X i) (G i.succ))
    let f0 : Polynomial (S ⧸ Iprev) :=
      Polynomial.map (Ideal.Quotient.mk Iprev)
        (Polynomial.map (MvPolynomial.C : P →+* S) (G 0))
    ((MvPolynomial (Fin (l + 1)) P) ⧸
      Ideal.span (Set.range fun i : Fin (l + 1) ↦
        Polynomial.aeval (MvPolynomial.X i) (G i))) ≃ₐ[P] AdjoinRoot f0 := by
  -- TODO: use `MvPolynomial.finSuccEquiv` to separate the first variable, identify the remaining
  -- relations with the coefficient ideal `Iprev`, pass to a double quotient, and then apply
  -- `AdjoinRoot.quotEquivQuotMap` to reach the quotient over `S ⧸ Iprev`.
  sorry

/-- Helper for Lemma 15.82.5: the regular module of the monic-relation quotient is
pseudo-coherent over the base presentation ring. -/
private theorem monic_relation_quotient_regularModule_isPseudoCoherent_over_base
    {n l : ℕ}
    (G : Fin l → Polynomial (MvPolynomial (Fin n) R))
    (hGmonic : ∀ i, (G i).Monic) :
    ((ModuleCat.restrictScalars
        (algebraMap (MvPolynomial (Fin n) R)
          ((MvPolynomial (Fin l) (MvPolynomial (Fin n) R)) ⧸
            Ideal.span (Set.range fun i : Fin l ↦
              Polynomial.aeval (MvPolynomial.X i) (G i))))).obj
      (ModuleCat.of
        ((MvPolynomial (Fin l) (MvPolynomial (Fin n) R)) ⧸
          Ideal.span (Set.range fun i : Fin l ↦
            Polynomial.aeval (MvPolynomial.X i) (G i)))
        ((MvPolynomial (Fin l) (MvPolynomial (Fin n) R)) ⧸
          Ideal.span (Set.range fun i : Fin l ↦
            Polynomial.aeval (MvPolynomial.X i) (G i))))).IsPseudoCoherent := by
  -- Route correction: this is the base-side induction from the source proof. Split off the first
  -- monic relation, identify the quotient with an `AdjoinRoot` over the previous-stage quotient,
  -- and then compose pseudo-coherence along `P → Q_prev → AdjoinRoot`.
  induction l with
  | zero =>
      let P : Type u := MvPolynomial (Fin n) R
      let e :
          ((MvPolynomial (Fin 0) P) ⧸
            Ideal.span (Set.range fun i : Fin 0 ↦
              Polynomial.aeval (MvPolynomial.X i) (G i))) ≃ₐ[P] P :=
        (AlgEquiv.quotientBot P (MvPolynomial (Fin 0) P)).trans
          (MvPolynomial.isEmptyAlgEquiv P (Fin 0))
      -- Proof comment: with no relations and no variables, the quotient ring is just the base
      -- presentation ring `P`.
      simpa [P] using
        restrictScalars_regularModule_isPseudoCoherent_of_ringEquiv e.symm.toRingEquiv
  | succ l ih =>
      let P : Type u := MvPolynomial (Fin n) R
      let S : Type u := MvPolynomial (Fin l) P
      let Iprev : Ideal S :=
        Ideal.span (Set.range fun i : Fin l ↦
          Polynomial.aeval (MvPolynomial.X i) (G i.succ))
      let Qprev : Type u := S ⧸ Iprev
      let f0 : Polynomial Qprev :=
        Polynomial.map (Ideal.Quotient.mk Iprev)
          (Polynomial.map (MvPolynomial.C : P →+* S) (G 0))
      have hPrev :
          ((ModuleCat.restrictScalars (algebraMap P Qprev)).obj
            (ModuleCat.of Qprev Qprev)).IsPseudoCoherent := by
        -- Proof comment: the induction hypothesis gives the previous-stage quotient over the same
        -- base presentation ring `P`.
        simpa [P, S, Iprev, Qprev] using
          ih (fun i : Fin l ↦ hGmonic i.succ)
      have hf0_monic : f0.Monic := by
        -- Proof comment: monicity survives first through coefficient inclusion into `S` and then
        -- through passage to the quotient `Qprev`.
        simpa [f0] using
          (((hGmonic 0).map (MvPolynomial.C : P →+* S)).map (Ideal.Quotient.mk Iprev))
      have hAdjoinOverQprev :
          ((ModuleCat.restrictScalars (algebraMap Qprev (AdjoinRoot f0))).obj
            (ModuleCat.of (AdjoinRoot f0) (AdjoinRoot f0))).IsPseudoCoherent := by
        -- Proof comment: a single monic `AdjoinRoot` stage is finite free over its coefficient
        -- ring.
        exact monic_adjoinRoot_regularModule_isPseudoCoherent f0 hf0_monic
      have hAdjoinOverP :
          ((ModuleCat.restrictScalars (algebraMap P (AdjoinRoot f0))).obj
            (ModuleCat.of (AdjoinRoot f0) (AdjoinRoot f0))).IsPseudoCoherent := by
        have hModuleOverQprev :
            (ModuleCat.of Qprev (AdjoinRoot f0)).IsPseudoCoherent := by
          simpa using hAdjoinOverQprev
        -- Proof comment: compose pseudo-coherence along `P → Qprev` with the one-step
        -- `AdjoinRoot` stage over `Qprev`.
        simpa using
          moduleCat_restrictScalars_isPseudoCoherent
            (f := algebraMap P Qprev) hPrev hModuleOverQprev
      let eSucc :
          ((MvPolynomial (Fin (l + 1 + 1)) P) ⧸
            Ideal.span (Set.range fun i : Fin (l + 1 + 1) ↦
              Polynomial.aeval (MvPolynomial.X i) (G i))) ≃ₐ[P] AdjoinRoot f0 :=
        monic_relation_quotient_succ_adjoinRoot_algEquiv (R := R) (n := n) (l := l) G
      let eModule :
          ((ModuleCat.restrictScalars
              (algebraMap P
                ((MvPolynomial (Fin (l + 1 + 1)) P) ⧸
                  Ideal.span (Set.range fun i : Fin (l + 1 + 1) ↦
                    Polynomial.aeval (MvPolynomial.X i) (G i))))).obj
            (ModuleCat.of
              ((MvPolynomial (Fin (l + 1 + 1)) P) ⧸
                Ideal.span (Set.range fun i : Fin (l + 1 + 1) ↦
                  Polynomial.aeval (MvPolynomial.X i) (G i)))
              ((MvPolynomial (Fin (l + 1 + 1)) P) ⧸
                Ideal.span (Set.range fun i : Fin (l + 1 + 1) ↦
                  Polynomial.aeval (MvPolynomial.X i) (G i))))) ≅
            ((ModuleCat.restrictScalars (algebraMap P (AdjoinRoot f0))).obj
              (ModuleCat.of (AdjoinRoot f0) (AdjoinRoot f0))) :=
        eSucc.toLinearEquiv.toModuleIso
      -- Proof comment: the structural quotient equivalence turns the target regular module into
      -- the `AdjoinRoot` regular module already handled above.
      simpa [P] using moduleCat_isPseudoCoherent_of_iso eModule hAdjoinOverP

/-- Helper for Lemma 15.82.5: once a fixed surjective polynomial presentation `α : P → A` is
refined to the source-faithful monic quotient cover `Q → B`, absolute `m`-pseudo-coherence over
`P[y]` is equivalent to absolute `m`-pseudo-coherence over `P` for the same derived `B`-complex. -/
private theorem absolute_isMPseudoCoherent_iff_of_monic_relation_quotient_cover
    {n l : ℕ}
    (α : MvPolynomial (Fin n) R →ₐ[R] A) (hα : Function.Surjective α)
    (G : Fin l → Polynomial (MvPolynomial (Fin n) R))
    (β : MvPolynomial (Fin l) (MvPolynomial (Fin n) R) →ₐ[MvPolynomial (Fin n) R] B)
    (π :
      (MvPolynomial (Fin l) (MvPolynomial (Fin n) R) ⧸
        Ideal.span (Set.range fun i : Fin l ↦
          Polynomial.aeval (MvPolynomial.X i) (G i))) →ₐ[MvPolynomial (Fin n) R] B)
    (hβ_surj : Function.Surjective β)
    (hπ_surj : Function.Surjective π)
    (hGmonic : ∀ i, (G i).Monic)
    (hβ_rel : ∀ i, β (Polynomial.aeval (MvPolynomial.X i) (G i)) = 0)
    (hπ_comp :
      π.comp
          (Ideal.Quotient.mkₐ (MvPolynomial (Fin n) R)
            (Ideal.span (Set.range fun i : Fin l ↦
              Polynomial.aeval (MvPolynomial.X i) (G i)))
            : MvPolynomial (Fin l) (MvPolynomial (Fin n) R) →ₐ[MvPolynomial (Fin n) R]
                (MvPolynomial (Fin l) (MvPolynomial (Fin n) R) ⧸
                  Ideal.span (Set.range fun i : Fin l ↦
                    Polynomial.aeval (MvPolynomial.X i) (G i)))) =
        β)
    (K : DModB) (m : ℤ) :
    ((ModuleCat.restrictScalars β.toRingHom).mapDerivedCategory.obj K).IsMPseudoCoherent m ↔
      ((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj
        ((restrictScalarsDerived).obj K)).IsMPseudoCoherent m := by
  -- Route correction: the main theorem is now reduced to the exact textbook fixed-presentation
  -- comparison. The remaining work is to show that the common quotient ring `Q` is
  -- pseudo-coherent both over `P` and over `P[y]`, then apply Lemma `15.65.11` twice through `π`.
  let P : Type u := MvPolynomial (Fin n) R
  let I : Ideal (MvPolynomial (Fin l) P) :=
    Ideal.span (Set.range fun i : Fin l ↦ Polynomial.aeval (MvPolynomial.X i) (G i))
  let Q : Type u := (MvPolynomial (Fin l) P) ⧸ I
  let q : MvPolynomial (Fin l) P →ₐ[P] Q := Ideal.Quotient.mkₐ P I
  let KQ : DerivedCategory (ModuleCat Q) :=
    ((ModuleCat.restrictScalars π.toRingHom).mapDerivedCategory.obj K)
  have hq_pseudo :
      ((ModuleCat.restrictScalars q.toRingHom).obj (ModuleCat.of Q Q)).IsPseudoCoherent := by
    -- Proof comment: this is exactly the source-side regular-module input for the first
    -- application of Lemma `15.65.11`.
    simpa [q, I, Q] using
      monic_relation_quotient_regularModule_isPseudoCoherent_over_source
        (R := R) G hGmonic
  have hQ_pseudo :
      ((ModuleCat.restrictScalars (algebraMap P Q)).obj (ModuleCat.of Q Q)).IsPseudoCoherent := by
    -- Proof comment: this is the base-side regular-module input for the second application of
    -- Lemma `15.65.11`.
    simpa [I, Q] using
      monic_relation_quotient_regularModule_isPseudoCoherent_over_base
        (R := R) G hGmonic
  have hleft :
      ((ModuleCat.restrictScalars β.toRingHom).mapDerivedCategory.obj K).IsMPseudoCoherent m ↔
        KQ.IsMPseudoCoherent m := by
    -- Proof comment: `β` factors as the quotient map `q` followed by `π`, so restriction along
    -- `β` is the same as first viewing `K` over `Q` and then restricting along `q`.
    simpa [KQ, q, I, hπ_comp, RingHom.comp_assoc] using
      (isMPseudoCoherent_iff_restrictScalars (K := KQ) (m := m) hq_pseudo).symm
  have hright :
      KQ.IsMPseudoCoherent m ↔
        ((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj
          ((restrictScalarsDerived).obj K)).IsMPseudoCoherent m := by
    -- Proof comment: the `P`-algebra structure on `Q` transported through `π` recovers the
    -- original `P → A → B` restriction route.
    simpa [KQ, restrictScalarsDerived, RingHom.comp_assoc] using
      (isMPseudoCoherent_iff_restrictScalars (K := KQ) (m := m) hQ_pseudo)
  exact hleft.trans hright

-- Proof sketch: for any surjective polynomial presentation `P → A`, compose with the finite map
-- `A → B` to view `B` as a finite `P`-algebra, then apply Lemma `15.65.11` over `P` to compare
-- `m`-pseudo-coherence of `K` with that of its restriction along `A → B`.
/-- Lemma 15.82.5: let `R` be a ring, let `A → B` be a finite map of finite type `R`-algebras,
let `m ∈ ℤ`, and let `K` be a derived `B`-complex. Then `K` is `m`-pseudo-coherent relative to
`R` if and only if the same object, viewed by restriction of scalars as a derived `A`-complex, is
`m`-pseudo-coherent relative to `R`. -/
theorem isMPseudoCoherentRelativeTo_iff_restrictScalars_of_finite
    (K : DModB) (m : ℤ) :
    by
      letI : Algebra.FiniteType R B := finiteType_over_base R A B
      exact
        K.IsMPseudoCoherentRelativeTo R m ↔
          ((restrictScalarsDerived).obj K).IsMPseudoCoherentRelativeTo R m := by
  constructor
  · intro hK
    intro n α hα
    obtain ⟨l, G, β, π, hβ_surj, hπ_surj, hGmonic, hβ_rel, hπ_comp⟩ :=
      monic_relation_quotient_cover_of_finite_extension (R := R) (A := A) (B := B) α hα
    let ePoly :
        MvPolynomial (Fin (l + n)) R ≃ₐ[R] MvPolynomial (Fin l) (MvPolynomial (Fin n) R) :=
      (MvPolynomial.renameEquiv R (finSumFinEquiv.symm)).trans
        (MvPolynomial.sumAlgEquiv R (Fin l) (Fin n))
    let ρ : MvPolynomial (Fin (l + n)) R →ₐ[R] B :=
      (β.restrictScalars R).comp ePoly.toAlgHom
    have hρ_surj : Function.Surjective ρ := by
      -- Proof comment: the flattening ring equivalence is bijective, so surjectivity reduces to
      -- the already constructed surjective iterated polynomial cover `β`.
      exact Function.Surjective.comp hβ_surj ePoly.surjective
    have hEqReg :
        ((ModuleCat.restrictScalars ePoly.toRingHom).obj
          (ModuleCat.of (MvPolynomial (Fin l) (MvPolynomial (Fin n) R))
            (MvPolynomial (Fin l) (MvPolynomial (Fin n) R)))).IsPseudoCoherent := by
      -- Proof comment: restriction along a polynomial-ring equivalence preserves the free rank-one
      -- regular module.
      exact restrictScalars_regularModule_isPseudoCoherent_of_ringEquiv ePoly
    have hβ_iff :
        ((ModuleCat.restrictScalars β.toRingHom).mapDerivedCategory.obj K).IsMPseudoCoherent m ↔
          ((ModuleCat.restrictScalars ρ.toRingHom).mapDerivedCategory.obj K).IsMPseudoCoherent m := by
      -- Proof comment: `ρ` is exactly `β` after precomposing with the polynomial flattening
      -- equivalence.
      simpa [ρ] using
        (isMPseudoCoherent_iff_restrictScalars
          (((ModuleCat.restrictScalars β.toRingHom).mapDerivedCategory.obj K))
          m hEqReg)
    have hρK :
        ((ModuleCat.restrictScalars ρ.toRingHom).mapDerivedCategory.obj K).IsMPseudoCoherent m :=
      hK (l + n) ρ hρ_surj
    have hβK :
        ((ModuleCat.restrictScalars β.toRingHom).mapDerivedCategory.obj K).IsMPseudoCoherent m :=
      hβ_iff.2 hρK
    -- Proof comment: the remaining source-faithful step is the fixed-presentation comparison
    -- through the common monic quotient cover `Q`.
    exact
      (absolute_isMPseudoCoherent_iff_of_monic_relation_quotient_cover
        (R := R) (A := A) (B := B)
        α hα G β π hβ_surj hπ_surj hGmonic hβ_rel hπ_comp K m).1 hβK
  · intro hK
    rcases
      Algebra.FiniteType.iff_quotient_mvPolynomial''.1
        (inferInstance : Algebra.FiniteType R A) with ⟨n, α, hα⟩
    obtain ⟨l, G, β, π, hβ_surj, hπ_surj, hGmonic, hβ_rel, hπ_comp⟩ :=
      monic_relation_quotient_cover_of_finite_extension (R := R) (A := A) (B := B) α hα
    let ePoly :
        MvPolynomial (Fin (l + n)) R ≃ₐ[R] MvPolynomial (Fin l) (MvPolynomial (Fin n) R) :=
      (MvPolynomial.renameEquiv R (finSumFinEquiv.symm)).trans
        (MvPolynomial.sumAlgEquiv R (Fin l) (Fin n))
    let ρ : MvPolynomial (Fin (l + n)) R →ₐ[R] B :=
      (β.restrictScalars R).comp ePoly.toAlgHom
    have hρ_surj : Function.Surjective ρ := by
      -- Proof comment: the flattened cover is still surjective because `ePoly` is an equivalence
      -- and `β` was chosen surjective.
      exact Function.Surjective.comp hβ_surj ePoly.surjective
    have hEqReg :
        ((ModuleCat.restrictScalars ePoly.toRingHom).obj
          (ModuleCat.of (MvPolynomial (Fin l) (MvPolynomial (Fin n) R))
            (MvPolynomial (Fin l) (MvPolynomial (Fin n) R)))).IsPseudoCoherent := by
      -- Proof comment: this is the same polynomial-ring equivalence transport as in the forward
      -- direction.
      exact restrictScalars_regularModule_isPseudoCoherent_of_ringEquiv ePoly
    have hβ_iff :
        ((ModuleCat.restrictScalars β.toRingHom).mapDerivedCategory.obj K).IsMPseudoCoherent m ↔
          ((ModuleCat.restrictScalars ρ.toRingHom).mapDerivedCategory.obj K).IsMPseudoCoherent m := by
      -- Proof comment: rewrite the flattened presentation back to the iterated polynomial
      -- presentation before invoking Lemma `15.65.11`.
      simpa [ρ] using
        (isMPseudoCoherent_iff_restrictScalars
          (((ModuleCat.restrictScalars β.toRingHom).mapDerivedCategory.obj K))
          m hEqReg)
    have hAα :
        ((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj
          ((restrictScalarsDerived).obj K)).IsMPseudoCoherent m :=
      hK n α hα
    have hβK :
        ((ModuleCat.restrictScalars β.toRingHom).mapDerivedCategory.obj K).IsMPseudoCoherent m :=
      (absolute_isMPseudoCoherent_iff_of_monic_relation_quotient_cover
        (R := R) (A := A) (B := B)
        α hα G β π hβ_surj hπ_surj hGmonic hβ_rel hπ_comp K m).2 hAα
    have hρK :
        ((ModuleCat.restrictScalars ρ.toRingHom).mapDerivedCategory.obj K).IsMPseudoCoherent m :=
      hβ_iff.1 hβK
    -- Proof comment: one flattened polynomial presentation of `B` is enough to recover the full
    -- relative condition via the previously proved “some presentation” criterion.
    exact
      (derived_isMPseudoCoherentRelativeTo_iff_overSomePolynomialPresentation
        (R := R) (S := B) K m).2
        ⟨l + n, ρ, hρ_surj, hρK⟩

-- Proof sketch: apply the previous theorem for each integer `m`, using the canonical owner
-- `IsPseudoCoherentRelativeTo` as the universal quantification of the `m`-relative notion.
/-- Under the same finite-map hypotheses, relative pseudo-coherence over `R` is unchanged by
restricting scalars from `B` to `A`. -/
theorem isPseudoCoherentRelativeTo_iff_restrictScalars_of_finite
    (K : DModB) :
    by
      letI : Algebra.FiniteType R B := finiteType_over_base R A B
      exact
        K.IsPseudoCoherentRelativeTo R ↔
          ((restrictScalarsDerived).obj K).IsPseudoCoherentRelativeTo R := by
  rw [DerivedCategory.IsPseudoCoherentRelativeTo]
  constructor
  · intro hK m
    -- Apply the degreewise finite-map comparison at the chosen integer `m`.
    exact (isMPseudoCoherentRelativeTo_iff_restrictScalars_of_finite K m).1 (hK m)
  · intro hK m
    -- Reverse the same degreewise comparison to recover the original relative statement.
    exact (isMPseudoCoherentRelativeTo_iff_restrictScalars_of_finite K m).2 (hK m)

end

end CategoryTheory
