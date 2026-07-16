import stacks_proof.stacks_project.Chap10.Lemma_10_118_3.FinitelyPresentedGenericFreeness.OwnerLocalization

universe u v w

section

variable {R : Type u} [CommRing R] [IsDomain R]
variable {S : Type v} [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
variable {M : Type w} [AddCommGroup M] [Module S M] [Module.Finite S M]

open GenericFlatness

attribute [local instance] MvPolynomial.algebraMvPolynomial

omit [IsDomain R] [Algebra.FiniteType R S] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: a surjective ring map with finitely generated kernel makes
the target finitely presented as a module over the source. -/
lemma moduleFinitePresentation_of_surjectiveRingHom_fg_ker
    {A B : Type*} [CommRing A] [CommRing B]
    (π : A →+* B) (hπ : Function.Surjective π) (hker : (RingHom.ker π).FG) :
    letI : Algebra A B := π.toAlgebra
    Module.FinitePresentation A B := by
  letI : Algebra A B := π.toAlgebra
  let q : A →ₗ[A] B := Algebra.linearMap A B
  have hq : Function.Surjective q := by
    -- Proof comment: the linear map attached to `π.toAlgebra` is just the original surjective
    -- ring map.
    intro b
    obtain ⟨a, ha⟩ := hπ b
    exact ⟨a, by simpa [q, Algebra.linearMap_apply, RingHom.algebraMap_toAlgebra] using ha⟩
  have hqker : LinearMap.ker q = (RingHom.ker π : Submodule A A) := by
    -- Proof comment: the kernel comparison exposes the supplied finitely generated relation
    -- ideal as the relation module of the one-generator presentation `A → B`.
    ext a
    simp [q, RingHom.mem_ker, RingHom.algebraMap_toAlgebra]
  have hqker_fg : (LinearMap.ker q).FG := by
    simpa [hqker] using hker
  -- Proof comment: present `B` as the quotient of the free rank-one `A`-module by this kernel.
  exact Module.finitePresentation_of_surjective q hq hqker_fg

omit [IsDomain R] [Algebra.FiniteType R S] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: finite presentation of a module descends along a
surjective presentation algebra once the presentation kernel is finitely generated. -/
lemma moduleFinitePresentation_restrictScalars_of_surjectiveRingHom_fg_ker
    {A B : Type*} [CommRing A] [CommRing B]
    (π : A →+* B) (hπ : Function.Surjective π) (hker : (RingHom.ker π).FG)
    {N : Type*} [AddCommGroup N] [Module B N] [Module.FinitePresentation B N] :
    letI : Algebra A B := π.toAlgebra
    letI : Module A N := Module.compHom N π
    Module.FinitePresentation A N := by
  letI : Algebra A B := π.toAlgebra
  letI : Module A N := Module.compHom N π
  letI : IsScalarTower A B N := RestrictScalars.isScalarTower A B N
  have hB : Module.FinitePresentation A B :=
    moduleFinitePresentation_of_surjectiveRingHom_fg_ker π hπ hker
  letI : Module.FinitePresentation A B := hB
  -- Proof comment: transitivity turns the finite `B`-presentation of `N` into a finite
  -- presentation over the chosen polynomial presentation algebra.
  exact Module.FinitePresentation.trans (R := A) (S := B) (M := N)

omit [Algebra.FiniteType R S] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: coefficient-away freeness over a polynomial presentation
transports to owner-away freeness over the presented algebra. -/
lemma ownerAway_free_of_coeffAway_free_presentation
    {n : ℕ} {A : Type*} [CommRing A] [Algebra R A]
    [Algebra (MvPolynomial (Fin n) R) A]
    [IsScalarTower R (MvPolynomial (Fin n) R) A]
    {N : Type*} [AddCommGroup N] [Module A N]
    [Module (MvPolynomial (Fin n) R) N]
    [IsScalarTower (MvPolynomial (Fin n) R) A N]
    (f : R)
    [Module.Free (Localization.Away f)
      (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N)] :
    Module.Free (Localization.Away f)
      (LocalizedModule.Away (algebraMap R A f) N) := by
  let Acoeff := MvPolynomial (Fin n) (Localization.Away f)
  let Bloc := Localization.Away (algebraMap R A f)
  let T := LocalizedModule.Away (algebraMap R A f) N
  letI : Algebra Acoeff Bloc :=
    localizedCoeffAwayOwnerAlgebra (R := R) (S := A) (n := n) f
  letI : Module Acoeff T :=
    localizedCoeffAwayOwnerModule (R := R) (S := A) (M := N) (n := n) f
  letI : IsScalarTower (Localization.Away f) Acoeff Bloc :=
    localizedCoeffAwayOwnerAlgebra_isScalarTower (R := R) (S := A) (n := n) f
  letI : IsScalarTower Acoeff Bloc T :=
    localizedCoeffAwayOwnerModule_isScalarTower (R := R) (S := A) (M := N) (n := n) f
  letI : IsScalarTower (Localization.Away f) Acoeff T := by
    -- Proof comment: the base `R_f`-action obtained through `R_f[x]` is the canonical action
    -- through the owner localization because the owner evaluation hom fixes coefficients.
    refine IsScalarTower.of_algebraMap_smul ?_
    intro r x
    rw [MvPolynomial.algebraMap_eq]
    change localizedCoeffAwayOwnerAlgHom (R := R) (S := A) (n := n) f
        (MvPolynomial.C r) • x = r • x
    rw [localizedCoeffAwayOwnerAlgHom_C]
    rfl
  -- Proof comment: the existing `R_f[x]`-linear owner comparison carries the free basis from
  -- the coefficient-away model to the owner-localized module.
  exact away_polynomial_model_free_over_base_of_linearEquiv
    (R := R) (n := n) (N := N) (T := T) f
    (localizedCoeffAwayOwnerModuleCoeffLinearEquiv (R := R) (S := A) (M := N) (n := n) f)

omit [Algebra.FiniteType R S] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: the general finite-presentation source theorem follows
from the coefficient-denominator generic-freeness theorem for finite-variable polynomial modules. -/
lemma exists_nonzero_away_free_of_finitePresentation_algebra_module_of_coeffAway
    (hcoeff :
      ∀ {n : ℕ}
        {N₀ : Type w} [AddCommGroup N₀] [Module (MvPolynomial (Fin n) R) N₀]
        [Module.FinitePresentation (MvPolynomial (Fin n) R) N₀],
        ∃ f : R, f ≠ 0 ∧
          Module.Free (Localization.Away f)
            (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N₀))
    {A : Type v} [CommRing A] [Algebra R A] [Algebra.FinitePresentation R A]
    {N : Type w} [AddCommGroup N] [Module A N] [Module.FinitePresentation A N] :
    ∃ f : R, f ≠ 0 ∧
      Module.Free (Localization.Away f) (LocalizedModule.Away (algebraMap R A f) N) := by
  -- Proof comment: choose a finite polynomial presentation of the algebra and use it to view the
  -- module as finitely presented over the polynomial algebra.
  obtain ⟨n, I, e, hI⟩ :=
    (Algebra.FinitePresentation.iff (R := R) (A := A)).mp
      (inferInstance : Algebra.FinitePresentation R A)
  let P := MvPolynomial (Fin n) R
  let π : P →ₐ[R] A := e.toAlgHom.comp (Ideal.Quotient.mkₐ R I)
  have hπ : Function.Surjective π := by
    -- Proof comment: the quotient map is surjective, and the chosen algebra equivalence carries
    -- its image onto `A`.
    intro a
    obtain ⟨q, hq⟩ := Ideal.Quotient.mk_surjective (e.symm a)
    refine ⟨q, ?_⟩
    simp [π, hq]
  have hmk_zero (p : P) : (Ideal.Quotient.mk I) p = 0 ↔ p ∈ I := by
    -- Proof comment: this is the kernel computation for the quotient presentation map.
    rw [← map_zero (Ideal.Quotient.mk I), Ideal.Quotient.eq]
    simp
  have hker : RingHom.ker π.toRingHom = I := by
    -- Proof comment: the algebra equivalence is injective, so the kernel of the composite
    -- presentation map is exactly the quotient ideal `I`.
    ext p
    simp [π, RingHom.mem_ker, hmk_zero]
  have hker_fg : (RingHom.ker π.toRingHom).FG := by
    rw [hker]
    exact hI
  letI : Algebra P A := π.toRingHom.toAlgebra
  letI : IsScalarTower R P A := by
    -- Proof comment: the presentation algebra action is compatible with the original `R`-algebra
    -- structure because `π` is an `R`-algebra homomorphism.
    refine IsScalarTower.of_algebraMap_eq ?_
    intro r
    exact (π.commutes r).symm
  letI : Module P N := Module.compHom N π.toRingHom
  letI : IsScalarTower P A N := IsScalarTower.of_compHom P A N
  have hfpP : Module.FinitePresentation P N := by
    -- Proof comment: the finite presentation of `N` over `A` restricts across the surjective
    -- polynomial presentation because the presentation ideal is finitely generated.
    exact
      moduleFinitePresentation_restrictScalars_of_surjectiveRingHom_fg_ker
        (A := P) (B := A) π.toRingHom hπ hker_fg (N := N)
  letI : Module.FinitePresentation P N := hfpP
  obtain ⟨f, hf, hFreeCoeff⟩ := hcoeff (n := n) (N₀ := N)
  letI : Module.Free (Localization.Away f)
      (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N) := hFreeCoeff
  -- Proof comment: the owner-localization bridge transports freeness from the polynomial
  -- coefficient localization to the localization at `algebraMap R A f`.
  exact
    ⟨f, hf,
      ownerAway_free_of_coeffAway_free_presentation (R := R) (n := n) (A := A) (N := N) f⟩

omit [IsDomain R] [Algebra.FiniteType R S] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: a finitely presented module over a finite-variable
polynomial ring has a finite presentation object, together with its exact relation sequence and
quotient model. -/
lemma mvPolynomialModule_finitePresentationData
    {n : ℕ} {N : Type w} [AddCommGroup N] [Module (MvPolynomial (Fin n) R) N]
    [Module.FinitePresentation (MvPolynomial (Fin n) R) N] :
    ∃ pres : Module.Presentation.{w, w} (MvPolynomial (Fin n) R) N,
      Finite pres.G ∧ Finite pres.R ∧
        Function.Exact pres.toRelations.map pres.toSolution.π ∧
        Nonempty (pres.toRelations.Quotient ≃ₗ[MvPolynomial (Fin n) R] N) := by
  -- Proof comment: mathlib's finite-presentation characterization already packages finitely many
  -- generators and relations as a `Module.Presentation`.
  obtain ⟨pres, hG, hR⟩ :=
    (Module.finitePresentation_iff_exists_presentation
      (A := MvPolynomial (Fin n) R) (M := N)).mp inferInstance
  -- Proof comment: the presentation object exposes both the exact relation map and the quotient
  -- equivalence needed for the coefficient-subring descent route.
  exact ⟨pres, hG, hR, pres.toIsPresentation.exact, ⟨pres.toIsPresentation.linearEquiv⟩⟩

omit [IsDomain R] [Algebra.FiniteType R S] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: a finitely presented polynomial module is a quotient of a
finite free module by the range of a map from another finite free module. -/
lemma mvPolynomialModule_finiteFreeQuotientPresentation
    {n : ℕ} {N : Type w} [AddCommGroup N] [Module (MvPolynomial (Fin n) R) N]
    [Module.FinitePresentation (MvPolynomial (Fin n) R) N] :
    ∃ (m r : ℕ)
      (rel : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R]
        (Fin m → MvPolynomial (Fin n) R))
      (K : Submodule (MvPolynomial (Fin n) R) (Fin m → MvPolynomial (Fin n) R)),
      Nonempty (N ≃ₗ[MvPolynomial (Fin n) R]
        (Fin m → MvPolynomial (Fin n) R) ⧸ K) ∧ LinearMap.range rel = K := by
  let P := MvPolynomial (Fin n) R
  -- Proof comment: mathlib's finite-presentation API first gives a finite free quotient with a
  -- finitely generated kernel.
  obtain ⟨m, K, e, hK⟩ := Module.FinitePresentation.exists_fin P N
  -- Proof comment: finite generation of that kernel is equivalently a relation map from another
  -- finite free module, which is the concrete relation-list form needed for coefficient descent.
  obtain ⟨r, rel, hrel⟩ := (Submodule.fg_iff_exists_fin_linearMap P (Fin m → P)).mp hK
  refine ⟨m, r, rel, K, ?_, hrel⟩
  exact ⟨e⟩

omit [IsDomain R] [Algebra.FiniteType R S] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: the quotient of a finite free module by finite free
relations is finitely presented. -/
lemma finiteFreeRelationQuotient_finitePresentation
    {P : Type*} [Ring P] {m r : ℕ}
    (rel : (Fin r → P) →ₗ[P] (Fin m → P)) :
    Module.FinitePresentation P ((Fin m → P) ⧸ LinearMap.range rel) := by
  -- Proof comment: the quotient map is surjective, and its kernel is exactly the finitely
  -- generated range of the finite-free relation map.
  refine Module.finitePresentation_of_surjective (Submodule.mkQ (LinearMap.range rel))
    (Submodule.mkQ_surjective _) ?_
  change (LinearMap.ker (Submodule.mkQ (LinearMap.range rel))).FG
  rw [Submodule.ker_mkQ]
  exact Submodule.fg_range rel

omit [IsDomain R] [Algebra.FiniteType R S] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: a module modeled by a finite-free relation quotient is
itself finitely presented over the polynomial ring. -/
lemma finiteFreeRelationQuotientPresentation_finitePresentation
    {P : Type*} [Ring P] {m r : ℕ}
    {N : Type*} [AddCommGroup N] [Module P N]
    (rel : (Fin r → P) →ₗ[P] (Fin m → P))
    (e : Nonempty (N ≃ₗ[P] (Fin m → P) ⧸ LinearMap.range rel)) :
    Module.FinitePresentation P N := by
  -- Proof comment: first record finite presentation for the explicit relation quotient, then
  -- transport it back along the given linear equivalence.
  obtain ⟨e⟩ := e
  letI : Module.FinitePresentation P ((Fin m → P) ⧸ LinearMap.range rel) :=
    finiteFreeRelationQuotient_finitePresentation rel
  exact Module.FinitePresentation.of_equiv e.symm

omit [IsDomain R] [Algebra.FiniteType R S] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: the coefficients in a finite-free relation matrix lie in
one finitely generated coefficient subalgebra. -/
lemma mvPolynomialFiniteFreeRelation_relationCoeff_mem_adjoin
    {n m r : ℕ}
    (rel : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R]
      (Fin m → MvPolynomial (Fin n) R)) :
    ∃ coeffs : Finset R,
      ∀ (i : Fin r) (j : Fin m) (mon : Fin n →₀ ℕ),
        mon ∈ (rel (Pi.single i (1 : MvPolynomial (Fin n) R)) j).support →
        MvPolynomial.coeff mon (rel (Pi.single i (1 : MvPolynomial (Fin n) R)) j) ∈
          Algebra.adjoin ℤ (coeffs : Set R) := by
  classical
  let P := MvPolynomial (Fin n) R
  let coeffs : Finset R :=
    Finset.univ.biUnion fun i : Fin r =>
      Finset.univ.biUnion fun j : Fin m =>
        ((rel (Pi.single i (1 : P)) j).support.image fun mon : Fin n →₀ ℕ =>
          MvPolynomial.coeff mon (rel (Pi.single i (1 : P)) j))
  refine ⟨coeffs, ?_⟩
  intro i j mon hmon
  -- Proof comment: the finite set was built by ranging over every matrix entry and every
  -- monomial in its support, so the requested coefficient is one of its generators.
  apply Algebra.subset_adjoin
  rw [Finset.mem_coe]
  dsimp [coeffs]
  rw [Finset.mem_biUnion]
  refine ⟨i, Finset.mem_univ i, ?_⟩
  rw [Finset.mem_biUnion]
  refine ⟨j, Finset.mem_univ j, ?_⟩
  exact Finset.mem_image.mpr ⟨mon, hmon, rfl⟩

omit [IsDomain R] [Algebra.FiniteType R S] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: a polynomial whose coefficients lie in a coefficient
subalgebra lifts along the induced polynomial map from that subalgebra. -/
lemma mvPolynomial_mem_range_map_of_coeffs_subset_subalgebra
    {σ : Type*} {A : Subalgebra ℤ R} {p : MvPolynomial σ R}
    (hp : (p.coeffs : Set R) ⊆ A) :
    p ∈ Set.range (MvPolynomial.map (algebraMap A R)) := by
  -- Proof comment: mathlib reduces polynomial descent along a ring map to checking that all
  -- coefficients belong to the map range; for a subalgebra this range is just the carrier.
  rw [MvPolynomial.mem_range_map_iff_coeffs_subset, Subalgebra.setRange_algebraMap]
  exact hp

omit [IsDomain R] [Algebra.FiniteType R S] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: after adjoining the coefficients of a finite relation
matrix, every matrix entry has a polynomial lift over that coefficient subalgebra. -/
lemma mvPolynomialFiniteFreeRelation_lift_entries_coeffSubring
    {n m r : ℕ}
    (rel : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R]
      (Fin m → MvPolynomial (Fin n) R)) :
    ∃ coeffs : Finset R,
      ∃ lift : (i : Fin r) → (j : Fin m) →
          MvPolynomial (Fin n) (Algebra.adjoin ℤ (coeffs : Set R)),
        ∀ (i : Fin r) (j : Fin m),
          MvPolynomial.map (algebraMap (Algebra.adjoin ℤ (coeffs : Set R)) R)
              (lift i j) =
            rel (Pi.single i (1 : MvPolynomial (Fin n) R)) j := by
  classical
  obtain ⟨coeffs, hcoeffs⟩ :=
    mvPolynomialFiniteFreeRelation_relationCoeff_mem_adjoin (R := R) (n := n) rel
  have hlift_mem :
      ∀ (i : Fin r) (j : Fin m),
        rel (Pi.single i (1 : MvPolynomial (Fin n) R)) j ∈
          Set.range (MvPolynomial.map
            (algebraMap (Algebra.adjoin ℤ (coeffs : Set R)) R)) := by
    intro i j
    -- Proof comment: use the coefficient criterion entrywise, converting membership in
    -- `coeffs` to a support coefficient of the same entry.
    apply mvPolynomial_mem_range_map_of_coeffs_subset_subalgebra
    intro c hc
    have hc' : c ∈ (rel (Pi.single i (1 : MvPolynomial (Fin n) R)) j).coeffs := by
      simpa using hc
    rw [MvPolynomial.mem_coeffs_iff] at hc'
    obtain ⟨mon, hmon, rfl⟩ := hc'
    exact hcoeffs i j mon hmon
  let lift : (i : Fin r) → (j : Fin m) →
      MvPolynomial (Fin n) (Algebra.adjoin ℤ (coeffs : Set R)) :=
    fun i j ↦ Classical.choose (hlift_mem i j)
  refine ⟨coeffs, lift, ?_⟩
  intro i j
  -- Proof comment: the chosen lifts are exactly witnesses to the polynomial range criterion.
  exact Classical.choose_spec (hlift_mem i j)

omit [IsDomain R] [Algebra.FiniteType R S] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: a fixed coefficient subalgebra containing the relation
matrix coefficients supplies entrywise polynomial lifts over that same subalgebra. -/
lemma mvPolynomialFiniteFreeRelation_lift_entries_of_relationCoeff_mem_adjoin
    {n m r : ℕ}
    (rel : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R]
      (Fin m → MvPolynomial (Fin n) R))
    (coeffs : Finset R)
    (hcoeffs :
      ∀ (i : Fin r) (j : Fin m) (mon : Fin n →₀ ℕ),
        mon ∈ (rel (Pi.single i (1 : MvPolynomial (Fin n) R)) j).support →
        MvPolynomial.coeff mon (rel (Pi.single i (1 : MvPolynomial (Fin n) R)) j) ∈
          Algebra.adjoin ℤ (coeffs : Set R)) :
    ∃ lift : (i : Fin r) → (j : Fin m) →
        MvPolynomial (Fin n) (Algebra.adjoin ℤ (coeffs : Set R)),
      ∀ (i : Fin r) (j : Fin m),
        MvPolynomial.map (algebraMap (Algebra.adjoin ℤ (coeffs : Set R)) R)
            (lift i j) =
          rel (Pi.single i (1 : MvPolynomial (Fin n) R)) j := by
  classical
  have hlift_mem :
      ∀ (i : Fin r) (j : Fin m),
        rel (Pi.single i (1 : MvPolynomial (Fin n) R)) j ∈
          Set.range (MvPolynomial.map
            (algebraMap (Algebra.adjoin ℤ (coeffs : Set R)) R)) := by
    intro i j
    -- Proof comment: the coefficient-range criterion reduces descent of each entry to the
    -- supplied fixed-subring membership for every support coefficient.
    apply mvPolynomial_mem_range_map_of_coeffs_subset_subalgebra
    intro c hc
    have hc' : c ∈ (rel (Pi.single i (1 : MvPolynomial (Fin n) R)) j).coeffs := by
      simpa using hc
    rw [MvPolynomial.mem_coeffs_iff] at hc'
    obtain ⟨mon, hmon, rfl⟩ := hc'
    exact hcoeffs i j mon hmon
  let lift : (i : Fin r) → (j : Fin m) →
      MvPolynomial (Fin n) (Algebra.adjoin ℤ (coeffs : Set R)) :=
    fun i j ↦ Classical.choose (hlift_mem i j)
  refine ⟨lift, ?_⟩
  intro i j
  -- Proof comment: the chosen lift is the witness returned by the range criterion for this
  -- particular matrix entry.
  exact Classical.choose_spec (hlift_mem i j)

omit [IsDomain R] [Algebra.FiniteType R S] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: lifted relation matrix entries assemble into a finite-free
relation map whose base change recovers the original relation map. -/
lemma mvPolynomialFiniteFreeRelation_liftedLinearMap_baseChange
    {A : Type*} [CommRing A] [Algebra A R]
    {n m r : ℕ}
    (rel : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R]
      (Fin m → MvPolynomial (Fin n) R))
    (lift : (i : Fin r) → (j : Fin m) → MvPolynomial (Fin n) A)
    (hlift : ∀ (i : Fin r) (j : Fin m),
      MvPolynomial.map (algebraMap A R) (lift i j) =
        rel (Pi.single i (1 : MvPolynomial (Fin n) R)) j) :
    ∃ rel0 : (Fin r → MvPolynomial (Fin n) A) →ₗ[MvPolynomial (Fin n) A]
        (Fin m → MvPolynomial (Fin n) A),
      ∀ x j,
        MvPolynomial.map (algebraMap A R) (rel0 x j) =
          rel (fun i : Fin r => MvPolynomial.map (algebraMap A R) (x i)) j := by
  classical
  let P0 := MvPolynomial (Fin n) A
  let P := MvPolynomial (Fin n) R
  -- Proof comment: build the descended relation map from the lifted matrix columns.
  let rel0 : (Fin r → P0) →ₗ[P0] (Fin m → P0) :=
    { toFun := fun x j => ∑ i : Fin r, x i * lift i j
      map_add' := by
        intro x y
        funext j
        simp [Finset.sum_add_distrib, add_mul]
      map_smul' := by
        intro a x
        funext j
        simp only [Pi.smul_apply, Algebra.smul_def, RingHom.id_apply]
        rw [Finset.mul_sum]
        simp [mul_assoc] }
  refine ⟨rel0, ?_⟩
  intro x j
  let y : Fin r → P := fun i => MvPolynomial.map (algebraMap A R) (x i)
  have y_decomp : y = ∑ i : Fin r, y i • (Pi.single i (1 : P) : Fin r → P) := by
    -- Proof comment: finite free vectors are the sum of their coordinates times the standard
    -- basis vectors.
    funext k
    simp [y, Pi.single_apply]
  have hrelvec : rel y = ∑ i : Fin r, y i • rel (Pi.single i (1 : P)) := by
    -- Proof comment: apply linearity of the original relation map to the standard-basis
    -- expansion of the base-changed input vector.
    calc
      rel y = rel (∑ i : Fin r, y i • (Pi.single i (1 : P) : Fin r → P)) :=
        congrArg rel y_decomp
      _ = ∑ i : Fin r, y i • rel (Pi.single i (1 : P)) := by
        simp
  have hrelj : rel y j = ∑ i : Fin r, y i * rel (Pi.single i (1 : P)) j := by
    -- Proof comment: evaluating the vector equality at `j` exposes the usual matrix product.
    calc
      rel y j = (∑ i : Fin r, y i • rel (Pi.single i (1 : P))) j := by
        rw [hrelvec]
      _ = ∑ i : Fin r, y i * rel (Pi.single i (1 : P)) j := by
        simp [P, Algebra.smul_def, Algebra.algebraMap_self]
  -- Proof comment: mapping the descended matrix product to `R` gives the same matrix product as
  -- the original relation map, entry by entry.
  calc
    MvPolynomial.map (algebraMap A R) (rel0 x j)
        = ∑ i : Fin r, y i * rel (Pi.single i (1 : P)) j := by
          simp [rel0, y, hlift]
    _ = rel y j := hrelj.symm

omit [IsDomain R] [Algebra.FiniteType R S] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: the coefficients appearing in the finite relation
polynomials of a presentation lie in one finitely generated coefficient subalgebra. -/
lemma mvPolynomialPresentation_relationCoeff_mem_adjoin
    {n : ℕ} {N : Type w} [AddCommGroup N] [Module (MvPolynomial (Fin n) R) N]
    (pres : Module.Presentation (MvPolynomial (Fin n) R) N)
    [Finite pres.G] [Finite pres.R] :
    ∃ coeffs : Finset R,
      ∀ (r : pres.R) (g : pres.G) (m : Fin n →₀ ℕ),
        g ∈ (pres.relation r).support →
        m ∈ ((pres.relation r) g).support →
        MvPolynomial.coeff m ((pres.relation r) g) ∈ Algebra.adjoin ℤ (coeffs : Set R) := by
  classical
  letI : Fintype pres.R := Fintype.ofFinite pres.R
  let coeffs : Finset R :=
    Finset.univ.biUnion fun r : pres.R =>
      (pres.relation r).support.biUnion fun g : pres.G =>
        (((pres.relation r) g).support.image fun m : Fin n →₀ ℕ =>
          MvPolynomial.coeff m ((pres.relation r) g))
  refine ⟨coeffs, ?_⟩
  intro r g m hg hm
  -- Proof comment: by construction the chosen finite set contains every coefficient in every
  -- relation polynomial support, hence each such coefficient lies in its generated subalgebra.
  apply Algebra.subset_adjoin
  rw [Finset.mem_coe]
  dsimp [coeffs]
  rw [Finset.mem_biUnion]
  refine ⟨r, Finset.mem_univ r, ?_⟩
  rw [Finset.mem_biUnion]
  refine ⟨g, hg, ?_⟩
  exact Finset.mem_image.mpr ⟨m, hm, rfl⟩

omit [IsDomain R] [Algebra.FiniteType R S] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: a subalgebra generated by a finite coefficient set over
`ℤ` is Noetherian. -/
lemma adjoinFinset_isNoetherianRing (coeffs : Finset R) :
    IsNoetherianRing (Algebra.adjoin ℤ (coeffs : Set R)) := by
  -- Proof comment: finite generation over the Noetherian ring `ℤ` gives the Noetherian
  -- coefficient subring used by the source generic-freeness argument.
  have hft : Algebra.FiniteType ℤ (Algebra.adjoin ℤ (coeffs : Set R)) :=
    Algebra.FiniteType.adjoin_of_finite
      (show (coeffs : Set R).Finite from coeffs.finite_toSet)
  have hfg : (Algebra.adjoin ℤ (coeffs : Set R)).FG :=
    (Subalgebra.fg_iff_finiteType (Algebra.adjoin ℤ (coeffs : Set R))).2 hft
  exact isNoetherianRing_of_fg hfg

/-- Helper for Chap10 Lemma 10 118 3: a finite coefficient subalgebra of the ambient domain is
again a domain. -/
lemma adjoinFinset_isDomain (coeffs : Finset R) :
    IsDomain (Algebra.adjoin ℤ (coeffs : Set R)) := by
  -- Proof comment: the generated coefficient algebra is a subalgebra of `R`, so mathlib's
  -- inherited-domain instance applies directly.
  infer_instance

omit [IsDomain R] [Algebra.FiniteType R S] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: a nonzero element of a coefficient subalgebra remains
nonzero in the ambient domain. -/
lemma subalgebra_coe_ne_zero {A : Subalgebra ℤ R} {x : A} (hx : x ≠ 0) :
    (x : R) ≠ 0 := by
  -- Proof comment: the subalgebra inclusion is injective because subalgebra elements are
  -- subtypes of the ambient ring.
  intro h
  exact hx (Subtype.ext h)

end
