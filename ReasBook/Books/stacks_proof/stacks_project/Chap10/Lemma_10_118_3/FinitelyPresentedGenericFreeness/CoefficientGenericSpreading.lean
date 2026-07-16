import stacks_proof.stacks_project.Chap10.Lemma_10_118_3.FinitelyPresentedGenericFreeness.MonomialSpan
import stacks_proof.stacks_project.Chap10.Lemma_10_118_3.FinitelyPresentedGenericFreeness.PolynomialPresentationDescent
import stacks_proof.stacks_project.Chap10.Lemma_10_118_3.FinitelyPresentedGenericFreeness.CoefficientProductLocalization

universe u w

section

variable {R : Type u} [CommRing R] [IsDomain R]

open GenericFlatness

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Helper for Chap10 Lemma 10 118 3: a finitely presented polynomial module has a finite
presentation whose relation coefficients generate a Noetherian domain inside the base domain. -/
lemma exists_mvPolynomialPresentation_withNoetherianCoeffSubring
    {n : ℕ}
    {N : Type w} [AddCommGroup N] [Module (MvPolynomial (Fin n) R) N]
    (hfp : Module.FinitePresentation (MvPolynomial (Fin n) R) N) :
    ∃ pres : Module.Presentation.{w, w} (MvPolynomial (Fin n) R) N,
      Finite pres.G ∧ Finite pres.R ∧
        Function.Exact pres.toRelations.map pres.toSolution.π ∧
        Nonempty (pres.toRelations.Quotient ≃ₗ[MvPolynomial (Fin n) R] N) ∧
        ∃ coeffs : Finset R,
          (∀ (r : pres.R) (g : pres.G) (m : Fin n →₀ ℕ),
            g ∈ (pres.relation r).support →
            m ∈ ((pres.relation r) g).support →
            MvPolynomial.coeff m ((pres.relation r) g) ∈
              Algebra.adjoin ℤ (coeffs : Set R)) ∧
          IsNoetherianRing (Algebra.adjoin ℤ (coeffs : Set R)) ∧
          IsDomain (Algebra.adjoin ℤ (coeffs : Set R)) := by
  classical
  let _ : Module.FinitePresentation (MvPolynomial (Fin n) R) N := hfp
  -- Proof comment: first use the finite-presentation API to obtain a presentation with finitely
  -- many generators and relations, plus its quotient model.
  obtain ⟨pres, hG, hR, hExact, hquot⟩ :=
    mvPolynomialModule_finitePresentationData (R := R) (n := n) (N := N)
  letI : Finite pres.G := hG
  letI : Finite pres.R := hR
  -- Proof comment: collect the finitely many coefficients appearing in the relation polynomials
  -- and record the two structural properties of the generated coefficient subring.
  obtain ⟨coeffs, hcoeffs⟩ :=
    mvPolynomialPresentation_relationCoeff_mem_adjoin (R := R) (n := n) (N := N) pres
  refine ⟨pres, hG, hR, hExact, hquot, coeffs, hcoeffs, ?_, ?_⟩
  · exact adjoinFinset_isNoetherianRing (R := R) coeffs
  · exact adjoinFinset_isDomain (R := R) coeffs

/-- Helper for Chap10 Lemma 10 118 3: the finite-presentation data can be chosen as an explicit
finite-free relation quotient whose relation coefficients generate a Noetherian domain. -/
lemma exists_finiteFreeRelationQuotientPresentation_withNoetherianCoeffSubring
    {n : ℕ}
    {N : Type w} [AddCommGroup N] [Module (MvPolynomial (Fin n) R) N]
    (hfp : Module.FinitePresentation (MvPolynomial (Fin n) R) N) :
    ∃ (m r : ℕ)
      (rel : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R]
        (Fin m → MvPolynomial (Fin n) R))
      (K : Submodule (MvPolynomial (Fin n) R) (Fin m → MvPolynomial (Fin n) R)),
        Nonempty (N ≃ₗ[MvPolynomial (Fin n) R]
          (Fin m → MvPolynomial (Fin n) R) ⧸ K) ∧
        LinearMap.range rel = K ∧
        ∃ coeffs : Finset R,
          (∀ (i : Fin r) (j : Fin m) (mon : Fin n →₀ ℕ),
            mon ∈ (rel (Pi.single i (1 : MvPolynomial (Fin n) R)) j).support →
            MvPolynomial.coeff mon
                (rel (Pi.single i (1 : MvPolynomial (Fin n) R)) j) ∈
              Algebra.adjoin ℤ (coeffs : Set R)) ∧
          IsNoetherianRing (Algebra.adjoin ℤ (coeffs : Set R)) ∧
          IsDomain (Algebra.adjoin ℤ (coeffs : Set R)) := by
  classical
  let _ : Module.FinitePresentation (MvPolynomial (Fin n) R) N := hfp
  -- Proof comment: first replace the abstract finite-presentation object by a concrete quotient
  -- of a finite free polynomial module by finitely many finite-free relations.
  obtain ⟨m, r, rel, K, hquot, hrel⟩ :=
    mvPolynomialModule_finiteFreeQuotientPresentation (R := R) (n := n) (N := N)
  -- Proof comment: then collect the finitely many coefficients occurring in the relation matrix
  -- and record the Noetherian-domain properties of the generated coefficient subring.
  obtain ⟨coeffs, hcoeffs⟩ :=
    mvPolynomialFiniteFreeRelation_relationCoeff_mem_adjoin (R := R) (n := n) rel
  refine ⟨m, r, rel, K, hquot, hrel, coeffs, hcoeffs, ?_, ?_⟩
  · exact adjoinFinset_isNoetherianRing (R := R) coeffs
  · exact adjoinFinset_isDomain (R := R) coeffs

/-- Helper for Chap10 Lemma 10 118 3: a finite-free relation quotient over a polynomial ring is
finitely presented over that polynomial ring. -/
lemma finiteFreeRelationQuotient_mvPolynomial_finitePresentation
    {A : Type*} [CommRing A] {n m r : ℕ}
    (rel₀ : (Fin r → MvPolynomial (Fin n) A) →ₗ[MvPolynomial (Fin n) A]
      (Fin m → MvPolynomial (Fin n) A)) :
    Module.FinitePresentation (MvPolynomial (Fin n) A)
      ((Fin m → MvPolynomial (Fin n) A) ⧸ LinearMap.range rel₀) := by
  -- Proof comment: the relation quotient is exactly the standard finite-free presentation
  -- already isolated in the polynomial-presentation support file.
  exact finiteFreeRelationQuotient_finitePresentation rel₀

/-- Helper for Chap10 Lemma 10 118 3: the coefficient generic fiber of any descended finite-free
relation quotient is free over the coefficient fraction field. -/
lemma finiteFreeRelationQuotient_coeffGenericFiber_free
    {A : Type*} [CommRing A] [IsDomain A] {n m r : ℕ}
    (rel₀ : (Fin r → MvPolynomial (Fin n) A) →ₗ[MvPolynomial (Fin n) A]
      (Fin m → MvPolynomial (Fin n) A)) :
    let P := MvPolynomial (Fin n) A
    let T := Algebra.algebraMapSubmonoid P (nonZeroDivisors A)
    let K := Localization (nonZeroDivisors A)
    let PT := Localization T
    letI : Module K (LocalizedModule T
      ((Fin m → MvPolynomial (Fin n) A) ⧸ LinearMap.range rel₀)) :=
      Module.compHom (LocalizedModule T
        ((Fin m → MvPolynomial (Fin n) A) ⧸ LinearMap.range rel₀)) (algebraMap K PT)
    Module.Free K (LocalizedModule T
      ((Fin m → MvPolynomial (Fin n) A) ⧸ LinearMap.range rel₀)) := by
  -- Proof comment: after inverting every nonzero coefficient, the quotient is just a vector space
  -- over the coefficient fraction field, hence free by the existing generic-fiber helper.
  exact mvPolynomialModule_coeffGenericFiber_free (R := A) (n := n)
    (N := (Fin m → MvPolynomial (Fin n) A) ⧸ LinearMap.range rel₀)

/-- Helper for Chap10 Lemma 10 118 3: the descended relation quotient has the two
generic-freeness side conditions already available before the remaining coefficient-denominator
spreading step. -/
lemma descendedFiniteFreeRelationQuotient_finitePresentation_and_coeffGenericFiber_free
    {A : Type*} [CommRing A] [IsDomain A] {n m r : ℕ}
    (rel₀ : (Fin r → MvPolynomial (Fin n) A) →ₗ[MvPolynomial (Fin n) A]
      (Fin m → MvPolynomial (Fin n) A)) :
    let P₀ := MvPolynomial (Fin n) A
    let Q₀ := (Fin m → P₀) ⧸ LinearMap.range rel₀
    Module.FinitePresentation P₀ Q₀ ∧
      (let T := Algebra.algebraMapSubmonoid P₀ (nonZeroDivisors A)
       let K₀ := Localization (nonZeroDivisors A)
       let PT₀ := Localization T
       letI : Module K₀ (LocalizedModule T Q₀) :=
         Module.compHom (LocalizedModule T Q₀) (algebraMap K₀ PT₀)
       Module.Free K₀ (LocalizedModule T Q₀)) := by
  -- Proof comment: the first component is the closed finite-free quotient presentation theorem.
  refine ⟨finiteFreeRelationQuotient_mvPolynomial_finitePresentation rel₀, ?_⟩
  -- Proof comment: the second component is the coefficient generic-fiber freeness of the same
  -- descended quotient, recorded with the identical `P₀`/`Q₀` spelling used by the main frontier.
  exact finiteFreeRelationQuotient_coeffGenericFiber_free rel₀

/-- Helper for Chap10 Lemma 10 118 3: an ambient finite-free relation quotient presentation
supplies finite presentation and coefficient-generic-fiber freeness for the represented module. -/
lemma ambientFiniteFreeRelationQuotient_finitePresentation_and_coeffGenericFiber_free
    {n m r : ℕ}
    {N : Type w} [AddCommGroup N] [Module (MvPolynomial (Fin n) R) N]
    (rel : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R]
      (Fin m → MvPolynomial (Fin n) R))
    (K : Submodule (MvPolynomial (Fin n) R) (Fin m → MvPolynomial (Fin n) R))
    (hquot : Nonempty (N ≃ₗ[MvPolynomial (Fin n) R]
      (Fin m → MvPolynomial (Fin n) R) ⧸ K))
    (hrel : LinearMap.range rel = K) :
    Module.FinitePresentation (MvPolynomial (Fin n) R) N ∧
      (let P := MvPolynomial (Fin n) R
       let T := Algebra.algebraMapSubmonoid P (nonZeroDivisors R)
       let K₀ := Localization (nonZeroDivisors R)
       let PT := Localization T
       letI : Module K₀ (LocalizedModule T N) :=
         Module.compHom (LocalizedModule T N) (algebraMap K₀ PT)
       Module.Free K₀ (LocalizedModule T N)) := by
  subst K
  -- Proof comment: first rewrite the presented quotient so the kernel is exactly the range of
  -- the displayed relation map, which is the form expected by the finite-presentation API.
  have hquotRange : Nonempty (N ≃ₗ[MvPolynomial (Fin n) R]
      (Fin m → MvPolynomial (Fin n) R) ⧸ LinearMap.range rel) := by
    exact hquot
  refine ⟨finiteFreeRelationQuotientPresentation_finitePresentation rel hquotRange, ?_⟩
  -- Proof comment: after inverting all nonzero coefficients, the localized object is a vector
  -- space over the coefficient fraction field, hence free by the existing generic-fiber helper.
  exact mvPolynomialModule_coeffGenericFiber_free (R := R) (n := n) (N := N)

/-- Helper for Chap10 Lemma 10 118 3: an injective algebra map sends nonzero source
denominators to nonzero target denominators. -/
lemma algebraMap_ne_zero_of_injective
    {A B : Type*} [CommSemiring A] [Semiring B] [Algebra A B]
    (hinj : Function.Injective (algebraMap A B)) {a : A} (ha : a ≠ 0) :
    algebraMap A B a ≠ 0 := by
  -- Proof comment: rewrite target-zero as equality with the image of source-zero, then reflect
  -- it back across injectivity.
  intro hzero
  exact ha (hinj (by simpa using hzero))

/-- Helper for Chap10 Lemma 10 118 3: an ambient freeness statement whose denominator comes from
the descended coefficient ring gives the required nonzero denominator in the ambient domain. -/
lemma exists_coeffAway_free_of_mapped_descended_denominator
    {A : Type*} [CommRing A] [Algebra A R]
    {n : ℕ}
    {N : Type w} [AddCommGroup N] [Module (MvPolynomial (Fin n) R) N]
    (hAinj : Function.Injective (algebraMap A R))
    (hfree :
      ∃ a : A, a ≠ 0 ∧
        Module.Free (Localization.Away (algebraMap A R a))
          (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) (algebraMap A R a)) N)) :
    ∃ f : R, f ≠ 0 ∧
      Module.Free (Localization.Away f)
        (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N) := by
  -- Proof comment: choose the descended denominator and map it to the ambient domain.
  obtain ⟨a, ha, hfreea⟩ := hfree
  refine ⟨algebraMap A R a, algebraMap_ne_zero_of_injective hAinj ha, hfreea⟩
  -- Proof comment: injectivity of `A → R` carries nonzeroness of the descended denominator to
  -- nonzeroness of its ambient image.

omit [IsDomain R] in
/-- Helper for Chap10 Lemma 10 118 3: a linear equivalence localizes to a linear equivalence
between the corresponding localized modules. -/
lemma localizedModuleLinearEquiv_nonempty_of_linearEquiv
    {A : Type*} [CommRing A] (U : Submonoid A)
    {M : Type*} [AddCommGroup M] [Module A M]
    {N : Type*} [AddCommGroup N] [Module A N]
    (e : M ≃ₗ[A] N) :
    Nonempty (LocalizedModule U M ≃ₗ[Localization U] LocalizedModule U N) := by
  -- Proof comment: localize the forward and inverse maps, then extend their scalar linearity
  -- from the source ring to the localization.
  let forwardA : LocalizedModule U M →ₗ[A] LocalizedModule U N :=
    LocalizedModule.map U e.toLinearMap
  let backwardA : LocalizedModule U N →ₗ[A] LocalizedModule U M :=
    LocalizedModule.map U e.symm.toLinearMap
  refine ⟨LinearEquiv.ofLinear
    (forwardA.extendScalarsOfIsLocalization U (Localization U))
    (backwardA.extendScalarsOfIsLocalization U (Localization U)) ?_ ?_⟩
  · -- Proof comment: on localized numerators the two maps compose to the identity.
    ext x
    refine LocalizedModule.induction_on (x := x) ?_
    intro m s
    simp [forwardA, backwardA]
  · -- Proof comment: the same numerator calculation proves the inverse composition.
    ext y
    refine LocalizedModule.induction_on (x := y) ?_
    intro n s
    simp [forwardA, backwardA]

/-- Helper for Chap10 Lemma 10 118 3: a polynomial-linear equivalence localizes to an
`R_f`-linear equivalence after inverting the constant polynomial `C f`. -/
lemma coeffAwayLocalizedLinearEquiv_nonempty_of_linearEquiv
    {n : ℕ} (f : R)
    {N N' : Type*} [AddCommGroup N] [Module (MvPolynomial (Fin n) R) N]
    [AddCommGroup N'] [Module (MvPolynomial (Fin n) R) N']
    (e : N ≃ₗ[MvPolynomial (Fin n) R] N') :
    Nonempty (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N ≃ₗ[Localization.Away f]
      LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N') := by
  let U := Submonoid.powers (MvPolynomial.C (σ := Fin n) f)
  -- Proof comment: first localize the original polynomial-linear equivalence over
  -- `R[x]_(C f)`.
  obtain ⟨eloc⟩ := localizedModuleLinearEquiv_nonempty_of_linearEquiv U e
  refine ⟨{
      toFun := eloc
      invFun := eloc.symm
      left_inv := eloc.left_inv
      right_inv := eloc.right_inv
      map_add' := eloc.map_add
      map_smul' := ?_ }⟩
  intro r x
  -- Proof comment: the restricted `R_f`-action is the direct away-map action, so `eloc`'s
  -- polynomial-localized linearity is enough.
  rw [away_polynomial_source_smul_eq_awayMap (R := R) (n := n) (N := N) f r x]
  rw [map_smul]
  exact (away_polynomial_source_smul_eq_awayMap
    (R := R) (n := n) (N := N') f r (eloc x)).symm

/-- Helper for Chap10 Lemma 10 118 3: coefficient-away freeness transports across an already
localized linear equivalence. -/
lemma coeffAway_free_of_localizedLinearEquiv
    {n : ℕ} (f : R)
    {N N' : Type*} [AddCommGroup N] [Module (MvPolynomial (Fin n) R) N]
    [AddCommGroup N'] [Module (MvPolynomial (Fin n) R) N']
    (e : LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N ≃ₗ[Localization.Away f]
      LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N')
    [Module.Free (Localization.Away f)
      (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N)] :
    Module.Free (Localization.Away f)
      (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N') := by
  -- Proof comment: once the quotient/base-change comparison is expressed as a localized linear
  -- equivalence, freeness moves across it by the standard basis-transport API.
  exact Module.Free.of_equiv'
    (inferInstance : Module.Free (Localization.Away f)
      (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N)) e

/-- Helper for Chap10 Lemma 10 118 3: coefficient-away freeness is preserved by a
polynomial-linear equivalence before localization. -/
lemma coeffAway_free_of_linearEquiv
    {n : ℕ} (f : R)
    {N N' : Type*} [AddCommGroup N] [Module (MvPolynomial (Fin n) R) N]
    [AddCommGroup N'] [Module (MvPolynomial (Fin n) R) N']
    (e : N ≃ₗ[MvPolynomial (Fin n) R] N')
    [Module.Free (Localization.Away f)
      (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N)] :
    Module.Free (Localization.Away f)
      (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N') := by
  -- Proof comment: turn the localized equivalence into an `R_f`-linear equivalence, then
  -- transport the chosen basis across it.
  obtain ⟨eloc⟩ := coeffAwayLocalizedLinearEquiv_nonempty_of_linearEquiv
    (R := R) (n := n) f e
  exact Module.Free.of_equiv'
    (inferInstance : Module.Free (Localization.Away f)
      (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N)) eloc

omit [IsDomain R] in
/-- Helper for Chap10 Lemma 10 118 3: an ambient quotient model identifies the quotient by the
displayed relation range with the represented module. -/
lemma ambientRelationQuotient_linearEquiv_nonempty
    {n m r : ℕ}
    {N : Type w} [AddCommGroup N] [Module (MvPolynomial (Fin n) R) N]
    (rel : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R]
      (Fin m → MvPolynomial (Fin n) R))
    (K : Submodule (MvPolynomial (Fin n) R) (Fin m → MvPolynomial (Fin n) R))
    (hquot : Nonempty (N ≃ₗ[MvPolynomial (Fin n) R]
      (Fin m → MvPolynomial (Fin n) R) ⧸ K))
    (hrel : LinearMap.range rel = K) :
    Nonempty (((Fin m → MvPolynomial (Fin n) R) ⧸ LinearMap.range rel) ≃ₗ[
      MvPolynomial (Fin n) R] N) := by
  -- Proof comment: first choose the supplied quotient model for `N`.
  obtain ⟨equot⟩ := hquot
  -- Proof comment: rewrite the quotient kernel from `K` to the displayed range and invert the
  -- chosen equivalence so the source is the ambient range quotient.
  exact ⟨Submodule.quotEquivOfEq _ _ hrel ≪≫ₗ equot.symm⟩

/-- Helper for Chap10 Lemma 10 118 3: freeness of the localized ambient relation quotient
transports to the represented module using the quotient model. -/
lemma coeffAway_free_of_ambientRelationQuotient
    {n m r : ℕ} (f : R)
    {N : Type w} [AddCommGroup N] [Module (MvPolynomial (Fin n) R) N]
    (rel : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R]
      (Fin m → MvPolynomial (Fin n) R))
    (K : Submodule (MvPolynomial (Fin n) R) (Fin m → MvPolynomial (Fin n) R))
    (hquot : Nonempty (N ≃ₗ[MvPolynomial (Fin n) R]
      (Fin m → MvPolynomial (Fin n) R) ⧸ K))
    (hrel : LinearMap.range rel = K)
    [Module.Free (Localization.Away f)
      (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f)
        ((Fin m → MvPolynomial (Fin n) R) ⧸ LinearMap.range rel))] :
    Module.Free (Localization.Away f)
      (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N) := by
  -- Proof comment: normalize the quotient kernel to `range rel`, then invert the provided
  -- quotient model for `N`.
  obtain ⟨eRange⟩ :=
    ambientRelationQuotient_linearEquiv_nonempty
      (R := R) (n := n) (m := m) (r := r) rel K hquot hrel
  -- Proof comment: the coefficient-away freeness now moves across this polynomial-linear
  -- equivalence by the localization transport lemma above.
  exact coeffAway_free_of_linearEquiv (R := R) (n := n) f eRange

/-- Helper for Chap10 Lemma 10 118 3: freeness of the descended ambient range quotient at a
mapped coefficient denominator transports to the represented module. -/
lemma coeffAway_free_of_descendedRangeQuotient
    {A : Type*} [CommRing A] [Algebra A R]
    {n m r : ℕ} (a : A)
    {N : Type w} [AddCommGroup N] [Module (MvPolynomial (Fin n) R) N]
    (rel : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R]
      (Fin m → MvPolynomial (Fin n) R))
    (K : Submodule (MvPolynomial (Fin n) R) (Fin m → MvPolynomial (Fin n) R))
    (hquot : Nonempty (N ≃ₗ[MvPolynomial (Fin n) R]
      (Fin m → MvPolynomial (Fin n) R) ⧸ K))
    (hrel : LinearMap.range rel = K)
    (hfreeRange :
      Module.Free (Localization.Away (algebraMap A R a))
        (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) (algebraMap A R a))
          ((Fin m → MvPolynomial (Fin n) R) ⧸ LinearMap.range rel))) :
    Module.Free (Localization.Away (algebraMap A R a))
      (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) (algebraMap A R a)) N) := by
  -- Proof comment: install the already chosen free basis on the ambient range quotient.
  letI : Module.Free (Localization.Away (algebraMap A R a))
      (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) (algebraMap A R a))
        ((Fin m → MvPolynomial (Fin n) R) ⧸ LinearMap.range rel)) := hfreeRange
  -- Proof comment: the existing quotient-model transport then moves the basis across `hrel` and
  -- the displayed quotient equivalence for `N`.
  exact coeffAway_free_of_ambientRelationQuotient
    (R := R) (n := n) (m := m) (r := r) (algebraMap A R a) rel K hquot hrel

/-- Helper for Chap10 Lemma 10 118 3: once the coefficient-spreading theorem is available over
a Noetherian domain, it gives the same-base finite-free relation quotient case. -/
lemma finiteFreeRelationQuotient_coeffAway_free_sameBase_of_spreading
    {A : Type u} [CommRing A] [IsDomain A]
    (hspread :
      ∀ {n : ℕ}
        {N : Type u} [AddCommGroup N] [Module (MvPolynomial (Fin n) A) N],
        Module.FinitePresentation (MvPolynomial (Fin n) A) N →
        (let P := MvPolynomial (Fin n) A
         let T := Algebra.algebraMapSubmonoid P (nonZeroDivisors A)
         let K := Localization (nonZeroDivisors A)
         let PT := Localization T
         letI : Module K (LocalizedModule T N) :=
           Module.compHom (LocalizedModule T N) (algebraMap K PT)
         Module.Free K (LocalizedModule T N)) →
        ∃ a : A, a ≠ 0 ∧
          Module.Free (Localization.Away a)
            (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) a) N))
    {n m r : ℕ}
    (rel₀ : (Fin r → MvPolynomial (Fin n) A) →ₗ[MvPolynomial (Fin n) A]
      (Fin m → MvPolynomial (Fin n) A)) :
    ∃ a : A, a ≠ 0 ∧
      Module.Free (Localization.Away a)
        (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) a)
          ((Fin m → MvPolynomial (Fin n) A) ⧸ LinearMap.range rel₀)) := by
  -- Proof comment: the descended quotient already has finite presentation and coefficient
  -- generic-fiber freeness, so the same-base theorem is exactly the spreading input applied to it.
  obtain ⟨hfp, hgeneric⟩ :=
    descendedFiniteFreeRelationQuotient_finitePresentation_and_coeffGenericFiber_free rel₀
  exact hspread (n := n)
    (N := (Fin m → MvPolynomial (Fin n) A) ⧸ LinearMap.range rel₀) hfp hgeneric

/-- Helper for Chap10 Lemma 10 118 3: a coefficient-spreading theorem can be consumed directly
from the finite-presentation and coefficient-generic-fiber side conditions of a descended
relation quotient. -/
lemma finiteFreeRelationQuotient_coeffAway_free_sameBase_of_sideConditions
    {A : Type u} [CommRing A] [IsDomain A]
    (hspread :
      ∀ {n : ℕ}
        {N : Type u} [AddCommGroup N] [Module (MvPolynomial (Fin n) A) N],
        Module.FinitePresentation (MvPolynomial (Fin n) A) N →
        (let P := MvPolynomial (Fin n) A
         let T := Algebra.algebraMapSubmonoid P (nonZeroDivisors A)
         let K := Localization (nonZeroDivisors A)
         let PT := Localization T
         letI : Module K (LocalizedModule T N) :=
           Module.compHom (LocalizedModule T N) (algebraMap K PT)
         Module.Free K (LocalizedModule T N)) →
        ∃ a : A, a ≠ 0 ∧
          Module.Free (Localization.Away a)
            (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) a) N))
    {n m r : ℕ}
    (rel₀ : (Fin r → MvPolynomial (Fin n) A) →ₗ[MvPolynomial (Fin n) A]
      (Fin m → MvPolynomial (Fin n) A))
    (hfp :
      Module.FinitePresentation (MvPolynomial (Fin n) A)
        ((Fin m → MvPolynomial (Fin n) A) ⧸ LinearMap.range rel₀))
    (hgeneric :
      let P := MvPolynomial (Fin n) A
      let T := Algebra.algebraMapSubmonoid P (nonZeroDivisors A)
      let K := Localization (nonZeroDivisors A)
      let PT := Localization T
      letI : Module K (LocalizedModule T
        ((Fin m → MvPolynomial (Fin n) A) ⧸ LinearMap.range rel₀)) :=
        Module.compHom (LocalizedModule T
          ((Fin m → MvPolynomial (Fin n) A) ⧸ LinearMap.range rel₀)) (algebraMap K PT)
      Module.Free K (LocalizedModule T
        ((Fin m → MvPolynomial (Fin n) A) ⧸ LinearMap.range rel₀))) :
    ∃ a : A, a ≠ 0 ∧
      Module.Free (Localization.Away a)
        (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) a)
          ((Fin m → MvPolynomial (Fin n) A) ⧸ LinearMap.range rel₀)) := by
  -- Proof comment: this adapter avoids recomputing the quotient side conditions when the
  -- frontier has already isolated them as explicit hypotheses.
  exact hspread hfp hgeneric

/-- Helper for Chap10 Lemma 10 118 3: mapped nonzero coefficients remain non-zero-divisors in
the ambient polynomial ring. -/
lemma coeffSubmonoid_le_nonZeroDivisors_mvPolynomial
    {A : Type*} [CommRing A] [IsDomain A] [Algebra A R]
    (hAinj : Function.Injective (algebraMap A R)) (n : ℕ) :
    Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) (nonZeroDivisors A) ≤
      nonZeroDivisors (MvPolynomial (Fin n) R) := by
  let P := MvPolynomial (Fin n) R
  -- Proof comment: the coefficient map into `R[x]` is injective because it factors through the
  -- injective map `A → R` followed by the injective constant-polynomial map.
  have hinj : Function.Injective (algebraMap A P) := by
    intro x y hxy
    have hC :
        MvPolynomial.C (σ := Fin n) (algebraMap A R x) =
          MvPolynomial.C (σ := Fin n) (algebraMap A R y) := by
      simpa [P, MvPolynomial.algebraMap_eq] using hxy
    exact hAinj (MvPolynomial.C_injective (σ := Fin n) (R := R) hC)
  -- Proof comment: injective homomorphisms into a domain carry non-zero-divisors to
  -- non-zero-divisors, which is exactly the mapped coefficient submonoid side condition.
  exact map_le_nonZeroDivisors_of_injective (algebraMap A P) hinj le_rfl

/-- Helper for Chap10 Lemma 10 118 3: membership in the mapped coefficient submonoid is exactly
the data of a nonzero coefficient denominator from the source domain. -/
lemma exists_coeff_of_mem_coeffSubmonoid
    {A : Type*} [CommRing A] [IsDomain A] [Algebra A R]
    {n : ℕ} {p : MvPolynomial (Fin n) R}
    (hp : p ∈ Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) (nonZeroDivisors A)) :
    ∃ a : A, a ≠ 0 ∧ p = MvPolynomial.C (σ := Fin n) (algebraMap A R a) := by
  -- Proof comment: unpack the mapped-submonoid witness and convert non-zero-divisor membership
  -- in a domain to nonzeroness of the chosen coefficient.
  rcases hp with ⟨a, ha, hp⟩
  refine ⟨a, mem_nonZeroDivisors_iff_ne_zero.mp ha, ?_⟩
  -- Proof comment: the algebra map from `A` to `R[x]` is the constant-polynomial map after
  -- applying the coefficient map `A → R`.
  simpa [MvPolynomial.algebraMap_eq] using hp.symm

/-- Helper for Chap10 Lemma 10 118 3: polynomial-away freeness at a constant polynomial can be
viewed as coefficient-away freeness at the underlying coefficient. -/
lemma coeffAway_free_of_polynomialAway_free
    {n : ℕ}
    {N : Type*} [AddCommGroup N] [Module (MvPolynomial (Fin n) R) N]
    (f : R)
    [Module.Free (Localization.Away (MvPolynomial.C (σ := Fin n) f))
      (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N)] :
    Module.Free (Localization.Away f)
      (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N) := by
  -- Proof comment: this is the coefficient-product localization bridge under the shorter
  -- support-file name used by the generic-spreading proof plan.
  exact coeffAwayFreeOfPolynomialAwayFree (R := R) (n := n) (N := N) f

omit [IsDomain R] in
/-- Helper for Chap10 Lemma 10 118 3: a coefficientwise image of a descended relation is an
ambient relation. -/
lemma liftedRelation_mem_ambientRange
    {A : Type*} [CommRing A] [Algebra A R]
    {n m r : ℕ}
    (rel : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R]
      (Fin m → MvPolynomial (Fin n) R))
    (rel₀ : (Fin r → MvPolynomial (Fin n) A) →ₗ[MvPolynomial (Fin n) A]
      (Fin m → MvPolynomial (Fin n) A))
    (hrel₀_baseChange : ∀ x j,
      MvPolynomial.map (algebraMap A R) (rel₀ x j) =
        rel (fun i : Fin r => MvPolynomial.map (algebraMap A R) (x i)) j)
    (x : Fin r → MvPolynomial (Fin n) A) :
    (fun j : Fin m => MvPolynomial.map (algebraMap A R) (rel₀ x j)) ∈
      LinearMap.range rel := by
  -- Proof comment: the ambient witness is obtained by applying the coefficient map to the
  -- source vector of relation coefficients.
  refine ⟨fun i : Fin r => MvPolynomial.map (algebraMap A R) (x i), ?_⟩
  funext j
  exact (hrel₀_baseChange x j).symm

omit [IsDomain R] in
/-- Helper for Chap10 Lemma 10 118 3: the coordinatewise coefficient map sends the descended
relation range into the ambient relation range. -/
lemma liftedRelation_range_le_ambientRange
    {A : Type*} [CommRing A] [Algebra A R]
    {n m r : ℕ}
    (rel : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R]
      (Fin m → MvPolynomial (Fin n) R))
    (rel₀ : (Fin r → MvPolynomial (Fin n) A) →ₗ[MvPolynomial (Fin n) A]
      (Fin m → MvPolynomial (Fin n) A))
    (hrel₀_baseChange : ∀ x j,
      MvPolynomial.map (algebraMap A R) (rel₀ x j) =
        rel (fun i : Fin r => MvPolynomial.map (algebraMap A R) (x i)) j) :
    let coeffMap : MvPolynomial (Fin n) A →+* MvPolynomial (Fin n) R :=
      MvPolynomial.map (algebraMap A R)
    let mapVec : (Fin m → MvPolynomial (Fin n) A) →ₛₗ[coeffMap]
        (Fin m → MvPolynomial (Fin n) R) :=
      { toFun := fun v j => coeffMap (v j)
        map_add' := by
          intro x y
          funext j
          simp
        map_smul' := by
          intro p x
          funext j
          simp [Pi.smul_apply, smul_eq_mul, map_mul] }
    LinearMap.range rel₀ ≤ Submodule.comap mapVec (LinearMap.range rel) := by
  -- Proof comment: a vector in the descended range is `rel₀ x`; map it coefficientwise and use
  -- the supplied base-change identity to exhibit the corresponding ambient relation witness.
  dsimp only
  intro y hy
  rcases hy with ⟨x, rfl⟩
  exact liftedRelation_mem_ambientRange
    (R := R) (A := A) (n := n) (m := m) (r := r) rel rel₀ hrel₀_baseChange x

omit [IsDomain R] in
/-- Helper for Chap10 Lemma 10 118 3: the quotient map induced by the coefficientwise lift sends
a descended quotient class to the corresponding ambient quotient class. -/
lemma liftedRelation_quotientMap_mk
    {A : Type*} [CommRing A] [Algebra A R]
    {n m r : ℕ}
    (rel : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R]
      (Fin m → MvPolynomial (Fin n) R))
    (rel₀ : (Fin r → MvPolynomial (Fin n) A) →ₗ[MvPolynomial (Fin n) A]
      (Fin m → MvPolynomial (Fin n) A))
    (hrel₀_baseChange : ∀ x j,
      MvPolynomial.map (algebraMap A R) (rel₀ x j) =
        rel (fun i : Fin r => MvPolynomial.map (algebraMap A R) (x i)) j)
    (y : Fin m → MvPolynomial (Fin n) A) :
    let coeffMap : MvPolynomial (Fin n) A →+* MvPolynomial (Fin n) R :=
      MvPolynomial.map (algebraMap A R)
    let mapVec : (Fin m → MvPolynomial (Fin n) A) →ₛₗ[coeffMap]
        (Fin m → MvPolynomial (Fin n) R) :=
      { toFun := fun v j => coeffMap (v j)
        map_add' := by
          intro x y
          funext j
          simp
        map_smul' := by
          intro p x
          funext j
          simp [Pi.smul_apply, smul_eq_mul, map_mul] }
    Submodule.mapQ (LinearMap.range rel₀) (LinearMap.range rel) mapVec
        (liftedRelation_range_le_ambientRange
          (R := R) (A := A) (n := n) (m := m) (r := r) rel rel₀ hrel₀_baseChange)
        (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (mapVec y) := by
  -- Proof comment: after the range-inclusion helper supplies well-definedness, `mapQ` computes
  -- definitionally on quotient generators.
  dsimp only
  rfl

/-- Helper for Chap10 Lemma 10 118 3: the remaining source-generic-freeness and
fixed-denominator quotient/base-change input for a descended relation range quotient. -/
lemma exists_coeffAway_free_of_descendedRangeQuotient_from_genericFiber
    {A : Type*} [CommRing A] [Algebra A R] [IsNoetherianRing A] [IsDomain A]
    {n m r : ℕ}
    (rel : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R]
      (Fin m → MvPolynomial (Fin n) R))
    (rel₀ : (Fin r → MvPolynomial (Fin n) A) →ₗ[MvPolynomial (Fin n) A]
      (Fin m → MvPolynomial (Fin n) A))
    (hAinj : Function.Injective (algebraMap A R))
    (hrel₀_baseChange : ∀ x j,
      MvPolynomial.map (algebraMap A R) (rel₀ x j) =
        rel (fun i : Fin r => MvPolynomial.map (algebraMap A R) (x i)) j)
    (hfp₀ : Module.FinitePresentation (MvPolynomial (Fin n) A)
      ((Fin m → MvPolynomial (Fin n) A) ⧸ LinearMap.range rel₀))
    (hgeneric₀ :
      let P₀ := MvPolynomial (Fin n) A
      let Q₀ := (Fin m → P₀) ⧸ LinearMap.range rel₀
      let T := Algebra.algebraMapSubmonoid P₀ (nonZeroDivisors A)
      let K₀ := Localization (nonZeroDivisors A)
      let PT₀ := Localization T
      letI : Module K₀ (LocalizedModule T Q₀) :=
        Module.compHom (LocalizedModule T Q₀) (algebraMap K₀ PT₀)
      Module.Free K₀ (LocalizedModule T Q₀)) :
    ∃ a : A, a ≠ 0 ∧
      Module.Free (Localization.Away (algebraMap A R a))
        (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) (algebraMap A R a))
          ((Fin m → MvPolynomial (Fin n) R) ⧸ LinearMap.range rel)) := by
  -- Proof comment: this is the stabilized frontier.  It must first choose a coefficient
  -- denominator from the same-base source generic-freeness theorem for the descended quotient,
  -- then transport freeness across the fixed-denominator localized quotient/base-change
  -- equivalence induced by `hrel₀_baseChange`.
  -- TODO: prove the same-base coefficient generic-freeness theorem for the descended quotient
  -- and the fixed-denominator localized quotient/base-change equivalence to the ambient range
  -- quotient.
  sorry

/-- Helper for Chap10 Lemma 10 118 3: the source coefficient denominator for a descended
finite-free relation quotient also gives freeness of the mapped ambient range quotient. -/
lemma exists_coeffAway_free_of_descendedRangeQuotient
    {A : Type*} [CommRing A] [Algebra A R] [IsNoetherianRing A] [IsDomain A]
    {n m r : ℕ}
    (rel : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R]
      (Fin m → MvPolynomial (Fin n) R))
    (rel₀ : (Fin r → MvPolynomial (Fin n) A) →ₗ[MvPolynomial (Fin n) A]
      (Fin m → MvPolynomial (Fin n) A))
    (hAinj : Function.Injective (algebraMap A R))
    (hrel₀_baseChange : ∀ x j,
      MvPolynomial.map (algebraMap A R) (rel₀ x j) =
        rel (fun i : Fin r => MvPolynomial.map (algebraMap A R) (x i)) j) :
    ∃ a : A, a ≠ 0 ∧
      Module.Free (Localization.Away (algebraMap A R a))
        (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) (algebraMap A R a))
          ((Fin m → MvPolynomial (Fin n) R) ⧸ LinearMap.range rel)) := by
  classical
  let P₀ := MvPolynomial (Fin n) A
  let Q₀ := (Fin m → P₀) ⧸ LinearMap.range rel₀
  -- Proof comment: record the verified same-base finite-presentation and generic-fiber facts for
  -- the descended quotient before the remaining coefficient-denominator spreading step.
  have hside :
      Module.FinitePresentation P₀ Q₀ ∧
        (let T := Algebra.algebraMapSubmonoid P₀ (nonZeroDivisors A)
         let K₀ := Localization (nonZeroDivisors A)
         let PT₀ := Localization T
         letI : Module K₀ (LocalizedModule T Q₀) :=
           Module.compHom (LocalizedModule T Q₀) (algebraMap K₀ PT₀)
         Module.Free K₀ (LocalizedModule T Q₀)) :=
    descendedFiniteFreeRelationQuotient_finitePresentation_and_coeffGenericFiber_free rel₀
  have hfp₀ : Module.FinitePresentation P₀ Q₀ := hside.1
  have hgeneric₀ :
      let T := Algebra.algebraMapSubmonoid P₀ (nonZeroDivisors A)
      let K₀ := Localization (nonZeroDivisors A)
      let PT₀ := Localization T
      letI : Module K₀ (LocalizedModule T Q₀) :=
        Module.compHom (LocalizedModule T Q₀) (algebraMap K₀ PT₀)
      Module.Free K₀ (LocalizedModule T Q₀) := hside.2
  -- Proof comment: delegate the now-isolated source theorem plus fixed-denominator transport
  -- step, keeping this public range-quotient theorem as the clean assembly point.
  exact exists_coeffAway_free_of_descendedRangeQuotient_from_genericFiber
    (R := R) (A := A) (n := n) (m := m) (r := r)
    rel rel₀ hAinj hrel₀_baseChange hfp₀ hgeneric₀

/-- Helper for Chap10 Lemma 10 118 3: a finite-free relation quotient descended to a
Noetherian coefficient subdomain spreads out to a coefficient-away free module over the ambient
domain. -/
theorem exists_coeffAway_free_of_descendedFiniteFreeRelationQuotient
    {A : Type*} [CommRing A] [Algebra A R] [IsNoetherianRing A] [IsDomain A]
    {n m r : ℕ}
    {N : Type w} [AddCommGroup N] [Module (MvPolynomial (Fin n) R) N]
    (rel : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R]
      (Fin m → MvPolynomial (Fin n) R))
    (rel₀ : (Fin r → MvPolynomial (Fin n) A) →ₗ[MvPolynomial (Fin n) A]
      (Fin m → MvPolynomial (Fin n) A))
    (hAinj : Function.Injective (algebraMap A R))
    (K : Submodule (MvPolynomial (Fin n) R) (Fin m → MvPolynomial (Fin n) R))
    (hquot : Nonempty (N ≃ₗ[MvPolynomial (Fin n) R]
      (Fin m → MvPolynomial (Fin n) R) ⧸ K))
    (hrel : LinearMap.range rel = K)
    (hrel₀_baseChange : ∀ x j,
      MvPolynomial.map (algebraMap A R) (rel₀ x j) =
        rel (fun i : Fin r => MvPolynomial.map (algebraMap A R) (x i)) j) :
    ∃ f : R, f ≠ 0 ∧
      Module.Free (Localization.Away f)
        (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N) := by
  classical
  -- Proof comment: first isolate the only remaining source step: choosing a denominator in the
  -- descended coefficient ring and transporting the localized relation quotient to `R`.
  refine exists_coeffAway_free_of_mapped_descended_denominator
    (R := R) (A := A) (n := n) (N := N) hAinj ?_
  have hfreeQuot :=
    exists_coeffAway_free_of_descendedRangeQuotient
      (R := R) (A := A) (n := n) (m := m) (r := r) rel rel₀ hAinj hrel₀_baseChange
  obtain ⟨a, ha, hfreeRange⟩ := hfreeQuot
  refine ⟨a, ha, ?_⟩
  -- Proof comment: once the localized ambient range quotient is free, the quotient model for `N`
  -- supplies the final transport.
  exact coeffAway_free_of_descendedRangeQuotient
    (R := R) (A := A) (n := n) (m := m) (r := r) a rel K hquot hrel hfreeRange

/-- Helper for Chap10 Lemma 10 118 3: coefficient-generic-fiber freeness of a finitely presented
polynomial module spreads out after inverting one nonzero coefficient. -/
theorem exists_coeffAway_free_of_finitelyPresented_mvPolynomialModule_of_coeffGenericFiber_free
    {n : ℕ}
    {N : Type w} [AddCommGroup N] [Module (MvPolynomial (Fin n) R) N]
    (hfp : Module.FinitePresentation (MvPolynomial (Fin n) R) N)
    (_hgeneric :
      let P := MvPolynomial (Fin n) R
      let T := Algebra.algebraMapSubmonoid P (nonZeroDivisors R)
      let K := Localization (nonZeroDivisors R)
      let PT := Localization T
      letI : Module K (LocalizedModule T N) :=
        Module.compHom (LocalizedModule T N) (algebraMap K PT)
      Module.Free K (LocalizedModule T N)) :
    ∃ f : R, f ≠ 0 ∧
      Module.Free (Localization.Away f)
        (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N) := by
  classical
  let _ : Module.FinitePresentation (MvPolynomial (Fin n) R) N := hfp
  -- Route correction: the source proof of Stacks 051S does not proceed from an arbitrary
  -- polynomial-away denominator.  It first chooses a finite polynomial presentation, gathers the
  -- finitely many coefficients occurring in the relations, and descends to the generated
  -- Noetherian coefficient subring.
  obtain ⟨m, r, rel, K, hquot, hrel, coeffs, hcoeffs,
      hcoeffRingNoetherian, hcoeffRingDomain⟩ :=
    exists_finiteFreeRelationQuotientPresentation_withNoetherianCoeffSubring
      (R := R) (n := n) (N := N) hfp
  let A₀ := Algebra.adjoin ℤ (coeffs : Set R)
  -- Proof comment: descend the actual relation matrix to the fixed Noetherian coefficient
  -- subring chosen above; this pins the next source step to a concrete `A₀[x]` relation map.
  obtain ⟨lift, hlift⟩ :=
    mvPolynomialFiniteFreeRelation_lift_entries_of_relationCoeff_mem_adjoin
      (R := R) (n := n) rel coeffs hcoeffs
  obtain ⟨rel₀, hrel₀_baseChange⟩ :=
    mvPolynomialFiniteFreeRelation_liftedLinearMap_baseChange
      (R := R) (A := A₀) (n := n) (m := m) (r := r) rel lift hlift
  -- Proof comment: install the structural facts for the coefficient subring and delegate exactly
  -- the remaining source theorem: generic freeness for the descended finite-free quotient and its
  -- transport back to the ambient polynomial module.
  letI : IsNoetherianRing A₀ := hcoeffRingNoetherian
  letI : IsDomain A₀ := hcoeffRingDomain
  exact exists_coeffAway_free_of_descendedFiniteFreeRelationQuotient
    (R := R) (A := A₀) (n := n) (m := m) (r := r) (N := N)
    rel rel₀ (fun _ _ h => Subtype.ext h) K hquot hrel hrel₀_baseChange

end
