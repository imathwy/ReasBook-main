import stacks_proof.stacks_project.Chap10.Lemma_10_118_3.FinitelyPresentedGenericFreeness.Index

universe u v w

section

variable {R : Type u} [CommRing R] [IsDomain R]
variable {S : Type v} [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
variable {M : Type w} [AddCommGroup M] [Module S M] [Module.Finite S M]

open GenericFlatness

attribute [local instance] MvPolynomial.algebraMvPolynomial

omit [Algebra.FiniteType R S] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: a finite-free relation quotient presentation supplies
both finite presentation and automatic coefficient-generic-fiber freeness. -/
theorem finiteFreeRelationQuotientPresentation_finitePresentation_and_coeffGenericFiber_free
    {n m r : ℕ}
    {N : Type w} [AddCommGroup N] [Module (MvPolynomial (Fin n) R) N]
    (rel : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R]
      (Fin m → MvPolynomial (Fin n) R))
    (_e : Nonempty (N ≃ₗ[MvPolynomial (Fin n) R]
      (Fin m → MvPolynomial (Fin n) R) ⧸ LinearMap.range rel)) :
    Module.FinitePresentation (MvPolynomial (Fin n) R) N ∧
      (let P := MvPolynomial (Fin n) R
       let T := Algebra.algebraMapSubmonoid P (nonZeroDivisors R)
       let K := Localization (nonZeroDivisors R)
       let PT := Localization T
       letI : Module K (LocalizedModule T N) :=
         Module.compHom (LocalizedModule T N) (algebraMap K PT)
       Module.Free K (LocalizedModule T N)) := by
  -- Proof comment: the quotient presentation gives finite presentation through the closed
  -- presentation-descent helper.
  refine ⟨finiteFreeRelationQuotientPresentation_finitePresentation rel _e, ?_⟩
  -- Proof comment: over the coefficient generic fiber, these finite-variable polynomial modules
  -- are free by the existing monomial-span support theorem.
  exact mvPolynomialModule_coeffGenericFiber_free (R := R) (n := n) (N := N)

omit [Algebra.FiniteType R S] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: a coefficient-spreading theorem for finitely presented
polynomial modules immediately proves the finite-free relation quotient presentation case. -/
theorem finiteFreeRelationQuotientPresentation_coeffAway_free_of_spreading
    (hspread :
      ∀ {n : ℕ}
        {N : Type w} [AddCommGroup N] [Module (MvPolynomial (Fin n) R) N],
        Module.FinitePresentation (MvPolynomial (Fin n) R) N →
        (let P := MvPolynomial (Fin n) R
         let T := Algebra.algebraMapSubmonoid P (nonZeroDivisors R)
         let K := Localization (nonZeroDivisors R)
         let PT := Localization T
         letI : Module K (LocalizedModule T N) :=
           Module.compHom (LocalizedModule T N) (algebraMap K PT)
         Module.Free K (LocalizedModule T N)) →
        ∃ f : R, f ≠ 0 ∧
          Module.Free (Localization.Away f)
            (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N))
    {n m r : ℕ}
    {N : Type w} [AddCommGroup N] [Module (MvPolynomial (Fin n) R) N]
    (rel : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R]
      (Fin m → MvPolynomial (Fin n) R))
    (_e : Nonempty (N ≃ₗ[MvPolynomial (Fin n) R]
      (Fin m → MvPolynomial (Fin n) R) ⧸ LinearMap.range rel)) :
    ∃ f : R, f ≠ 0 ∧
      Module.Free (Localization.Away f)
        (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N) := by
  -- Proof comment: package the two structural facts needed by the source spreading theorem.
  obtain ⟨hfp, hgeneric⟩ :=
    finiteFreeRelationQuotientPresentation_finitePresentation_and_coeffGenericFiber_free
      (R := R) (n := n) (N := N) rel _e
  -- Proof comment: after recording finite presentation and generic-fiber freeness, the adapter
  -- consumes the single remaining coefficient-denominator spreading input.
  exact hspread hfp hgeneric

omit [Algebra.FiniteType R S] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: the coefficient-denominator generic-freeness core reduces
to finite-free quotient presentations of finitely presented polynomial modules. -/
theorem exists_nonzero_coeffAway_free_of_finiteFreeRelationQuotientPresentation
    {n m r : ℕ}
    {N : Type w} [AddCommGroup N] [Module (MvPolynomial (Fin n) R) N]
    (rel : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R]
      (Fin m → MvPolynomial (Fin n) R))
    (_e : Nonempty (N ≃ₗ[MvPolynomial (Fin n) R]
      (Fin m → MvPolynomial (Fin n) R) ⧸ LinearMap.range rel)) :
    ∃ f : R, f ≠ 0 ∧
      Module.Free (Localization.Away f)
        (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N) := by
  -- Proof comment: all relation-quotient bookkeeping is handled by the adapter above; the first
  -- open point is now the source coefficient-spreading theorem for finitely presented polynomial
  -- modules with free coefficient generic fiber.
  refine finiteFreeRelationQuotientPresentation_coeffAway_free_of_spreading
    (R := R) (n := n) (N := N) ?_ rel _e
  -- Proof comment: the coefficient-spreading theorem now lives in the imported acyclic helper
  -- module, so this target declaration is only the relation-quotient specialization.
  exact exists_coeffAway_free_of_finitelyPresented_mvPolynomialModule_of_coeffGenericFiber_free
    (R := R)

omit [Algebra.FiniteType R S] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: the source generic-freeness core for finitely presented
modules over finite-variable polynomial algebras, with denominator taken from the coefficient
domain.  This is the remaining Stacks 051S coefficient-denominator input. -/
theorem exists_nonzero_coeffAway_free_of_finitelyPresented_mvPolynomialModule_core
    {n : ℕ}
    {N : Type w} [AddCommGroup N] [Module (MvPolynomial (Fin n) R) N]
    [Module.FinitePresentation (MvPolynomial (Fin n) R) N] :
    ∃ f : R, f ≠ 0 ∧
      Module.Free (Localization.Away f)
        (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N) := by
  classical
  -- Proof comment: consume the same acyclic coefficient-spreading input directly, using the
  -- automatic coefficient-generic-fiber freeness over the fraction field.
  exact exists_coeffAway_free_of_finitelyPresented_mvPolynomialModule_of_coeffGenericFiber_free
    (R := R) (n := n) (N := N) inferInstance
    (mvPolynomialModule_coeffGenericFiber_free (R := R) (n := n) (N := N))

omit [Algebra.FiniteType R S] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: a finitely presented polynomial module that is free after
inverting one nonzero polynomial has a nonzero coefficient denominator after which the module is
free over the localized coefficient ring. -/
theorem exists_coeffAway_free_of_polynomialAway_free
    {n : ℕ}
    {N : Type w} [AddCommGroup N] [Module (MvPolynomial (Fin n) R) N]
    [Module.FinitePresentation (MvPolynomial (Fin n) R) N]
    (g : MvPolynomial (Fin n) R) (_hg : g ≠ 0)
    (_hfree : Module.Free (Localization.Away g) (LocalizedModule.Away g N)) :
    ∃ f : R, f ≠ 0 ∧
      Module.Free (Localization.Away f)
        (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N) := by
  -- Proof comment: polynomial-away freeness is not sufficient by itself to choose a coefficient
  -- denominator.  The true source theorem supplies such a denominator independently of the
  -- particular polynomial witness.
  exact exists_nonzero_coeffAway_free_of_finitelyPresented_mvPolynomialModule_core
    (R := R) (n := n) (N := N)

omit [Algebra.FiniteType R S] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: coefficient-generic-fiber freeness of a finitely presented
polynomial module spreads out to freeness after inverting one nonzero coefficient. -/
theorem exists_nonzero_coeffAway_free_of_coeffGenericFiber_free
    {n : ℕ}
    {N : Type w} [AddCommGroup N] [Module (MvPolynomial (Fin n) R) N]
    [Module.FinitePresentation (MvPolynomial (Fin n) R) N]
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
  -- Route correction: use mathlib's arbitrary polynomial denominator first, then delegate only the
  -- denominator-normalization step to the isolated structural theorem above.
  obtain ⟨g, hg, hfree⟩ :=
    exists_nonzero_away_polynomial_free_of_finitely_presented_module
      (R := R) (n := n) (N := N)
  -- Proof comment: the remaining source step converts the polynomial denominator `g` into some
  -- nonzero coefficient denominator of `R`.
  exact exists_coeffAway_free_of_polynomialAway_free (R := R) (n := n) (N := N) g hg hfree

omit [Algebra.FiniteType R S] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: the coefficient-denominator core also gives the same
localized freeness when the polynomial denominator is written as `algebraMap R _ f`. -/
lemma exists_nonzero_algebraMapAway_free_of_coeffAway_core
    {n : ℕ}
    {N : Type w} [AddCommGroup N] [Module (MvPolynomial (Fin n) R) N]
    [Module.FinitePresentation (MvPolynomial (Fin n) R) N] :
    ∃ f : R, f ≠ 0 ∧
      Module.Free (Localization.Away f)
        (LocalizedModule.Away (algebraMap R (MvPolynomial (Fin n) R) f) N) := by
  -- Proof comment: consume the named coefficient core, then hand its free basis to the existing
  -- owner-localization bridge so the denominator spelling and module action both match.
  obtain ⟨f, hf, hfree⟩ :=
    exists_nonzero_coeffAway_free_of_finitelyPresented_mvPolynomialModule_core
      (R := R) (n := n) (N := N)
  refine ⟨f, hf, ?_⟩
  letI : Module.Free (Localization.Away f)
      (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N) := hfree
  -- Proof comment: the owner-localization bridge changes only the module action, from the
  -- coefficient-localized polynomial action to the canonical action for the denominator
  -- `algebraMap R (MvPolynomial _) f`.
  exact ownerAway_free_of_coeffAway_free_presentation
    (R := R) (n := n) (A := MvPolynomial (Fin n) R) (N := N) f

omit [Algebra.FiniteType R S] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: source generic freeness for a finitely presented algebra
and a finitely presented module over a domain. -/
theorem exists_nonzero_away_free_of_finitePresentation_algebra_module
    {A : Type v} [CommRing A] [Algebra R A] [Algebra.FinitePresentation R A]
    {N : Type w} [AddCommGroup N] [Module A N] [Module.FinitePresentation A N] :
    ∃ f : R, f ≠ 0 ∧
      Module.Free (Localization.Away f) (LocalizedModule.Away (algebraMap R A f) N) := by
  -- Route correction: the presentation descent and owner-localization transport have been
  -- isolated in the previous helper, so this theorem now consumes the standalone coefficient
  -- core instead of hiding that source theorem as a local proof hole.
  let hcoeff :
      ∀ {n : ℕ}
        {N₀ : Type w} [AddCommGroup N₀] [Module (MvPolynomial (Fin n) R) N₀]
        [Module.FinitePresentation (MvPolynomial (Fin n) R) N₀],
        ∃ f : R, f ≠ 0 ∧
          Module.Free (Localization.Away f)
            (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N₀) :=
    fun {n} {N₀} ↦
      exists_nonzero_coeffAway_free_of_finitelyPresented_mvPolynomialModule_core
        (R := R) (n := n) (N := N₀)
  -- Proof comment: once the polynomial coefficient core is supplied, the closed reduction helper
  -- completes the finite-presentation algebra/module case.
  exact exists_nonzero_away_free_of_finitePresentation_algebra_module_of_coeffAway
    (R := R) (A := A) (N := N) hcoeff

/-- Helper for Chap10 Lemma 10 118 3: source generic freeness specialized to a finite-variable
polynomial algebra, before normalizing the denominator to `MvPolynomial.C f`. -/
lemma exists_nonzero_algebraMapAway_free_of_finitelyPresented_mvPolynomialModule
    {n : ℕ}
    {N : Type*} [AddCommGroup N] [Module (MvPolynomial (Fin n) R) N]
    [Module.FinitePresentation (MvPolynomial (Fin n) R) N] :
    ∃ f : R, f ≠ 0 ∧
      Module.Free (Localization.Away f)
        (LocalizedModule.Away (algebraMap R (MvPolynomial (Fin n) R) f) N) := by
  -- Proof comment: this algebra-map spelling is supplied by the named coefficient core plus the
  -- owner-localization bridge packaged in the previous adapter.
  exact exists_nonzero_algebraMapAway_free_of_coeffAway_core (R := R) (n := n) (N := N)

omit [IsDomain R] [Algebra.FiniteType R S] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: the coefficient denominator written through the
polynomial algebra map is the same polynomial as `MvPolynomial.C f`. -/
lemma mvPolynomial_algebraMap_eq_C_coeff
    {n : ℕ} (f : R) :
    algebraMap R (MvPolynomial (Fin n) R) f = MvPolynomial.C (σ := Fin n) f := by
  -- Proof comment: this records the denominator-spelling bridge used when moving between
  -- owner-localization APIs and coefficient-polynomial APIs.
  rw [MvPolynomial.algebraMap_eq]

/-- Helper for Chap10 Lemma 10 118 3: replace the source-theorem denominator
`algebraMap R (MvPolynomial (Fin n) R) f` by the coefficient polynomial `C f`. -/
lemma coeffAway_free_of_algebraMapAway_free
    {n : ℕ}
    {N : Type*} [AddCommGroup N] [Module (MvPolynomial (Fin n) R) N]
    (f : R)
    [Module.Free (Localization.Away f)
      (LocalizedModule.Away (algebraMap R (MvPolynomial (Fin n) R) f) N)] :
    Module.Free (Localization.Away f)
      (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N) := by
  let P := MvPolynomial (Fin n) R
  let B := Localization.Away (MvPolynomial.C (σ := Fin n) f)
  let algAB := (Localization.awayMapₐ (Algebra.ofId R P) f).toAlgebra
  letI : SMul (Localization.Away f) B := algAB.toSMul
  letI : Algebra (Localization.Away f) B := algAB
  let mcanon : Module (Localization.Away f)
      (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N) :=
    Module.compHom (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N)
      (algebraMap (Localization.Away f) B)
  have hfree : @Module.Free (Localization.Away f)
      (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N) _ _ mcanon := by
    -- Proof comment: expose the canonical away-map action and use the polynomial algebra-map
    -- computation to identify the two denominator spellings.
    simpa [P, B, algAB, mcanon, mvPolynomial_algebraMap_eq_C_coeff (R := R) (n := n) f] using
      (inferInstance : Module.Free (Localization.Away f)
        (LocalizedModule.Away (algebraMap R (MvPolynomial (Fin n) R) f) N))
  -- Proof comment: after denominator normalization, reuse the existing same-carrier bridge to
  -- switch to the base-localized polynomial action expected by downstream lemmas.
  exact coeffAwayBaseModuleFreeOfCanonicalRestriction (R := R) (n := n) (N := N) f hfree

/-- Helper for Chap10 Lemma 10 118 3: source generic freeness for one finitely presented
polynomial module, specialized to coefficient denominators from the base domain. -/
theorem exists_nonzero_coeffAway_free_of_finitelyPresented_mvPolynomialModule
    {n : ℕ}
    {N : Type*} [AddCommGroup N] [Module (MvPolynomial (Fin n) R) N]
    [Module.FinitePresentation (MvPolynomial (Fin n) R) N] :
    ∃ f : R, f ≠ 0 ∧
      Module.Free (Localization.Away f)
        (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N) := by
  -- Proof comment: the public polynomial specialization is now just the named coefficient-core
  -- theorem; the surrounding source theorem consumes the same core through the presentation
  -- reduction above.
  exact exists_nonzero_coeffAway_free_of_finitelyPresented_mvPolynomialModule_core
    (R := R) (n := n) (N := N)

/-- Helper for Chap10 Lemma 10 118 3: two already-known coefficient-away freeness witnesses can
be refined to one common product denominator. -/
lemma exists_common_coeffAway_free_of_pair
    {n : ℕ}
    {S' : Type*} [AddCommGroup S'] [Module (MvPolynomial (Fin n) R) S']
    {M' : Type*} [AddCommGroup M'] [Module (MvPolynomial (Fin n) R) M']
    (hS : ∃ f : R, f ≠ 0 ∧
      Module.Free (Localization.Away f)
        (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) S'))
    (hM : ∃ f : R, f ≠ 0 ∧
      Module.Free (Localization.Away f)
        (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) M')) :
    ∃ f : R, f ≠ 0 ∧
      Module.Free (Localization.Away f)
        (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) S') ∧
      Module.Free (Localization.Away f)
        (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) M') := by
  -- Proof comment: unpack the two denominators and use their product as the shared principal open.
  obtain ⟨fS, hfS, hFreeS⟩ := hS
  obtain ⟨fM, hfM, hFreeM⟩ := hM
  refine ⟨fS * fM, mul_ne_zero hfS hfM, ?_, ?_⟩
  · letI : Module.Free (Localization.Away fS)
        (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) fS) S') := hFreeS
    -- Proof comment: further localize the `S'` witness at the second denominator.
    exact coeffAway_free_of_mul_right (R := R) (n := n) (N := S') fS fM
  · letI : Module.Free (Localization.Away fM)
        (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) fM) M') := hFreeM
    -- Proof comment: localize the `M'` witness at the first denominator and commute the product
    -- at the lemma statement level so it matches the chosen common denominator.
    exact coeffAway_free_of_mul_left (R := R) (n := n) (N := M') fM fS

/-- Helper for Chap10 Lemma 10 118 3: two finitely presented polynomial modules become free
after inverting one common nonzero coefficient. -/
theorem exists_common_nonzero_coeffAway_free_of_finitelyPresented_mvPolynomialModules
    {n : ℕ}
    {S' : Type*} [AddCommGroup S'] [Module (MvPolynomial (Fin n) R) S']
    [Module.FinitePresentation (MvPolynomial (Fin n) R) S']
    {M' : Type*} [AddCommGroup M'] [Module (MvPolynomial (Fin n) R) M']
    [Module.FinitePresentation (MvPolynomial (Fin n) R) M'] :
    ∃ f : R, f ≠ 0 ∧
      Module.Free (Localization.Away f)
        (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) S') ∧
      Module.Free (Localization.Away f)
        (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) M') := by
  -- Proof comment: obtain separate one-module denominators from the source theorem, then delegate
  -- the product-denominator refinement to the reusable pair helper above.
  exact exists_common_coeffAway_free_of_pair (R := R) (n := n) (S' := S') (M' := M')
    (exists_nonzero_coeffAway_free_of_finitelyPresented_mvPolynomialModule
      (R := R) (n := n) (N := S'))
    (exists_nonzero_coeffAway_free_of_finitelyPresented_mvPolynomialModule
      (R := R) (n := n) (N := M'))

omit [Algebra.FiniteType R S] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: a generic-fiber equivalence descends injectivity to the
fixed coefficient-away localization once the source is free over `R_f`. -/
theorem coeffAway_localized_map_injective_of_genericFiber_linearEquiv
    {n : ℕ} {f : R} (hf : f ≠ 0)
    {N' N : Type*} [AddCommGroup N'] [Module (MvPolynomial (Fin n) R) N']
    [AddCommGroup N] [Module (MvPolynomial (Fin n) R) N]
    (φ : N' →ₗ[MvPolynomial (Fin n) R] N)
    (e : LocalizedModule
        (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) (nonZeroDivisors R)) N' ≃ₗ[Localization
            (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) (nonZeroDivisors R))]
        LocalizedModule
          (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) (nonZeroDivisors R)) N)
    (he : e.toLinearMap = LocalizedModule.map
      (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) (nonZeroDivisors R)) φ)
    [Module.Free (Localization.Away f)
      (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N')] :
    Function.Injective
      (LocalizedModule.map (Submonoid.powers (MvPolynomial.C (σ := Fin n) f)) φ) := by
  -- Proof comment: localize the fixed coefficient-away map further to the coefficient generic
  -- fiber; there it is the supplied equivalence, hence injective.
  intro x y hxy
  let P := MvPolynomial (Fin n) R
  let U : Submonoid P := Submonoid.powers (MvPolynomial.C (σ := Fin n) f)
  let T : Submonoid P := Algebra.algebraMapSubmonoid P (nonZeroDivisors R)
  have hUT : U ≤ T := by
    simpa [P, U, T] using powers_C_le_polynomial_generic_denominators (R := R) (n := n) hf
  let lN' : LocalizedModule U N' →ₗ[P] LocalizedModule T N' :=
    LocalizedModule.liftOfLE U T hUT
  let lN : LocalizedModule U N →ₗ[P] LocalizedModule T N :=
    LocalizedModule.liftOfLE U T hUT
  have hcomm (z : LocalizedModule U N') :
      lN ((LocalizedModule.map U φ) z) =
        (LocalizedModule.map T φ) (lN' z) := by
    -- Proof comment: the natural further-localization maps commute with localizing `φ`.
    refine LocalizedModule.induction_on (x := z) ?_
    intro m s
    rw [LocalizedModule.map_mk]
    rw [IsLocalizedModule.mk_eq_mk' (S := U) (M := N) s (φ m)]
    rw [IsLocalizedModule.liftOfLE_mk']
    rw [IsLocalizedModule.mk_eq_mk' (S := U) (M := N') s m]
    rw [IsLocalizedModule.liftOfLE_mk']
    rw [← IsLocalizedModule.mk_eq_mk' (S := T) (M := N') ⟨s.1, hUT s.2⟩ m]
    rw [LocalizedModule.map_mk]
    rw [IsLocalizedModule.mk_eq_mk' (S := T) (M := N) ⟨s.1, hUT s.2⟩ (φ m)]
  have hgen :
      (LocalizedModule.map T φ) (lN' x) = (LocalizedModule.map T φ) (lN' y) := by
    rw [← hcomm x, ← hcomm y, hxy]
  have hinjT : Function.Injective (LocalizedModule.map T φ) := by
    rw [← he]
    exact e.injective
  have hlift : lN' x = lN' y := hinjT hgen
  have hliftInj : Function.Injective lN' := by
    intro a b hab
    obtain ⟨t, ht⟩ := IsLocalizedModule.exists_of_eq (S := T) (f := lN') hab
    rcases t with ⟨_, r, hr, rfl⟩
    let A := Localization.Away f
    letI : IsDomain A :=
      IsLocalization.isDomain_of_le_nonZeroDivisors A
        (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
    letI : Module A (LocalizedModule U N') :=
      away_polynomial_module_over_base_localization (R := R) (n := n) f
    have hscalar (z : LocalizedModule U N') :
        (MvPolynomial.C (σ := Fin n) r : P) • z = (algebraMap R A r) • z := by
      rw [away_polynomial_source_coeff_smul_eq (R := R) (n := n) (N := N') f
        (algebraMap R A r) z]
      rw [away_mvPolynomial_C_algEquiv_symm_C (R := R) (n := n) f r]
      exact (IsScalarTower.algebraMap_smul
        (Localization.Away (MvPolynomial.C (σ := Fin n) f))
        (MvPolynomial.C (σ := Fin n) r : MvPolynomial (Fin n) R) z).symm
    have htA : (algebraMap R A r) • a = (algebraMap R A r) • b := by
      rw [← hscalar a, ← hscalar b]
      exact ht
    have hrA : algebraMap R A r ≠ 0 :=
      IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors A
        (powers_le_nonZeroDivisors_of_noZeroDivisors hf) hr
    have hsub : (algebraMap R A r) • (a - b) = 0 := by
      rw [smul_sub, htA, sub_self]
    have hzero : a - b = 0 := (smul_eq_zero_iff_right hrA).mp hsub
    exact sub_eq_zero.mp hzero
  exact hliftInj hlift

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 118 3: a compatible generic-fiber equivalence descends a
coefficient-away localized algebra presentation to the owner localization of `S`. -/
theorem localized_algebra_model_linearEquiv_of_genericFiber_linearEquiv
    {n : ℕ} {f : R} (hf : f ≠ 0)
    [Algebra (MvPolynomial (Fin n) R) S]
    [IsScalarTower R (MvPolynomial (Fin n) R) S]
    {S' : Type*} [AddCommGroup S'] [Module (MvPolynomial (Fin n) R) S']
    (φS : S' →ₗ[MvPolynomial (Fin n) R] S) (hφS : Function.Surjective φS)
    (eS : LocalizedModule
        (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) (nonZeroDivisors R)) S' ≃ₗ[Localization
          (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) (nonZeroDivisors R))]
          LocalizedModule
            (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) (nonZeroDivisors R)) S)
    (heS : eS.toLinearMap = LocalizedModule.map
      (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) (nonZeroDivisors R)) φS)
    [Module.Free (Localization.Away f)
      (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) S')] :
    letI : Algebra (MvPolynomial (Fin n) (Localization.Away f))
        (Localization.Away (algebraMap R S f)) :=
      localizedCoeffAwayOwnerAlgebra (R := R) (S := S) (n := n) f
    letI : IsScalarTower (Localization.Away f)
        (MvPolynomial (Fin n) (Localization.Away f))
        (Localization.Away (algebraMap R S f)) :=
      localizedCoeffAwayOwnerAlgebra_isScalarTower (R := R) (S := S) (n := n) f
    ∃ (_ : LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) S' ≃ₗ[
        MvPolynomial (Fin n) (Localization.Away f)]
        Localization.Away (algebraMap R S f)),
      True := by
  -- Proof comment: install the canonical owner algebra structure so the descent equivalence is
  -- stated in a stable instance world rather than under an arbitrary algebra witness.
  letI : Algebra (MvPolynomial (Fin n) (Localization.Away f))
      (Localization.Away (algebraMap R S f)) :=
    localizedCoeffAwayOwnerAlgebra (R := R) (S := S) (n := n) f
  letI : IsScalarTower (Localization.Away f)
      (MvPolynomial (Fin n) (Localization.Away f))
      (Localization.Away (algebraMap R S f)) :=
    localizedCoeffAwayOwnerAlgebra_isScalarTower (R := R) (S := S) (n := n) f
  refine ⟨?_, True.intro⟩
  -- Proof comment: once injectivity is known at this fixed coefficient denominator, the direct
  -- coefficient-away equivalence composes with the owner comparison equivalence.
  have hinj : Function.Injective
      (LocalizedModule.map (Submonoid.powers (MvPolynomial.C (σ := Fin n) f)) φS) := by
    exact coeffAway_localized_map_injective_of_genericFiber_linearEquiv
      (R := R) (n := n) (f := f) hf φS eS heS
  exact
    (coeffAway_localizedCoeffLinearEquivOfInjective
      (R := R) (n := n) (f := f) φS hφS hinj).trans
      (localizedCoeffAwayOwnerSelfCoeffLinearEquiv
        (R := R) (S := S) (n := n) f)

omit [Algebra.FiniteType R S] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: a compatible generic-fiber equivalence descends a
coefficient-away localized module presentation to the owner localization of `M`. -/
theorem localized_module_model_linearEquiv_of_genericFiber_linearEquiv
    {n : ℕ} {f : R} (hf : f ≠ 0)
    [Algebra (MvPolynomial (Fin n) R) S]
    [IsScalarTower R (MvPolynomial (Fin n) R) S]
    [Module (MvPolynomial (Fin n) R) M]
    [IsScalarTower (MvPolynomial (Fin n) R) S M]
    {M' : Type*} [AddCommGroup M'] [Module (MvPolynomial (Fin n) R) M']
    (φM : M' →ₗ[MvPolynomial (Fin n) R] M) (hφM : Function.Surjective φM)
    (eM : LocalizedModule
        (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) (nonZeroDivisors R)) M' ≃ₗ[Localization
          (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) (nonZeroDivisors R))]
          LocalizedModule
            (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) (nonZeroDivisors R)) M)
    (heM : eM.toLinearMap = LocalizedModule.map
      (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) (nonZeroDivisors R)) φM)
    [Module.Free (Localization.Away f)
      (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) M')] :
    letI : Algebra (MvPolynomial (Fin n) (Localization.Away f))
        (Localization.Away (algebraMap R S f)) :=
      localizedCoeffAwayOwnerAlgebra (R := R) (S := S) (n := n) f
    letI : Module (MvPolynomial (Fin n) (Localization.Away f))
        (LocalizedModule.Away (algebraMap R S f) M) :=
      localizedCoeffAwayOwnerModule (R := R) (S := S) (M := M) (n := n) f
    letI : IsScalarTower (MvPolynomial (Fin n) (Localization.Away f))
        (Localization.Away (algebraMap R S f))
        (LocalizedModule.Away (algebraMap R S f) M) :=
      localizedCoeffAwayOwnerModule_isScalarTower (R := R) (S := S) (M := M) (n := n) f
    ∃ (_ : LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) M' ≃ₗ[
        MvPolynomial (Fin n) (Localization.Away f)]
        LocalizedModule.Away (algebraMap R S f) M),
      True := by
  -- Route correction: the module descent is now stated in the canonical owner algebra/module
  -- instance world, avoiding the false arbitrary-algebra comparison route.
  letI : Algebra (MvPolynomial (Fin n) (Localization.Away f))
      (Localization.Away (algebraMap R S f)) :=
    localizedCoeffAwayOwnerAlgebra (R := R) (S := S) (n := n) f
  letI : Module (MvPolynomial (Fin n) (Localization.Away f))
      (LocalizedModule.Away (algebraMap R S f) M) :=
    localizedCoeffAwayOwnerModule (R := R) (S := S) (M := M) (n := n) f
  letI : IsScalarTower (MvPolynomial (Fin n) (Localization.Away f))
      (Localization.Away (algebraMap R S f))
      (LocalizedModule.Away (algebraMap R S f) M) :=
    localizedCoeffAwayOwnerModule_isScalarTower (R := R) (S := S) (M := M) (n := n) f
  refine ⟨?_, True.intro⟩
  -- Proof comment: as in the algebra case, the module comparison is now reduced to injectivity
  -- of the fixed-denominator localized presentation map; surjectivity and the owner comparison
  -- then assemble the required `R_f[x]`-linear equivalence.
  have hinj : Function.Injective
      (LocalizedModule.map (Submonoid.powers (MvPolynomial.C (σ := Fin n) f)) φM) := by
    exact coeffAway_localized_map_injective_of_genericFiber_linearEquiv
      (R := R) (n := n) (f := f) hf φM eM heM
  exact
    (coeffAway_localizedCoeffLinearEquivOfInjective
      (R := R) (n := n) (f := f) φM hφM hinj).trans
      (localizedCoeffAwayOwnerModuleCoeffLinearEquiv
        (R := R) (S := S) (M := M) (n := n) f)

end
