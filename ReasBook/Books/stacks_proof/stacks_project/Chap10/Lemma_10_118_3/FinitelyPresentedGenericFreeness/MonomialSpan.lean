import stacks_proof.stacks_project.Chap10.Lemma_10_118_3.PolynomialModels

universe u v w

section

variable {R : Type u} [CommRing R] [IsDomain R]
variable {S : Type v} [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
variable {M : Type w} [AddCommGroup M] [Module S M] [Module.Finite S M]

open GenericFlatness

attribute [local instance] MvPolynomial.algebraMvPolynomial

omit [Algebra.FiniteType R S] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: after inverting all nonzero coefficients, any localized
polynomial module is free over the fraction field of the coefficient domain. -/
lemma mvPolynomialModule_coeffGenericFiber_free
    {n : ℕ} {N : Type w} [AddCommGroup N] [Module (MvPolynomial (Fin n) R) N] :
    let P := MvPolynomial (Fin n) R
    let T := Algebra.algebraMapSubmonoid P (nonZeroDivisors R)
    let K := Localization (nonZeroDivisors R)
    let PT := Localization T
    letI : Module K (LocalizedModule T N) :=
      Module.compHom (LocalizedModule T N) (algebraMap K PT)
    Module.Free K (LocalizedModule T N) := by
  -- Proof comment: the total coefficient localization is a field, so the localized module is a
  -- vector space and therefore free over that coefficient field.
  dsimp
  infer_instance

omit [IsDomain R] [Algebra.FiniteType R S] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: an injective coefficient map preserves the monomial-order
leading degree of a multivariable polynomial. -/
private lemma monomialOrderDegree_map_of_injective
    {n : ℕ} {A : Type*} [CommSemiring A]
    (m : MonomialOrder (Fin n)) (φ : R →+* A) (hφ : Function.Injective φ)
    (g : MvPolynomial (Fin n) R) :
    m.degree (MvPolynomial.map φ g) = m.degree g := by
  -- Proof comment: the support is unchanged by an injective coefficient map, and the degree is
  -- the supremum of that support in the chosen monomial order.
  simp [MonomialOrder.degree, MvPolynomial.support_map_of_injective g hφ]

omit [IsDomain R] [Algebra.FiniteType R S] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: an injective coefficient map sends the monomial-order
leading coefficient to the leading coefficient after mapping. -/
private lemma monomialOrderLeadingCoeff_map_of_injective
    {n : ℕ} {A : Type*} [CommSemiring A]
    (m : MonomialOrder (Fin n)) (φ : R →+* A) (hφ : Function.Injective φ)
    (g : MvPolynomial (Fin n) R) :
    m.leadingCoeff (MvPolynomial.map φ g) = φ (m.leadingCoeff g) := by
  -- Proof comment: after preserving the leading degree, the coefficient computation is exactly
  -- `MvPolynomial.coeff_map` at that degree.
  simp [MonomialOrder.leadingCoeff,
    monomialOrderDegree_map_of_injective (R := R) (m := m) φ hφ g,
    MvPolynomial.coeff_map]

omit [Algebra.FiniteType R S] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: after localizing at a nonzero coefficient, the image of
that coefficient is a unit and remains the mapped leading coefficient. -/
private lemma mappedPolynomialLeadingCoeff_isUnit_away
    {n : ℕ} (m : MonomialOrder (Fin n)) (g : MvPolynomial (Fin n) R)
    {c : R} (hc : c = m.leadingCoeff g) (hc0 : c ≠ 0) :
    IsUnit (m.leadingCoeff (MvPolynomial.map (algebraMap R (Localization.Away c)) g)) := by
  have hregular : Submonoid.powers c ≤ nonZeroDivisors R :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hc0
  have hinj : Function.Injective (algebraMap R (Localization.Away c)) :=
    IsLocalization.injective (Localization.Away c) hregular
  -- Proof comment: identify the new leading coefficient with the image of `c`, then use the
  -- universal localization fact that the inverted element is a unit.
  rw [monomialOrderLeadingCoeff_map_of_injective (R := R) (m := m)
    (algebraMap R (Localization.Away c)) hinj g, ← hc]
  exact IsLocalization.Away.algebraMap_isUnit c

omit [Algebra.FiniteType R S] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: if a leading coefficient divides the chosen coefficient
denominator, then its image is still the mapped leading coefficient and is a unit after localizing
away from that denominator. -/
private lemma mappedPolynomialLeadingCoeff_isUnit_away_of_dvd
    {n : ℕ} (m : MonomialOrder (Fin n)) (g : MvPolynomial (Fin n) R)
    {f : R} (hf : f ≠ 0) (hdiv : m.leadingCoeff g ∣ f) :
    IsUnit (m.leadingCoeff (MvPolynomial.map (algebraMap R (Localization.Away f)) g)) := by
  have hregular : Submonoid.powers f ≤ nonZeroDivisors R :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hf
  have hinj : Function.Injective (algebraMap R (Localization.Away f)) :=
    IsLocalization.injective (Localization.Away f) hregular
  -- Proof comment: injectivity keeps the monomial-order leading coefficient visible after
  -- mapping coefficients, and divisibility by the inverted denominator makes that coefficient a
  -- unit in the away localization.
  rw [monomialOrderLeadingCoeff_map_of_injective (R := R) (m := m)
    (algebraMap R (Localization.Away f)) hinj g]
  exact IsLocalization.Away.isUnit_of_dvd f hdiv

omit [Algebra.FiniteType R S] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: a finite product of nonzero monomial-order leading
coefficients is nonzero. -/
private lemma monomialOrderLeadingCoeff_finsetProduct_ne_zero
    {n : ℕ} (m : MonomialOrder (Fin n))
    (s : Finset (MvPolynomial (Fin n) R))
    (hs : ∀ g ∈ s, g ≠ 0) :
    s.prod (fun g => m.leadingCoeff g) ≠ 0 := by
  -- Proof comment: over a domain, a finite product is nonzero once each leading coefficient is
  -- nonzero; the monomial-order API identifies that condition with nonzero polynomials.
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro g hg
  exact m.leadingCoeff_ne_zero_iff.mpr (hs g hg)

omit [Algebra.FiniteType R S] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: when the denominator is the product of finitely many leading
coefficients, every member of the finite family has unit mapped leading coefficient after
localization at that product. -/
private lemma mappedPolynomialLeadingCoeff_isUnit_away_finsetProduct
    {n : ℕ} (m : MonomialOrder (Fin n))
    (s : Finset (MvPolynomial (Fin n) R)) {g : MvPolynomial (Fin n) R} (hg : g ∈ s)
    (hprod : s.prod (fun h => m.leadingCoeff h) ≠ 0) :
    IsUnit (m.leadingCoeff (MvPolynomial.map
      (algebraMap R (Localization.Away (s.prod fun h => m.leadingCoeff h))) g)) := by
  -- Proof comment: membership in the finite family supplies the divisibility of the product
  -- denominator by this polynomial's leading coefficient.
  exact mappedPolynomialLeadingCoeff_isUnit_away_of_dvd (R := R) (m := m) g hprod
    (Finset.dvd_prod_of_mem (fun h : MvPolynomial (Fin n) R => m.leadingCoeff h) hg)

omit [Algebra.FiniteType R S] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: for a finite family of nonzero polynomials, localizing
away from the product of their leading coefficients makes every mapped leading coefficient a
unit. -/
private lemma mappedPolynomialLeadingCoeff_isUnit_away_finsetProduct_of_nonzero
    {n : ℕ} (m : MonomialOrder (Fin n))
    (s : Finset (MvPolynomial (Fin n) R)) {g : MvPolynomial (Fin n) R} (hg : g ∈ s)
    (hs : ∀ h ∈ s, h ≠ 0) :
    IsUnit (m.leadingCoeff (MvPolynomial.map
      (algebraMap R (Localization.Away (s.prod fun h => m.leadingCoeff h))) g)) := by
  -- Proof comment: this packages the two side conditions needed for denominator clearing:
  -- nonzero product denominator and divisibility of each listed leading coefficient by it.
  exact mappedPolynomialLeadingCoeff_isUnit_away_finsetProduct (R := R) (m := m) s hg
    (monomialOrderLeadingCoeff_finsetProduct_ne_zero (R := R) m s hs)

omit [CommRing R] [IsDomain R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
  [AddCommGroup M] [Module S M] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: module monomials in a finite free multivariable
polynomial module. -/
private noncomputable abbrev moduleMonomialVector
    {A : Type*} [CommSemiring A] {n m : ℕ}
    (ja : Fin m × (Fin n →₀ ℕ)) : Fin m → MvPolynomial (Fin n) A :=
  Pi.single ja.1 (MvPolynomial.monomial ja.2 (1 : A))

omit [CommRing R] [IsDomain R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
  [AddCommGroup M] [Module S M] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: the submodule spanned by a set of module monomials. -/
private noncomputable abbrev moduleMonomialSpan
    {A : Type*} [CommSemiring A] {n m : ℕ}
    (D : Set (Fin m × (Fin n →₀ ℕ))) :
    Submodule (MvPolynomial (Fin n) A) (Fin m → MvPolynomial (Fin n) A) :=
  Submodule.span (MvPolynomial (Fin n) A) (moduleMonomialVector '' D)

omit [CommRing R] [IsDomain R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
  [AddCommGroup M] [Module S M] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: a module monomial whose term is divisible by one of the
chosen generators belongs to the corresponding module-monomial span. -/
private lemma moduleMonomial_mem_span_of_dvd
    {A : Type*} [CommSemiring A] {n m : ℕ}
    {D : Set (Fin m × (Fin n →₀ ℕ))} {j j0 : Fin m} {a a0 : Fin n →₀ ℕ} {c : A}
    (hD : (j0, a0) ∈ D) (hj : j = j0) (hle : a0 ≤ a) :
    (Pi.single j (MvPolynomial.monomial a c) : Fin m → MvPolynomial (Fin n) A) ∈
      moduleMonomialSpan (A := A) (n := n) (m := m) D := by
  -- Proof comment: replace the target coordinate by the generator coordinate, then express the
  -- larger monomial as a scalar multiple of the chosen generator monomial.
  subst j
  obtain ⟨b, rfl⟩ : ∃ b, a = a0 + b := by
    simpa [add_comm] using (le_iff_exists_add.mp hle)
  let gen : Fin m → MvPolynomial (Fin n) A :=
    moduleMonomialVector (A := A) (n := n) (m := m) (j0, a0)
  have hgen : gen ∈ moduleMonomialVector (A := A) (n := n) (m := m) '' D := by
    -- Proof comment: the selected divisor term is one of the listed module-monomial generators.
    exact ⟨(j0, a0), hD, rfl⟩
  have hmem : gen ∈ moduleMonomialSpan (A := A) (n := n) (m := m) D :=
    Submodule.subset_span hgen
  -- Proof comment: scalar-multiply the generator by the quotient monomial and verify the
  -- coordinatewise identity in the finite free module.
  convert Submodule.smul_mem _ (MvPolynomial.monomial b c) hmem using 1
  funext k
  by_cases hk : k = j0
  · subst k
    dsimp [gen, moduleMonomialVector]
    rw [Pi.single_eq_same, Pi.single_eq_same, MvPolynomial.monomial_mul]
    simp [add_comm]
  · dsimp [gen, moduleMonomialVector]
    rw [Pi.single_eq_of_ne hk, Pi.single_eq_of_ne hk, mul_zero]

omit [CommRing R] [IsDomain R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
  [AddCommGroup M] [Module S M] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: a coordinate polynomial supported on terms divisible by
chosen module monomials lies in their span. -/
private lemma moduleSingle_mem_span_of_support_forall
    {A : Type*} [CommSemiring A] {n m : ℕ}
    {D : Set (Fin m × (Fin n →₀ ℕ))} (j : Fin m) (p : MvPolynomial (Fin n) A)
    (h : ∀ a ∈ p.support, ∃ j0 a0, (j0, a0) ∈ D ∧ j = j0 ∧ a0 ≤ a) :
    (Pi.single j p : Fin m → MvPolynomial (Fin n) A) ∈
      moduleMonomialSpan (A := A) (n := n) (m := m) D := by
  have hsum :
      (Pi.single j p : Fin m → MvPolynomial (Fin n) A) =
        ∑ a ∈ p.support, (Pi.single j (MvPolynomial.monomial a (p.coeff a)) :
          Fin m → MvPolynomial (Fin n) A) := by
    -- Proof comment: expand the coordinate polynomial into its finite monomial support while
    -- keeping the surrounding `Pi.single` map explicit.
    funext k
    by_cases hk : k = j
    · subst k
      rw [Pi.single_eq_same, Finset.sum_apply]
      simp only [Pi.single_eq_same]
      exact p.as_sum
    · rw [Pi.single_eq_of_ne hk, Finset.sum_apply]
      simp only [Pi.single_eq_of_ne hk]
      rw [Finset.sum_const_zero]
  -- Proof comment: after the support expansion, each monomial summand is handled by the
  -- divisibility-to-span lemma above.
  rw [hsum]
  refine Submodule.sum_mem _ fun a ha => ?_
  obtain ⟨j0, a0, hD, hj, hle⟩ := h a ha
  exact moduleMonomial_mem_span_of_dvd (A := A) (n := n) (m := m) hD hj hle

omit [CommRing R] [IsDomain R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
  [AddCommGroup M] [Module S M] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: the support-divisibility condition puts a finite free
polynomial-module vector in the span of the corresponding module monomials. -/
private lemma module_mem_span_of_support_forall
    {A : Type*} [CommSemiring A] {n m : ℕ}
    {D : Set (Fin m × (Fin n →₀ ℕ))} (v : Fin m → MvPolynomial (Fin n) A)
    (h : ∀ j a, a ∈ (v j).support → ∃ j0 a0, (j0, a0) ∈ D ∧ j = j0 ∧ a0 ≤ a) :
    v ∈ moduleMonomialSpan (A := A) (n := n) (m := m) D := by
  -- Proof comment: decompose the vector into coordinate singles and apply the coordinate
  -- support criterion to each summand.
  rw [← Finset.univ_sum_single v]
  refine Submodule.sum_mem _ fun j _ => ?_
  exact moduleSingle_mem_span_of_support_forall (A := A) (n := n) (m := m) j (v j) (h j)

omit [CommRing R] [IsDomain R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
  [AddCommGroup M] [Module S M] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: membership in a module-monomial span projects to
membership of each coordinate in the corresponding monomial ideal. -/
private lemma moduleMonomialSpan_coord_mem_monomialIdeal
    {A : Type*} [CommSemiring A] {n m : ℕ}
    {D : Set (Fin m × (Fin n →₀ ℕ))}
    {v : Fin m → MvPolynomial (Fin n) A}
    (hv : v ∈ moduleMonomialSpan (A := A) (n := n) (m := m) D) (j : Fin m) :
    v j ∈ Ideal.span
      ((fun a : Fin n →₀ ℕ => MvPolynomial.monomial a (1 : A)) ''
        {a | (j, a) ∈ D}) := by
  let I : Ideal (MvPolynomial (Fin n) A) :=
    Ideal.span ((fun a : Fin n →₀ ℕ => MvPolynomial.monomial a (1 : A)) ''
      {a | (j, a) ∈ D})
  -- Proof comment: induct over the span presentation; a generator either lives in this coordinate
  -- and gives a listed monomial, or projects to zero.
  change v j ∈ I
  induction hv using Submodule.span_induction with
  | mem x hx =>
    change x j ∈ I
    obtain ⟨ja, hja, rfl⟩ := hx
    rcases ja with ⟨j0, a0⟩
    by_cases hj : j0 = j
    · subst j0
      dsimp [moduleMonomialVector, I]
      rw [Pi.single_eq_same]
      exact Ideal.subset_span ⟨a0, hja, rfl⟩
    · dsimp [moduleMonomialVector, I]
      simpa [Pi.single_apply, hj] using Ideal.zero_mem I
  | zero =>
    change (0 : Fin m → MvPolynomial (Fin n) A) j ∈ I
    exact Ideal.zero_mem I
  | add x y _ _ hx hy =>
    change (x + y) j ∈ I
    exact Ideal.add_mem I hx hy
  | smul a x _ hx =>
    change (a • x) j ∈ I
    -- Proof comment: the span is a `P`-submodule, while the projected coordinate condition is an
    -- ideal condition, so scalar multiplication becomes multiplication in the coordinate ideal.
    simpa [Pi.smul_apply, smul_eq_mul] using Ideal.mul_mem_left I a hx

omit [CommRing R] [IsDomain R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
  [AddCommGroup M] [Module S M] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: the finite-free module monomial span is characterized by
coordinatewise support divisibility by the listed module monomials. -/
private lemma mem_moduleMonomialSpan_iff_support_forall
    {A : Type*} [CommSemiring A] {n m : ℕ}
    {D : Set (Fin m × (Fin n →₀ ℕ))} (v : Fin m → MvPolynomial (Fin n) A) :
    v ∈ moduleMonomialSpan (A := A) (n := n) (m := m) D ↔
      ∀ j a, a ∈ (v j).support →
        ∃ j0 a0, (j0, a0) ∈ D ∧ j = j0 ∧ a0 ≤ a := by
  constructor
  · intro hv j a ha
    -- Proof comment: project the module span to the `j`th monomial ideal, then use mathlib's
    -- monomial-ideal support criterion to recover a divisor of the support term.
    have hcoord :=
      moduleMonomialSpan_coord_mem_monomialIdeal (A := A) (n := n) (m := m)
        (D := D) hv j
    obtain ⟨a0, ha0D, hle⟩ :=
      (MvPolynomial.mem_ideal_span_monomial_image (x := v j)
        (s := {a0 | (j, a0) ∈ D})).mp hcoord a ha
    exact ⟨j, a0, ha0D, rfl, hle⟩
  · intro h
    -- Proof comment: the reverse implication is the already isolated support-to-span direction.
    exact module_mem_span_of_support_forall (A := A) (n := n) (m := m) v h

-- Route correction: the tempting unit-leading-coefficient descent is false as stated.  For
-- instance, over `ℤ` with `N = ℤ[x] ⧸ (2, x)` and `g = x`, the localization `N_g` is zero and
-- hence free, while localizing at the unit leading coefficient leaves `ℤ/2`, which is not a free
-- `ℤ`-module.  The remaining placeholder is therefore the actual source generic-freeness theorem,
-- not a Groebner normal-form consequence.

omit [IsDomain R] [Algebra.FiniteType R S] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: a monic one-variable quotient is free over its
coefficient ring. -/
private theorem monicPolynomialQuotient_freeOverBase
    {A : Type*} [CommRing A] {q : Polynomial A} (hq : q.Monic) :
    Module.Free A (Polynomial A ⧸ Ideal.span ({q} : Set (Polynomial A))) := by
  -- Proof comment: mathlib's power-basis construction for monic quotients already supplies the
  -- required free basis over the coefficient ring.
  simpa using hq.free_quotient

end
