import Mathlib
import StacksProject_2024.Chap15.Lemma_15_51_3
import StacksProject_2024.Chap15.Lemma_15_51_4

-- Declarations for this item will be appended below by the statement pipeline.

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

section

/- Domain sampling pass:
- primary domain: permanence of the Chapter 15 `P`-ring formal-fiber condition under essentially
  finite type algebra maps;
- sampled owner declarations:
  `IsPRing`,
  `FieldAlgebraProperty.HasPropertyA`,
  `FieldAlgebraProperty.HasPropertyB`,
  `FieldAlgebraProperty.HasPropertyC`,
  `FieldAlgebraProperty.HasPropertyD`,
  `isPRing_of_quasiFinite`,
  `isPRing_iff_localFormalFibersHaveProperty_atMaximal`;
- best owner abstraction: the source-facing owner is `IsPRing P R`; the theorem should stay on
  that owner and reuse the Chapter 15 permanence axioms as inferable classes, rather than
  expanding the prime-pair condition or carrying redundant Noetherian hypotheses in the public
  interface;
- primitive data: the `R`-algebra `S`, the essentially finite type hypothesis, the four transfer
  axioms `(A)` through `(D)` on `P`, and the owner input `hR : IsPRing P R`;
- derived API: the resulting owner conclusion `IsPRing P S`.

Source/core/bridge triage:
- `source-facing`: `isPRing_of_essFiniteType`;
- `core/canonical`: `IsPRing` together with the owner axioms `P.HasPropertyA`, `P.HasPropertyB`,
  `P.HasPropertyC`, and `P.HasPropertyD`;
- `bridge/view`: `isPRing_of_quasiFinite` and
  `isPRing_iff_localFormalFibersHaveProperty_atMaximal`, which supply the canonical local and
  quasi-finite reductions used by the proof strategy.
-/
variable (P : FieldAlgebraProperty)
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Algebra.EssFiniteType R S]
variable [P.HasPropertyA] [P.HasPropertyB] [P.HasPropertyC] [P.HasPropertyD]

/-- Helper for Proposition 15.51.5: every prime localization of a `P`-ring is again a `P`-ring. -/
lemma isPRing_localizationAtPrime
    {A : Type u} [CommRing A] (hA : IsPRing P A) (p : PrimeSpectrum A) :
    IsPRing P (Localization.AtPrime p.asIdeal) := by
  let _ : IsNoetherianRing A := hA.toIsNoetherian
  -- Proof comment: rewrite the localized target by the prime-pair criterion and specialize the
  -- ambient `P`-ring hypothesis along the inclusion `q ≤ p`.
  refine (isPRing_localizationAtPrime_iff (P := P) p).2 ?_
  intro q hqp
  exact hA.satisfiesPPrimePairCondition p q hqp

/-- Helper for Proposition 15.51.5: a Noetherian ring is a `P`-ring once all of its prime
localizations are `P`-rings. -/
lemma isPRing_of_localizationsAtPrime
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (hlocal : ∀ p : PrimeSpectrum A, IsPRing P (Localization.AtPrime p.asIdeal)) :
    IsPRing P A := by
  -- Proof comment: the global prime-pair condition is read off from the chosen localization at
  -- the larger prime `p`.
  refine (isPRing_iff_satisfiesPPrimePairCondition (P := P) (R := A)).2 ?_
  intro p q hqp
  exact (isPRing_localizationAtPrime_iff (P := P) p).1 (hlocal p) q hqp

/-- Helper for Proposition 15.51.5: any chosen localization model of `A` at a prime inherits the
`P`-ring property from `A`. -/
lemma isPRing_of_localization_model_atPrime
    {A T : Type u} [CommRing A] [CommRing T] [Algebra A T]
    (p : PrimeSpectrum A) [IsLocalization.AtPrime T p.asIdeal]
    (hA : IsPRing P A) :
    IsPRing P T := by
  have hsource : IsPRing P (Localization.AtPrime p.asIdeal) :=
    isPRing_localizationAtPrime (P := P) hA p
  let e : Localization.AtPrime p.asIdeal ≃ₐ[A] T :=
    IsLocalization.algEquiv p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal) T
  let _ : Algebra (Localization.AtPrime p.asIdeal) T := e.toRingHom.toAlgebra
  let _ : Algebra.FiniteType (Localization.AtPrime p.asIdeal) T :=
    Algebra.FiniteType.of_surjective (R := Localization.AtPrime p.asIdeal) e.toAlgHom e.surjective
  let hfinite : e.toRingHom.Finite := by
    simpa [AlgHom.Finite, RingHom.Finite] using AlgHom.Finite.of_surjective e.toAlgHom e.surjective
  let _ : Algebra.QuasiFinite (Localization.AtPrime p.asIdeal) T :=
    RingHom.QuasiFinite.of_finite hfinite
  -- Proof comment: the chosen localization model is algebraically equivalent to the canonical
  -- localization, so the local step is a quasi-finite transfer from `A_p`.
  exact
    isPRing_of_quasiFinite (P := P) (R := Localization.AtPrime p.asIdeal) (R' := T) hsource

/-- Helper for Proposition 15.51.5: the finite-type case reduces to the polynomial source once a
surjective polynomial presentation is fixed. -/
lemma isPRing_of_surjective_mvPolynomial
    {T : Type u} [CommRing T] [Algebra R T]
    (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] T) (hα : Function.Surjective α)
    (hpoly : IsPRing P (MvPolynomial (Fin n) R)) :
    IsPRing P T := by
  let _ : IsNoetherianRing (MvPolynomial (Fin n) R) := hpoly.toIsNoetherian
  let _ : Module.Finite (MvPolynomial (Fin n) R) T :=
    Module.Finite.of_surjective (Algebra.linearMap (MvPolynomial (Fin n) R) T) hα
  let hfinite : α.toRingHom.Finite := by
    simpa [AlgHom.Finite, RingHom.Finite] using AlgHom.Finite.of_surjective α hα
  let _ : Algebra.QuasiFinite (MvPolynomial (Fin n) R) T :=
    RingHom.QuasiFinite.of_finite hfinite
  -- Proof comment: a surjective polynomial presentation is finite, hence quasi-finite, so
  -- Lemma `15.51.3` transfers the `P`-ring condition from the polynomial source to `T`.
  exact
    isPRing_of_quasiFinite (P := P) (R := MvPolynomial (Fin n) R) (R' := T) hpoly

/-- Helper for Proposition 15.51.5: a surjective one-variable polynomial presentation transfers
the `P`-ring property to the target algebra. -/
lemma isPRing_of_surjective_polynomial
    {B T : Type u} [CommRing B] [CommRing T] [Algebra B T]
    (α : Polynomial B →ₐ[B] T) (hα : Function.Surjective α)
    (hpoly : IsPRing P (Polynomial B)) :
    IsPRing P T := by
  let _ : IsNoetherianRing (Polynomial B) := hpoly.toIsNoetherian
  let _ : Module.Finite (Polynomial B) T :=
    Module.Finite.of_surjective (Algebra.linearMap (Polynomial B) T) hα
  let hfinite : α.toRingHom.Finite := by
    simpa [AlgHom.Finite, RingHom.Finite] using AlgHom.Finite.of_surjective α hα
  let _ : Algebra.QuasiFinite (Polynomial B) T :=
    RingHom.QuasiFinite.of_finite hfinite
  -- Proof comment: a surjective polynomial presentation is finite, hence quasi-finite, so
  -- Lemma `15.51.3` applies exactly as in the multivariable quotient step.
  exact
    isPRing_of_quasiFinite (P := P) (R := Polynomial B) (R' := T) hpoly

/-- Helper for Proposition 15.51.5: after contracting `q ⊂ A[X]` to `p ⊂ A`, the induced prime
of `(A_p)[X]` gives the canonical localization model of `A[X]_q`. -/
lemma polynomial_localization_compare_at_contracted_prime
    {A : Type u} [CommRing A] (q : PrimeSpectrum (Polynomial A)) :
    let p : PrimeSpectrum A := PrimeSpectrum.comap Polynomial.C q
    let Ap := Localization.AtPrime p.asIdeal
    let S := Polynomial Ap
    ∃ q' : PrimeSpectrum S,
      let _ : Algebra (Polynomial A) S :=
        (Polynomial.mapRingHom (algebraMap A Ap)).toAlgebra
      Nonempty (Localization.AtPrime q.asIdeal ≃ₐ[Polynomial A] Localization.AtPrime q'.asIdeal) := by
  let p : PrimeSpectrum A := PrimeSpectrum.comap Polynomial.C q
  let Ap := Localization.AtPrime p.asIdeal
  let S := Polynomial Ap
  let M : Submonoid (Polynomial A) := p.asIdeal.primeCompl.map Polynomial.C
  letI : Algebra (Polynomial A) S :=
    (Polynomial.mapRingHom (algebraMap A Ap)).toAlgebra
  letI : IsLocalization M S := Polynomial.isLocalization p.asIdeal.primeCompl Ap
  have hdisj : Disjoint (M : Set (Polynomial A)) q.asIdeal := by
    -- Proof comment: an element of `M` comes from a coefficient outside `p = q ∩ A`, so it
    -- cannot lie in `q`.
    refine Set.disjoint_left.mpr fun f hf hfq ↦ ?_
    rcases hf with ⟨g, hg, rfl⟩
    exact hg (by simpa [p] using hfq)
  let q' : PrimeSpectrum S := ⟨
    Ideal.map (algebraMap (Polynomial A) S) q.asIdeal,
    IsLocalization.isPrime_of_isPrime_disjoint M S q.asIdeal q.toPrimeSpectrum.2 hdisj⟩
  have hq' : Ideal.comap (algebraMap (Polynomial A) S) q'.asIdeal = q.asIdeal := by
    -- Proof comment: the chosen prime of `(A_p)[X]` is exactly the prime lying over `q`.
    simpa [q', PrimeSpectrum.asIdeal] using
      IsLocalization.comap_map_of_isPrime_disjoint M S q.toPrimeSpectrum.2 hdisj
  letI : IsLocalization.AtPrime (Localization.AtPrime q'.asIdeal) q.asIdeal := by
    -- Proof comment: once the comap is identified with `q`, both localizations are models of
    -- the same prime localization of `A[X]`.
    simpa [hq'] using
      (IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        M (Localization.AtPrime q'.asIdeal) q'.asIdeal)
  refine ⟨q', ?_⟩
  -- Proof comment: the universal property of localization now gives the comparison equivalence.
  exact
    ⟨IsLocalization.algEquiv q.asIdeal.primeCompl
      (Localization.AtPrime q.asIdeal) (Localization.AtPrime q'.asIdeal)⟩

/-- Helper for Proposition 15.51.5: once the base has been replaced by a local `P`-ring, its
maximal-ideal localization model already has the source formal fibers with property `P`. -/
lemma localization_at_maximal_formal_fibers_have_property_of_isPRing
    {A : Type u} [CommRing A] [IsLocalRing A] (hA : IsPRing P A) :
    LocalFormalFibersHaveProperty P (Localization.AtPrime (maximalIdeal A)) := by
  let _ : IsNoetherianRing A := hA.toIsNoetherian
  let m : MaximalSpectrum A := ⟨maximalIdeal A, inferInstance⟩
  have hlocal : IsPRing P (Localization.AtPrime m.asIdeal) :=
    isPRing_localizationAtPrime (P := P) hA m.toPrimeSpectrum
  -- Proof comment: Lemma `15.51.4` rewrites the `P`-ring condition on the maximal localization
  -- exactly as the formal-fiber condition needed in the local source square.
  exact
    (isPRing_localizationAtMaximal_iff_localFormalFibersHaveProperty
      (P := P) (m := m)).1 hlocal

/-- Helper for Proposition 15.51.5: if `A` is a local `P`-ring, then every fiber of the canonical
completed maximal localization `R̂_[m]` has property `P`. -/
lemma completed_maximal_localization_fibers_have_property_of_local_pRing
    {A : Type u} [CommRing A] [IsLocalRing A] (hA : IsPRing P A) :
    ∀ p : PrimeSpectrum A,
      P p.asIdeal.ResidueField
        (p.asIdeal.Fiber (R̂_[(⟨maximalIdeal A, inferInstance⟩ : MaximalSpectrum A).toPrimeSpectrum])) := by
  let m : MaximalSpectrum A := ⟨maximalIdeal A, inferInstance⟩
  have hformal :
      LocalFormalFibersHaveProperty P (Localization.AtPrime (maximalIdeal A)) :=
    localization_at_maximal_formal_fibers_have_property_of_isPRing
      (P := P) (A := A) hA
  have hprimePair :
      ∀ q : PrimeSpectrum A, q.asIdeal ≤ m.asIdeal →
        P q.asIdeal.ResidueField (q.asIdeal.Fiber (R̂_[m.toPrimeSpectrum])) :=
    (localFormalFibersHaveProperty_localizationAtMaximal_iff_primePair
      (P := P) (R := A) m).1 hformal
  intro p
  -- Proof comment: in a local ring every prime lies under the maximal ideal, so the maximal
  -- localization formal-fiber criterion specializes directly to the chosen prime.
  simpa [m] using hprimePair p p.asIdeal.le_maximalIdeal

/-- Helper for Proposition 15.51.5: the completion of a flat local map of Noetherian local rings
is faithfully flat. -/
lemma maximalIdealCompletionMap_faithfullyFlat_of_flat_local
    {A B : Type u} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    (f : A →+* B) [IsLocalHom f] (hf : f.Flat) :
    RingHom.FaithfullyFlat (maximalIdealCompletionMap f) := by
  have hcompletion_flat : (maximalIdealCompletionMap f).Flat := by
    -- Proof comment: completion preserves flatness for local maps of Noetherian local rings.
    exact (flat_iff_flat_maximalIdealCompletionMap f).2 hf
  let _ : IsLocalHom (maximalIdealCompletionMap f) := by infer_instance
  let _ :
      Module.Flat (AdicCompletion (maximalIdeal A) A) (AdicCompletion (maximalIdeal B) B) := by
    exact RingHom.flat_algebraMap_iff.mp <| by
      simpa [RingHom.algebraMap_toAlgebra] using hcompletion_flat
  -- Proof comment: a flat local map between local rings is faithfully flat, so the induced map on
  -- completions is ready for axiom `(D)`.
  simpa [RingHom.algebraMap_toAlgebra] using
    (RingHom.faithfullyFlat_algebraMap_iff.mpr
      (Module.FaithfullyFlat.of_flat_of_isLocalHom :
        Module.FaithfullyFlat (AdicCompletion (maximalIdeal A) A)
          (AdicCompletion (maximalIdeal B) B)))

/-- Helper for Proposition 15.51.5: scalar extension of a one-variable polynomial ring is the
tensor product model used by the source completion square. -/
noncomputable abbrev polynomial_tensor_algEquiv
    {A B : Type u} [CommSemiring A] [CommSemiring B] [Algebra A B] :
    TensorProduct A B (Polynomial A) ≃ₐ[B] Polynomial B :=
  -- Proof comment: rewrite one-variable polynomials as `MvPolynomial PUnit`, apply the standard
  -- tensor-base-change equivalence there, and then return to `Polynomial`.
  let e₁ :
      TensorProduct A B (Polynomial A) ≃ₐ[B] TensorProduct A B (MvPolynomial PUnit.{1} A) :=
    Algebra.TensorProduct.congr (AlgEquiv.refl (R := B) (A₁ := B))
      (MvPolynomial.pUnitAlgEquiv.{u, 0} A).symm
  let e₂ :
      TensorProduct A B (MvPolynomial PUnit.{1} A) ≃ₐ[B] MvPolynomial PUnit.{1} B :=
    MvPolynomial.algebraTensorAlgEquiv A B
  let e₃ : MvPolynomial PUnit.{1} B ≃ₐ[B] Polynomial B :=
    MvPolynomial.pUnitAlgEquiv.{u, 0} B
  e₁.trans (e₂.trans e₃)

/-- Helper for Proposition 15.51.5: after identifying `B[X]` with the tensor product
`B ⊗[A] A[X]`, the resulting comparison sends the canonical `A[X]`-algebra map to
`Polynomial.mapRingHom (A → B)`. -/
lemma polynomial_tensor_algEquiv_comp_algebraMap
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] :
    let e : TensorProduct A (Polynomial A) B ≃+* Polynomial B :=
      (Algebra.TensorProduct.commRight A (Polynomial A) B).toRingEquiv.trans
        (polynomial_tensor_algEquiv (A := A) (B := B)).toRingEquiv
    e.toRingHom.comp (algebraMap (Polynomial A) (TensorProduct A (Polynomial A) B)) =
      Polynomial.mapRingHom (algebraMap A B) := by
  -- Proof comment: the tensor-side map and the coefficient-wise polynomial map agree on
  -- constants and on `X`, so the polynomial universal property identifies them.
  apply Polynomial.ringHom_ext
  · intro a
    simp [polynomial_tensor_algEquiv]
  · simp [polynomial_tensor_algEquiv]

/-- Helper for Proposition 15.51.5: a finite type morphism induces an essentially finite type
extension on residue fields at every prime. -/
lemma residueField_extension_essFiniteType_of_finiteType
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    (q' : PrimeSpectrum B) :
    let q : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A B) q'
    Algebra.EssFiniteType q.asIdeal.ResidueField q'.asIdeal.ResidueField := by
  let q : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A B) q'
  let _ : Algebra.EssFiniteType B q'.asIdeal.ResidueField := inferInstance
  let _ : Algebra.EssFiniteType A q'.asIdeal.ResidueField :=
    Algebra.EssFiniteType.comp A B q'.asIdeal.ResidueField
  -- Proof comment: first view `κ(q')` as an essentially finite type `A`-algebra through `B`,
  -- then descend along the canonical factorization `A → κ(q) → κ(q')`.
  exact Algebra.EssFiniteType.of_comp A q.asIdeal.ResidueField q'.asIdeal.ResidueField

/-- Helper for Proposition 15.51.5: after contracting `t ⊂ Ap[X]` to `r ⊂ Ap`, axiom `(A)`
already gives property `P` for the explicit tensor-model fiber over `κ(t)`. -/
lemma polynomial_completion_baseChange_fiber_has_property
    {Ap Ahat : Type u} [CommRing Ap] [CommRing Ahat] [Algebra Ap Ahat]
    [IsNoetherianRing Ap] [IsNoetherianRing Ahat]
    (hAhat_fibers :
      ∀ r : PrimeSpectrum Ap,
        P r.asIdeal.ResidueField (r.asIdeal.Fiber Ahat))
    (t : PrimeSpectrum (Polynomial Ap)) :
    let r : PrimeSpectrum Ap := PrimeSpectrum.comap Polynomial.C t
    P t.asIdeal.ResidueField
      (t.asIdeal.ResidueField ⊗[r.asIdeal.ResidueField] (r.asIdeal.Fiber Ahat)) := by
  let r : PrimeSpectrum Ap := PrimeSpectrum.comap Polynomial.C t
  have hrt : Algebra.EssFiniteType r.asIdeal.ResidueField t.asIdeal.ResidueField := by
    -- Proof comment: `Ap → Ap[X]` is finite type, so the induced residue-field extension along
    -- `r = t ∩ Ap` is essentially finite type.
    simpa [r] using
      residueField_extension_essFiniteType_of_finiteType
        (A := Ap) (B := Polynomial Ap) t
  -- Proof comment: apply axiom `(A)` exactly to the source formal fiber `r.Fiber Ahat` and the
  -- residue-field extension `κ(r) → κ(t)`.
  exact
    FieldAlgebraProperty.HasPropertyA.baseChange
      (P := P) r.asIdeal.ResidueField (r.asIdeal.Fiber Ahat)
      t.asIdeal.ResidueField (hAhat_fibers r)

/-- Helper for Proposition 15.51.5: faithful flatness of `A → B` ascends to the induced
coefficient-extension map `A[X] → B[X]`. -/
lemma polynomial_mapRingHom_faithfullyFlat
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (hAB : RingHom.FaithfullyFlat (algebraMap A B)) :
    RingHom.FaithfullyFlat (Polynomial.mapRingHom (algebraMap A B)) := by
  let e : TensorProduct A (Polynomial A) B ≃+* Polynomial B :=
    (Algebra.TensorProduct.commRight A (Polynomial A) B).toRingEquiv.trans
      (polynomial_tensor_algEquiv (A := A) (B := B)).toRingEquiv
  let _ : Module.FaithfullyFlat A B := RingHom.faithfullyFlat_algebraMap_iff.mp hAB
  have htensor :
      Module.FaithfullyFlat (Polynomial A) (TensorProduct A (Polynomial A) B) :=
    Module.FaithfullyFlat.instTensorProduct (R := A) (M := B) (S := Polynomial A)
  let _ : Algebra (TensorProduct A (Polynomial A) B) (Polynomial B) := e.toRingHom.toAlgebra
  let _ : Module.FaithfullyFlat (TensorProduct A (Polynomial A) B) (Polynomial B) := by
    -- Proof comment: the tensor model and `B[X]` are ring-equivalent, hence faithfully flat over
    -- one another.
    exact RingHom.faithfullyFlat_algebraMap_iff.mp (RingHom.FaithfullyFlat.of_bijective e.bijective)
  have hEq :
      e.toRingHom.comp (algebraMap (Polynomial A) (TensorProduct A (Polynomial A) B)) =
        Polynomial.mapRingHom (algebraMap A B) :=
    polynomial_tensor_algEquiv_comp_algebraMap (A := A) (B := B)
  let _ : Algebra (Polynomial A) (Polynomial B) :=
    (Polynomial.mapRingHom (algebraMap A B)).toAlgebra
  have hTower :
      IsScalarTower (Polynomial A) (TensorProduct A (Polynomial A) B) (Polynomial B) := by
    -- Proof comment: the chosen tensor-side algebra structure composes back to the usual
    -- coefficient-wise polynomial map.
    refine @IsScalarTower.of_algebraMap_eq' (Polynomial A) (TensorProduct A (Polynomial A) B)
      (Polynomial B) _ _ _ _ _ _ hEq.symm
  let _ : IsScalarTower (Polynomial A) (TensorProduct A (Polynomial A) B) (Polynomial B) := hTower
  have hcomp : Module.FaithfullyFlat (Polynomial A) (Polynomial B) :=
    Module.FaithfullyFlat.trans (Polynomial A) (TensorProduct A (Polynomial A) B) (Polynomial B)
  -- Proof comment: faithful flatness first holds for the tensor model and then transfers across
  -- the comparison equivalence to the actual coefficient-extension map.
  exact RingHom.faithfullyFlat_algebraMap_iff.mpr hcomp

/-- Helper for Proposition 15.51.5: if the polynomial ring over a completed base is already a
`G`-ring, then every prime-local completion map on that polynomial ring is regular. -/
lemma localized_polynomial_completion_map_isRegularRingMap
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsGRing (Polynomial A)]
    (q : PrimeSpectrum (Polynomial A)) :
    (algebraMap (Localization.AtPrime q.asIdeal)
      (AdicCompletion (maximalIdeal (Localization.AtPrime q.asIdeal))
        (Localization.AtPrime q.asIdeal))).IsRegularRingMap := by
  -- Proof comment: once the polynomial ring is known to be a `G`-ring, the desired map is one of
  -- the defining regular localization-completion maps.
  simpa [CompletedLocalizationAtPrime] using
    (IsGRing.regular_localization_completion (R := Polynomial A) q)

/-- Helper for Proposition 15.51.5: the core one-variable step should identify the formal fibers
of `A[X]` with the source completion diagram and apply axioms `(A)` through `(D)`. -/
lemma isPRing_polynomial
    {A : Type u} [CommRing A] (hA : IsPRing P A) :
    IsPRing P (Polynomial A) := by
  let _ : IsNoetherianRing A := hA.toIsNoetherian
  -- Route correction: first carry out the source reduction to a maximal ideal of `A[X]`, contract
  -- it to `A`, and replace the base by the local ring `A_p`. The only remaining blocker is then
  -- the source-faithful local completion square over that local base.
  rw [isPRing_iff_localFormalFibersHaveProperty_atMaximal]
  intro q
  let p : PrimeSpectrum A := PrimeSpectrum.comap Polynomial.C q.toPrimeSpectrum
  let Ap := Localization.AtPrime p.asIdeal
  let S := Polynomial Ap
  let mAp : MaximalSpectrum Ap := ⟨maximalIdeal Ap, inferInstance⟩
  let Ahat := R̂_[mAp.toPrimeSpectrum]
  have hlocal : IsPRing P Ap :=
    isPRing_of_localization_model_atPrime (P := P) (A := A) (T := Ap) p hA
  let _ : IsLocalRing Ap := inferInstance
  let _ : IsPRing P Ap := hlocal
  have hAhat_fibers :
      ∀ r : PrimeSpectrum Ap,
        P r.asIdeal.ResidueField (r.asIdeal.Fiber Ahat) :=
    completed_maximal_localization_fibers_have_property_of_local_pRing
      (P := P) (A := Ap) hlocal
  have hcompare :
      ∃ q' : PrimeSpectrum S,
        Nonempty (Localization.AtPrime q.asIdeal ≃ₐ[Polynomial A] Localization.AtPrime q'.asIdeal) := by
    -- Proof comment: this is the source reduction from `A[X]_q` to the corresponding
    -- localization of `(A_p)[X]`.
    simpa [p, Ap, S] using
      polynomial_localization_compare_at_contracted_prime (A := A) q.toPrimeSpectrum
  obtain ⟨q', ⟨e⟩⟩ := hcompare
  let _ := e
  let _ := hAhat_fibers
  have hcompletion_ff :
      RingHom.FaithfullyFlat (algebraMap Ap Ahat) := by
    simpa [RingHom.algebraMap_toAlgebra] using
      maximalIdeal_adicCompletion_algebraMap_faithfullyFlat Ap
  have hpoly_ff :
      RingHom.FaithfullyFlat (algebraMap (Polynomial Ap) (Polynomial Ahat)) := by
    simpa [RingHom.algebraMap_toAlgebra] using
      polynomial_mapRingHom_faithfullyFlat (A := Ap) (B := Ahat) hcompletion_ff
  have hpoly_tensor :
      ∀ t : PrimeSpectrum (Polynomial Ap),
        let r : PrimeSpectrum Ap := PrimeSpectrum.comap Polynomial.C t
        P t.asIdeal.ResidueField
          (t.asIdeal.ResidueField ⊗[r.asIdeal.ResidueField] (r.asIdeal.Fiber Ahat)) := by
    intro t
    -- Proof comment: this is the source sentence saying the lower horizontal fibers have `P`
    -- before identifying the explicit tensor model with the actual polynomial fiber.
    simpa using
      polynomial_completion_baseChange_fiber_has_property
        (P := P) (Ap := Ap) (Ahat := Ahat) hAhat_fibers t
  obtain ⟨qhat, hqhat⟩ :=
    (PrimeSpectrum.comap_surjective_of_faithfullyFlat
      (A := Polynomial Ap) (B := Polynomial Ahat)) q'
  let _ := qhat
  let _ := hqhat
  -- Proof comment: at this point the global reduction is complete. The remaining local goal is
  -- exactly the textbook square for the local `P`-ring `A_p`, the canonical completed maximal
  -- localization `Ahat`, the comparison prime `q' ⊂ (A_p)[X]`, the lifted prime
  -- `qhat ⊂ Ahat[X]`, and the localization equivalence `e : A[X]_q ≃ ((A_p)[X])_{q'}`.
  -- TODO: the new frontier is now explicit. `hpoly_tensor` proves the source-theorem tensor model
  -- `κ(t) ⊗[κ(r)] (r.Fiber Ahat)` has property `P` for every `t ⊂ Ap[X]`. The remaining blocker
  -- is the missing owner-level bridge from that tensor model to the actual fiber
  -- `t.asIdeal.Fiber (Polynomial Ahat)`: the available comparison is an algebra equivalence, but
  -- the current API for a generic `FieldAlgebraProperty` does not yet transport `P` across such
  -- equivalences. After that bridge is supplied, clause `(1) → (2)` of Lemma `15.51.2` gives the
  -- localized lower-horizontal fibers, and the final `(C)`/`(D)` square argument can follow the
  -- same pattern as `completion_maximal_localFiber_hasProperty`.
  sorry

/-- Helper for Proposition 15.51.5: finite polynomial algebras over a `P`-ring should again be
`P`-rings. -/
lemma isPRing_mvPolynomial_fin
    {A : Type u} [CommRing A] (hA : IsPRing P A) (n : ℕ) :
    IsPRing P (MvPolynomial (Fin n) A) := by
  -- Route correction: the source proof first proves the one-variable polynomial case by the
  -- local formal-fiber diagram, then iterates that result through the standard finite-variable
  -- decomposition of `MvPolynomial`.
  induction n with
  | zero =>
      let e : A ≃ₐ[A] MvPolynomial (Fin 0) A := (MvPolynomial.isEmptyAlgEquiv A (Fin 0)).symm
      let _ : Algebra.FiniteType A (MvPolynomial (Fin 0) A) :=
        Algebra.FiniteType.of_surjective (R := A) e.toAlgHom e.surjective
      let hfinite : e.toRingHom.Finite := by
        simpa [AlgHom.Finite, RingHom.Finite] using
          AlgHom.Finite.of_surjective e.toAlgHom e.surjective
      let _ : Algebra.QuasiFinite A (MvPolynomial (Fin 0) A) :=
        RingHom.QuasiFinite.of_finite hfinite
      -- Proof comment: the empty-variable polynomial ring is just a quasi-finite copy of `A`.
      exact isPRing_of_quasiFinite (P := P) (R := A) (R' := MvPolynomial (Fin 0) A) hA
  | succ n ih =>
      have hpoly : IsPRing P (Polynomial (MvPolynomial (Fin n) A)) :=
        isPRing_polynomial (P := P) ih
      let α : Polynomial (MvPolynomial (Fin n) A) →ₐ[MvPolynomial (Fin n) A]
          MvPolynomial (Fin (n + 1)) A :=
        (MvPolynomial.finSuccEquiv A n).symm.toAlgHom
      have hα : Function.Surjective α := (MvPolynomial.finSuccEquiv A n).symm.surjective
      -- Proof comment: the successor stage is the canonical one-variable polynomial presentation
      -- of `MvPolynomial (Fin (n + 1)) A`.
      exact isPRing_of_surjective_polynomial (P := P) α hα hpoly

/-- Helper for Proposition 15.51.5: once the polynomial case is known, every finite type
algebra over a `P`-ring is again a `P`-ring. -/
lemma isPRing_of_finiteType
    {T : Type u} [CommRing T] [Algebra R T] [Algebra.FiniteType R T]
    (hR : IsPRing P R) :
    IsPRing P T := by
  let _ : IsNoetherianRing R := hR.toIsNoetherian
  obtain ⟨n, α, hα⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'').1
      (inferInstance : Algebra.FiniteType R T)
  have hpoly : IsPRing P (MvPolynomial (Fin n) R) :=
    isPRing_mvPolynomial_fin (P := P) hR n
  -- Proof comment: choose one surjective polynomial presentation of the finite-type algebra and
  -- push the polynomial `P`-ring property across that quasi-finite quotient map.
  exact isPRing_of_surjective_mvPolynomial (P := P) n α hα hpoly

/-- Helper for Proposition 15.51.5: after replacing an essentially finite type target by the
canonical finite type subalgebra inside it, the remaining step is to transfer the `P`-ring
condition across the localization model. -/
lemma isPRing_of_essFiniteType_subalgebra
    (hR : IsPRing P R)
    (hA : IsPRing P (Algebra.EssFiniteType.subalgebra R S)) :
    IsPRing P S := by
  let A := Algebra.EssFiniteType.subalgebra R S
  let _ : IsNoetherianRing R := hR.toIsNoetherian
  let _ : IsNoetherianRing S := Algebra.EssFiniteType.isNoetherianRing R S
  let _ : Algebra R A := A.algebra
  let _ : Algebra A S := inferInstance
  -- Proof comment: reduce the localization target `S` to its prime localizations, exactly as in
  -- the source reduction from essentially finite type to the finite-type model.
  refine isPRing_of_localizationsAtPrime (P := P) ?_
  intro p
  let q : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A S) p
  letI : IsLocalization.AtPrime (Localization.AtPrime p.asIdeal) q.asIdeal := by
    -- Proof comment: the prime localization of the localization model is another model for the
    -- same prime localization of the finite-type subalgebra.
    simpa [q] using
      (IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        (Algebra.EssFiniteType.submonoid R S)
        (Localization.AtPrime p.asIdeal) p.asIdeal)
  -- Proof comment: once `S_p` is recognized as a prime-localization model of the finite-type
  -- subalgebra, the reusable localization-model transfer closes the local step.
  exact isPRing_of_localization_model_atPrime (P := P) (A := A) (T := Localization.AtPrime p.asIdeal) q hA

-- Proof sketch: reduce by `isPRing_iff_localFormalFibersHaveProperty_atMaximal` to the local
-- rings `S_m` at maximal ideals of `S`. Present each `S_m` as essentially finite type over the
-- corresponding localization of `R`, use the quasi-finite permanence theorem `isPRing_of_quasiFinite`
-- from Lemma `15.51.3` together with axioms `(A)` and `(B)` to handle the finite-type part, and
-- then apply axioms `(C)` and `(D)` through Lemma `15.51.4` to descend the comparison on formal
-- fibers.
/-- Proposition 15.51.5: if `R` is a `P`-ring and `R → S` is essentially of finite type, where
`P` satisfies `(A)`, `(B)`, `(C)`, and `(D)`, then `S` is again a `P`-ring. -/
theorem isPRing_of_essFiniteType
    (hR : IsPRing P R) :
    IsPRing P S := by
  let A := Algebra.EssFiniteType.subalgebra R S
  let _ : Algebra R A := A.algebra
  let _ : Algebra.FiniteType R A := inferInstance
  have hA : IsPRing P A :=
    isPRing_of_finiteType (P := P) (R := R) hR
  -- Proof comment: after proving the canonical finite-type model is a `P`-ring, only the
  -- localization step from that model to `S` remains.
  simpa [A] using isPRing_of_essFiniteType_subalgebra (P := P) (R := R) (S := S) hR hA

end
