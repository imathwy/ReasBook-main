import StacksProject_2024.Chap10.Lemma_10_118_7.CyclicQuotientTransport

universe u v w

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module S M]

namespace GenericFlatness

/-- Helper for Lemma 10.118.7: localizing the coefficients preserves monicity of the defining
polynomial. -/
lemma map_monic_localizationAway
    {A : Type*} [CommRing A] [Algebra R A] {q : Polynomial A} (hq : q.Monic) (f : R) :
    (Polynomial.map (algebraMap A (Localization.Away (algebraMap R A f))) q).Monic := by
  -- A monic polynomial stays monic after applying the coefficient map to the localized ring.
  simpa using hq.map (algebraMap A (Localization.Away (algebraMap R A f)))

/-- Helper for Lemma 10.118.7: after localizing the coefficients, the single-equation quotient is
still finitely presented over the ambient localized polynomial ring. -/
theorem localized_polynomial_singleton_quotient_finitePresentation_over_polynomial
    {A : Type*} [CommRing A] [Algebra R A] (q : Polynomial A) (f : R) :
    Module.FinitePresentation (Polynomial (Localization.Away (algebraMap R A f)))
      (Polynomial (Localization.Away (algebraMap R A f)) ⧸
        Ideal.span
          ({Polynomial.map (algebraMap A (Localization.Away (algebraMap R A f))) q} : Set _)) := by
  -- This is the same one-equation quotient lemma, applied after localizing the coefficient ring.
  simpa using
    (polynomial_singleton_quotient_finitePresentation_over_polynomial
      (A := Localization.Away (algebraMap R A f))
      (q := Polynomial.map (algebraMap A (Localization.Away (algebraMap R A f))) q))

/-- Helper for Lemma 10.118.7: after localizing the coefficients, a monic one-equation quotient is
free over the localized coefficient ring. -/
theorem localized_monic_polynomial_quotient_free_over_base
    {A : Type*} [CommRing A] [Algebra R A] {q : Polynomial A} (hq : q.Monic) (f : R) :
    Module.Free (Localization.Away (algebraMap R A f))
      (Polynomial (Localization.Away (algebraMap R A f)) ⧸
        Ideal.span
          ({Polynomial.map (algebraMap A (Localization.Away (algebraMap R A f))) q} : Set _)) := by
  -- Move to the localized coefficient ring and reuse the monic quotient freeness theorem there.
  simpa using
    (monic_polynomial_quotient_free_over_base
      (A := Localization.Away (algebraMap R A f))
      (q := Polynomial.map (algebraMap A (Localization.Away (algebraMap R A f))) q)
      (map_monic_localizationAway (R := R) (A := A) hq f))

/-- Helper for Lemma 10.118.7: after localizing the coefficients, a monic one-equation quotient is
finitely presented over the localized coefficient ring. -/
theorem localized_monic_polynomial_quotient_finitePresentation_over_base
    {A : Type*} [CommRing A] [Algebra R A] {q : Polynomial A} (hq : q.Monic) (f : R) :
    Module.FinitePresentation (Localization.Away (algebraMap R A f))
      (Polynomial (Localization.Away (algebraMap R A f)) ⧸
        Ideal.span
          ({Polynomial.map (algebraMap A (Localization.Away (algebraMap R A f))) q} : Set _)) := by
  -- Move to the localized coefficient ring and reuse the monic quotient finite-presentation
  -- theorem there.
  simpa using
    (monic_polynomial_quotient_finitePresentation_over_base
      (A := Localization.Away (algebraMap R A f))
      (q := Polynomial.map (algebraMap A (Localization.Away (algebraMap R A f))) q)
      (map_monic_localizationAway (R := R) (A := A) hq f))

/-- Helper for Lemma 10.118.7: the localized module `B_(f)` carries the expected scalar tower from
`R_f` through `B_f`. -/
instance localized_away_module_isScalarTower
    {B : Type*} [CommRing B] [Algebra R B] (f : R) :
    IsScalarTower (Localization.Away f) (Localization.Away (algebraMap R B f))
      (LocalizedModule.Away (algebraMap R B f) B) := by
  -- The `R_f`-action was defined by restriction of scalars along `R_f → B_f`, so the two scalar
  -- actions agree definitionally once we unfold that comparison map.
  refine IsScalarTower.of_algebraMap_eq ?_
  intro r
  rfl

/-- Helper for Lemma 10.118.7: every localized `B`-module carries the expected scalar tower from
`R_f` through `B_f`. -/
instance localized_away_moduleTarget_isScalarTower
    {B : Type*} [CommRing B] [Algebra R B]
    {N : Type*} [AddCommGroup N] [Module B N] (f : R) :
    IsScalarTower (Localization.Away f) (Localization.Away (algebraMap R B f))
      (LocalizedModule.Away (algebraMap R B f) N) := by
  -- The localized `R_f`-action on any `B`-module is induced through `B_f`, so the tower law is
  -- just `mul_smul` after rewriting the intermediate scalar action on `B_f`.
  refine ⟨?_⟩
  intro r s x
  change ((algebraMap (Localization.Away f) (Localization.Away (algebraMap R B f)) r) * s) • x =
    (algebraMap (Localization.Away f) (Localization.Away (algebraMap R B f)) r) • (s • x)
  simpa using
    (mul_smul
      (algebraMap (Localization.Away f) (Localization.Away (algebraMap R B f)) r)
      s x)

/-- Helper for Lemma 10.118.7: the localized cyclic quotient module agrees with the canonical
localized monic-quotient model after passing through the quotient of the localized polynomial ring. -/
private noncomputable abbrev localized_cyclic_quotient_module_linearEquiv
    {A : Type*} [CommRing A] [Algebra R A] (q : Polynomial A) (f : R) :
    LocalizedModule.Away (algebraMap R (Polynomial A) f)
      (Polynomial A ⧸ Ideal.span ({q} : Set (Polynomial A))) ≃ₗ[Localization.Away f]
      (Polynomial (Localization.Away (algebraMap R A f)) ⧸
        Ideal.span
          ({Polynomial.map (algebraMap A (Localization.Away (algebraMap R A f))) q} : Set _)) :=
  -- Restrict scalars along `R_f → (A[X])_f` using the stabilized scalar tower on the transported
  -- target quotient.
  LinearEquiv.restrictScalars (Localization.Away f)
    (localized_cyclic_quotient_module_linearEquiv_over_source
      (R := R) (A := A) q f)

/-- Helper for Lemma 10.118.7: before transporting to the localized-coefficient model, the
localized cyclic quotient is finitely presented over the localized source polynomial ring because
it is a one-equation quotient of that ring. -/
theorem localized_cyclic_quotient_source_finitePresentation_over_source
    {A : Type*} [CommRing A] [Algebra R A] (q : Polynomial A) (f : R) :
    Module.FinitePresentation (Localization.Away (algebraMap R (Polynomial A) f))
      (Localization.Away (algebraMap R (Polynomial A) f) ⧸
        Ideal.map
          (algebraMap (Polynomial A)
            (Localization.Away (algebraMap R (Polynomial A) f)))
          (Ideal.span ({q} : Set (Polynomial A)))) := by
  let B := Localization.Away (algebraMap R (Polynomial A) f)
  let P : Ideal B :=
    Ideal.map
      (algebraMap (Polynomial A) B)
      (Ideal.span ({q} : Set (Polynomial A)))
  let _ : Module.Finite B (B ⧸ P) :=
    -- The quotient is cyclic over the localized source ring.
    Module.Finite.of_surjective
      (Algebra.linearMap B (B ⧸ P))
      (Ideal.Quotient.mk_surjective (I := P))
  let _ : Algebra.FinitePresentation B B :=
    Algebra.FinitePresentation.self B
  let _ : Algebra.FinitePresentation B (B ⧸ P) := by
    -- The localized relation ideal is still generated by the image of the single polynomial `q`.
    exact Algebra.FinitePresentation.quotient (R := B) (A := B) <| by
      simpa [P, Ideal.map_span, Set.image_singleton] using
        (Submodule.fg_span_singleton (R := B) (algebraMap (Polynomial A) B q))
  -- Finite plus finitely presented algebra yields finite presentation as a module.
  exact Module.FinitePresentation.of_finite_of_finitePresentation (R := B) (S := B ⧸ P)

/-- Helper for Lemma 10.118.7: transporting the localized cyclic quotient through the
localized-polynomial comparison preserves finite presentation over the localized source polynomial
ring. -/
theorem localized_cyclic_quotient_target_finitePresentation_over_source
    {A : Type*} [CommRing A] [Algebra R A] (q : Polynomial A) (f : R) :
    Module.FinitePresentation (Localization.Away (algebraMap R (Polynomial A) f))
      (Polynomial (Localization.Away (algebraMap R A f)) ⧸
        Ideal.span
          ({Polynomial.map (algebraMap A (Localization.Away (algebraMap R A f))) q} : Set _)) := by
  let _ : Module.FinitePresentation
      (Localization.Away (algebraMap R (Polynomial A) f))
      (Localization.Away (algebraMap R (Polynomial A) f) ⧸
        Ideal.map
          (algebraMap (Polynomial A)
            (Localization.Away (algebraMap R (Polynomial A) f)))
          (Ideal.span ({q} : Set (Polynomial A)))) :=
    localized_cyclic_quotient_source_finitePresentation_over_source
      (R := R) (A := A) q f
  -- Transfer finite presentation across the localized quotient transport equivalence.
  exact Module.FinitePresentation.of_equiv
    ((localized_cyclic_quotient_transport_algEquiv_over_source
      (R := R) (A := A) q f).toLinearEquiv)

/-- Helper for Lemma 10.118.7: the localized module of the cyclic quotient is finitely presented
over the localized source polynomial ring after identifying it with the canonical localized
quotient model. -/
theorem localized_cyclic_quotient_module_finitePresentation_over_source
    {A : Type*} [CommRing A] [Algebra R A] (q : Polynomial A) (f : R) :
    Module.FinitePresentation (Localization.Away (algebraMap R (Polynomial A) f))
      (LocalizedModule.Away (algebraMap R (Polynomial A) f)
        (Polynomial A ⧸ Ideal.span ({q} : Set (Polynomial A)))) := by
  let _ : Module.FinitePresentation
      (Localization.Away (algebraMap R (Polynomial A) f))
      (Polynomial (Localization.Away (algebraMap R A f)) ⧸
        Ideal.span
          ({Polynomial.map (algebraMap A (Localization.Away (algebraMap R A f))) q} : Set _)) :=
    localized_cyclic_quotient_target_finitePresentation_over_source
      (R := R) (A := A) q f
  -- Transport the finite-presentation structure back along the localized module comparison.
  exact Module.FinitePresentation.of_equiv
    (localized_cyclic_quotient_module_linearEquiv_over_source
      (R := R) (A := A) q f).symm


/-- Helper for Lemma 10.118.7: the localized module of `B` agrees with the localized ring as a
`B`-module. -/
noncomputable abbrev localized_self_module_linearEquiv_over_base
    {B : Type*} [CommRing B] [Algebra R B] (f : R) :
    LocalizedModule.Away (algebraMap R B f) B ≃ₗ[B]
      Localization.Away (algebraMap R B f) :=
  IsLocalizedModule.linearEquiv
    (.powers (algebraMap R B f))
    (LocalizedModule.mkLinearMap (.powers (algebraMap R B f)) B)
    (Algebra.linearMap B (Localization.Away (algebraMap R B f)))

/-- Helper for Lemma 10.118.7: the owner localized self-module comparison sends the canonical
generator `b / 1` to the corresponding localized ring element. -/
@[simp] theorem localized_self_module_linearEquiv_over_base_apply_mk_one
    {B : Type*} [CommRing B] [Algebra R B] (f : R) (b : B) :
    localized_self_module_linearEquiv_over_base (R := R) (B := B) f (LocalizedModule.mk b 1) =
      algebraMap B (Localization.Away (algebraMap R B f)) b := by
  -- Evaluate the owner localization comparison on the generator `b / 1`.
  simpa [localized_self_module_linearEquiv_over_base] using
    (IsLocalizedModule.linearEquiv_apply
      (.powers (algebraMap R B f))
      (LocalizedModule.mkLinearMap (.powers (algebraMap R B f)) B)
      (Algebra.linearMap B (Localization.Away (algebraMap R B f)))
      b)

/-- Helper for Lemma 10.118.7: localizing a ring considered as a module over itself is the
localized ring, viewed by restriction of scalars from `B_(f)` to `R_f`. -/
noncomputable abbrev localized_self_module_linearEquiv
    {B : Type*} [CommRing B] [Algebra R B] (f : R) :
    LocalizedModule.Away (algebraMap R B f) B ≃ₗ[Localization.Away f]
      Localization.Away (algebraMap R B f) :=
  -- First upgrade the owner `B`-linear equivalence to a `B_f`-linear one, then restrict scalars
  -- along the canonical map `R_f → B_f`.
  LinearEquiv.restrictScalars (Localization.Away f)
    (LinearEquiv.extendScalarsOfIsLocalization
      (.powers (algebraMap R B f))
      (Localization.Away (algebraMap R B f))
      (localized_self_module_linearEquiv_over_base (R := R) (B := B) f))

/-- Helper for Lemma 10.118.7: restricting scalars on the localized self-module equivalence does
not change its underlying function. -/
@[simp] private theorem localized_self_module_linearEquiv_apply
    {B : Type*} [CommRing B] [Algebra R B] (f : R)
    (x : LocalizedModule.Away (algebraMap R B f) B) :
    localized_self_module_linearEquiv (R := R) (B := B) f x =
      localized_self_module_linearEquiv_over_base (R := R) (B := B) f x := by
  -- The restricted-scalars wrapper keeps the same underlying function.
  rfl

/-- Helper for Lemma 10.118.7: the localized self-module equivalence sends the canonical class
`b / 1` to the corresponding element of the localized ring. -/
@[simp] theorem localized_self_module_linearEquiv_apply_mk_one
    {B : Type*} [CommRing B] [Algebra R B] (f : R) (b : B) :
    localized_self_module_linearEquiv (R := R) (B := B) f (LocalizedModule.mk b 1) =
      algebraMap B (Localization.Away (algebraMap R B f)) b := by
  -- The restricted-scalars wrapper has the same underlying function as the owner comparison.
  simpa [localized_self_module_linearEquiv] using
    localized_self_module_linearEquiv_over_base_apply_mk_one (R := R) (B := B) f b

/-- Helper for Lemma 10.118.7: once a localized module is viewed as an `R`-module by restriction
of scalars along `R → R_f`, it lies in the expected scalar tower `R → R_f → N_f`. -/
private theorem localized_away_moduleTarget_isScalarTower_over_base
    {B : Type*} [CommRing B] [Algebra R B]
    {N : Type*} [AddCommGroup N] [Module B N] (f : R) :
    let _ : Module R (LocalizedModule.Away (algebraMap R B f) N) :=
      Module.compHom (LocalizedModule.Away (algebraMap R B f) N)
        (algebraMap R (Localization.Away f))
    IsScalarTower R (Localization.Away f)
      (LocalizedModule.Away (algebraMap R B f) N) := by
  let _ : Module R (LocalizedModule.Away (algebraMap R B f) N) :=
    Module.compHom (LocalizedModule.Away (algebraMap R B f) N)
      (algebraMap R (Localization.Away f))
  -- The restricted `R`-action is defined by composing through `R_f`, so the scalar tower is
  -- just `mul_smul` after rewriting the two scalar actions.
  refine ⟨?_⟩
  intro r s x
  simpa [Module.compHom, Algebra.smul_def] using
    (mul_smul (algebraMap R (Localization.Away f) r) s x)

/-- Helper for Lemma 10.118.7: a surjective polynomial presentation makes the target algebra
finite as a module over the polynomial ring. -/
theorem moduleFinite_of_surjective_mvPolynomial_presentation
    {n : ℕ} (π : MvPolynomial (Fin n) R →ₐ[R] S) (hπ : Function.Surjective π) :
    let _ : Algebra (MvPolynomial (Fin n) R) S := π.toAlgebra
    Module.Finite (MvPolynomial (Fin n) R) S := by
  let _ : Algebra (MvPolynomial (Fin n) R) S := π.toAlgebra
  -- The polynomial presentation map is surjective, so the target is cyclic over the source ring.
  exact Module.Finite.of_surjective
    (Algebra.linearMap (MvPolynomial (Fin n) R) S) hπ

end GenericFlatness

end
