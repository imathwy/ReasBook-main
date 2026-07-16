import stacks_proof.stacks_project.Chap10.Lemma_10_118_7.PolynomialLocalization
import stacks_proof.stacks_project.Chap10.Lemma_10_30_2

universe u v w

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module S M]

namespace GenericFlatness

/-- Helper for Lemma 10.118.7: transporting the localized principal relation ideal through the
localized polynomial comparison identifies it with the singleton span of the mapped polynomial. -/
lemma localized_quotient_ideal_map_eq_mapped_singleton_span
    {A : Type*} [CommRing A] [Algebra R A] (q : Polynomial A) (f : R) :
    Ideal.map (localized_polynomial_algEquiv (R := R) (A := A) f).toRingHom
      (Ideal.map (algebraMap (Polynomial A)
        (Localization.Away (algebraMap R (Polynomial A) f)))
        (Ideal.span ({q} : Set (Polynomial A)))) =
      Ideal.span
        ({Polynomial.map (algebraMap A (Localization.Away (algebraMap R A f))) q} : Set _) := by
  -- Push the principal ideal through the two ring maps and then normalize the unique generator.
  rw [Ideal.map_map, Ideal.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases Set.mem_singleton_iff.mp hy with rfl
    -- The composed image of the generator is the mapped polynomial from the previous lemma.
    simpa using localized_polynomial_algEquiv_algebraMap (R := R) (A := A) f y
  · rintro rfl
    exact ⟨q, Set.mem_singleton q,
      localized_polynomial_algEquiv_algebraMap (R := R) (A := A) f q⟩

/-- Helper for Lemma 10.118.7: in the cyclic quotient, the image of the powers of
`algebraMap R (Polynomial A) f` is exactly the powers of the image of `f` in the quotient. -/
lemma quotient_polynomial_algebraMapSubmonoid_powers_eq
    {A : Type*} [CommRing A] [Algebra R A] (q : Polynomial A) (f : R) :
    Algebra.algebraMapSubmonoid
      (Polynomial A ⧸ Ideal.span ({q} : Set (Polynomial A)))
      (Submonoid.powers (algebraMap R (Polynomial A) f)) =
        Submonoid.powers
          (algebraMap R (Polynomial A ⧸ Ideal.span ({q} : Set (Polynomial A))) f) := by
  -- The quotient map commutes with the base-ring algebra map, so images of powers stay powers.
  simpa only [IsScalarTower.algebraMap_eq R (Polynomial A)
      (Polynomial A ⧸ Ideal.span ({q} : Set (Polynomial A)))] using
    (Algebra.algebraMapSubmonoid_powers
      (R := Polynomial A)
      (S := Polynomial A ⧸ Ideal.span ({q} : Set (Polynomial A)))
      (algebraMap R (Polynomial A) f))

/-- Helper for Lemma 10.118.7: after transporting the localized relation ideal across the
localized polynomial comparison, both quotient rings lie over the same ideal of `R`. -/
lemma localized_cyclic_quotient_transport_comap_eq
    {A : Type*} [CommRing A] [Algebra R A] (q : Polynomial A) (f : R) :
    Ideal.comap
        (algebraMap R
          (Localization.Away (algebraMap R (Polynomial A) f)))
        (Ideal.map
          (algebraMap (Polynomial A)
            (Localization.Away (algebraMap R (Polynomial A) f)))
          (Ideal.span ({q} : Set (Polynomial A)))) =
      Ideal.comap
        (algebraMap R (Polynomial (Localization.Away (algebraMap R A f))))
        (Ideal.span
          ({Polynomial.map (algebraMap A (Localization.Away (algebraMap R A f))) q} : Set _)) := by
  let e := localized_polynomial_algEquiv (R := R) (A := A) f
  let P : Ideal (Localization.Away (algebraMap R (Polynomial A) f)) :=
    Ideal.map
      (algebraMap (Polynomial A)
        (Localization.Away (algebraMap R (Polynomial A) f)))
      (Ideal.span ({q} : Set (Polynomial A)))
  let Q : Ideal (Polynomial (Localization.Away (algebraMap R A f))) :=
    Ideal.span
      ({Polynomial.map (algebraMap A (Localization.Away (algebraMap R A f))) q} : Set _)
  have hQ : Ideal.map e.toRingHom P = Q :=
    localized_quotient_ideal_map_eq_mapped_singleton_span (R := R) (A := A) q f
  have hcomp :
      e.toRingHom.comp
          (algebraMap R (Localization.Away (algebraMap R (Polynomial A) f))) =
        algebraMap R (Polynomial (Localization.Away (algebraMap R A f))) := by
    ext x n
    simpa using
      congrArg
        (fun p : Polynomial (Localization.Away (algebraMap R A f)) ↦ p.coeff n)
        (e.commutes x)
  -- Rewrite the target contraction through the polynomial-localization equivalence, then cancel
  -- the inverse-image of the mapped ideal using bijectivity of the equivalence.
  symm
  calc
    Ideal.comap
        (algebraMap R (Polynomial (Localization.Away (algebraMap R A f))))
        Q =
      Ideal.comap
        (algebraMap R (Localization.Away (algebraMap R (Polynomial A) f)))
        (Ideal.comap e.toRingHom Q) := by
        rw [← hcomp, Ideal.comap_comap]
    _ =
      Ideal.comap
        (algebraMap R (Localization.Away (algebraMap R (Polynomial A) f)))
        P := by
        rw [← hQ, Ideal.comap_map_of_bijective e.toRingHom e.bijective]

/-- Helper for Lemma 10.118.7: the quotient of the localized polynomial ring carries the canonical
algebra structure from the cyclic quotient `A[X] / (q)`. -/
@[reducible]
private noncomputable def localized_cyclic_quotient_target_quotient_algebra
    {A : Type*} [CommRing A] [Algebra R A] (q : Polynomial A) (f : R) :
    Algebra (Polynomial A ⧸ Ideal.span ({q} : Set (Polynomial A)))
      (Localization.Away (algebraMap R (Polynomial A) f) ⧸
        Ideal.map
          (algebraMap (Polynomial A)
            (Localization.Away (algebraMap R (Polynomial A) f)))
          (Ideal.span ({q} : Set (Polynomial A)))) :=
  Ideal.Quotient.algebraQuotientMapQuotient

/-- Helper for Lemma 10.118.7: Proposition `10.9.14` specialized to the cyclic quotient localizes
the quotient before any transport to the localized-polynomial model. -/
private noncomputable abbrev localized_cyclic_quotient_localization_algEquiv
    {A : Type*} [CommRing A] [Algebra R A] (q : Polynomial A) (f : R) :
    Localization.Away
        (algebraMap R (Polynomial A ⧸ Ideal.span ({q} : Set (Polynomial A))) f) ≃ₐ[R]
      Localization.Away (algebraMap R (Polynomial A) f) ⧸
        Ideal.map
          (algebraMap (Polynomial A)
            (Localization.Away (algebraMap R (Polynomial A) f)))
          (Ideal.span ({q} : Set (Polynomial A))) := by
  let I : Ideal (Polynomial A) := Ideal.span ({q} : Set (Polynomial A))
  let T :=
    Localization.Away (algebraMap R (Polynomial A) f) ⧸
      Ideal.map
        (algebraMap (Polynomial A)
          (Localization.Away (algebraMap R (Polynomial A) f)))
        I
  let hAlg : Algebra (Polynomial A ⧸ I) T :=
    localized_cyclic_quotient_target_quotient_algebra (R := R) (A := A) q f
  letI : Algebra (Polynomial A ⧸ I) T :=
    hAlg
  letI : SMul (Polynomial A ⧸ I) T := hAlg.toSMul
  letI : Module (Polynomial A ⧸ I) T := Algebra.toModule
  let hTower : IsScalarTower R (Polynomial A ⧸ I) T := by
    -- Compare the two composites `R → A[X] / (q) → (A[X])_f / (q)` and `R → (A[X])_f / (q)` on
    -- quotient generators.
    refine IsScalarTower.of_algebraMap_eq (R := R) (S := Polynomial A ⧸ I) (A := T) ?_
    intro r
    simpa [localized_cyclic_quotient_target_quotient_algebra] using
      (show algebraMap R T r = algebraMap (Polynomial A ⧸ I) T (algebraMap R (Polynomial A ⧸ I) r)
        by rfl)
  letI : IsScalarTower R (Polynomial A ⧸ I) T := hTower
  letI : IsLocalization (Submonoid.powers (algebraMap R (Polynomial A ⧸ I) f)) T := by
    -- The quotient-localization target is already known to localize at the image submonoid coming
    -- from `A[X]`; rewrite that submonoid as the powers of the image of `f` in the quotient.
    simpa [quotient_polynomial_algebraMapSubmonoid_powers_eq (R := R) (A := A) q f] using
      (inferInstance :
        IsLocalization
          (Algebra.algebraMapSubmonoid (Polynomial A ⧸ I)
            (Submonoid.powers (algebraMap R (Polynomial A) f)))
          T)
  -- Specialize Proposition `10.9.14` to the cyclic quotient and rewrite the source localization
  -- submonoid into the away-localization submonoid used in the statement.
  simpa [Localization.Away, I, T] using
    ((Localization.algEquiv
      (Submonoid.powers (algebraMap R (Polynomial A ⧸ I) f))
      T).restrictScalars R)

/-- Helper for Lemma 10.118.7: the localization half of the cyclic-quotient bridge sends the
class of a polynomial to the corresponding class in the quotient of the localized polynomial ring. -/
private lemma localized_cyclic_quotient_localization_apply_mk
    {A : Type*} [CommRing A] [Algebra R A] (q p : Polynomial A) (f : R) :
    localized_cyclic_quotient_localization_algEquiv (R := R) (A := A) q f
      (algebraMap (Polynomial A ⧸ Ideal.span ({q} : Set (Polynomial A)))
        (Localization.Away (algebraMap R (Polynomial A ⧸ Ideal.span ({q} : Set (Polynomial A))) f))
        (Ideal.Quotient.mk _ p)) =
      Ideal.Quotient.mk _
        (algebraMap (Polynomial A) (Localization.Away (algebraMap R (Polynomial A) f)) p) := by
  let I : Ideal (Polynomial A) := Ideal.span ({q} : Set (Polynomial A))
  let T :=
    Localization.Away (algebraMap R (Polynomial A) f) ⧸
      Ideal.map
        (algebraMap (Polynomial A)
          (Localization.Away (algebraMap R (Polynomial A) f)))
        I
  let Mq :=
    Submonoid.powers (algebraMap R (Polynomial A ⧸ I) f)
  let hAlg : Algebra (Polynomial A ⧸ I) T :=
    localized_cyclic_quotient_target_quotient_algebra (R := R) (A := A) q f
  letI : Algebra (Polynomial A ⧸ I) T :=
    hAlg
  letI : SMul (Polynomial A ⧸ I) T := hAlg.toSMul
  letI : Module (Polynomial A ⧸ I) T := Algebra.toModule
  let hTower : IsScalarTower R (Polynomial A ⧸ I) T := by
    -- The local scalar-tower witness matches the one used in the localization equivalence.
    refine IsScalarTower.of_algebraMap_eq (R := R) (S := Polynomial A ⧸ I) (A := T) ?_
    intro r
    simpa [localized_cyclic_quotient_target_quotient_algebra] using
      (show algebraMap R T r = algebraMap (Polynomial A ⧸ I) T (algebraMap R (Polynomial A ⧸ I) r)
        by rfl)
  letI : IsScalarTower R (Polynomial A ⧸ I) T := hTower
  letI : IsLocalization Mq T := by
    -- Rewrite the already-available quotient-localization structure onto the literal powers
    -- submonoid in the quotient ring.
    simpa [Mq, quotient_polynomial_algebraMapSubmonoid_powers_eq (R := R) (A := A) q f] using
      (inferInstance :
        IsLocalization
          (Algebra.algebraMapSubmonoid (Polynomial A ⧸ I)
            (Submonoid.powers (algebraMap R (Polynomial A) f)))
          T)
  have hmk :
      ((Localization.algEquiv Mq T).restrictScalars R)
        (algebraMap (Polynomial A ⧸ I) (Localization Mq) (Ideal.Quotient.mk I p)) =
      Ideal.Quotient.mk _
        (algebraMap (Polynomial A) (Localization.Away (algebraMap R (Polynomial A) f)) p) := by
    -- Rewrite the quotient generator as `p / 1` in the source localization and then evaluate the
    -- owner localization equivalence on that class.
    change (Localization.algEquiv Mq T)
        (algebraMap (Polynomial A ⧸ I) (Localization Mq) (Ideal.Quotient.mk I p)) = _
    rw [← IsLocalization.mk'_one (M := Mq) (S := Localization Mq) (Ideal.Quotient.mk I p)]
    rw [Localization.algEquiv_mk', IsLocalization.mk'_one]
    simpa [I, T] using
      (Ideal.Quotient.algebraMap_quotient_map_quotient
        (R := Polynomial A)
        (S := Localization.Away (algebraMap R (Polynomial A) f))
        (p := I)
        p)
  simpa [localized_cyclic_quotient_localization_algEquiv, Localization.Away, I, Mq, T,
      quotient_polynomial_algebraMapSubmonoid_powers_eq (R := R) (A := A) q f] using hmk

/-- Helper for Lemma 10.118.7: transport the localized cyclic quotient from the quotient of the
localized polynomial ring to the quotient by the mapped polynomial over the localized coefficients. -/
private noncomputable abbrev localized_cyclic_quotient_transport_algEquiv
    {A : Type*} [CommRing A] [Algebra R A] (q : Polynomial A) (f : R) :
    (Localization.Away (algebraMap R (Polynomial A) f) ⧸
        Ideal.map
          (algebraMap (Polynomial A)
            (Localization.Away (algebraMap R (Polynomial A) f)))
          (Ideal.span ({q} : Set (Polynomial A)))) ≃ₐ[R]
      (Polynomial (Localization.Away (algebraMap R A f)) ⧸
        Ideal.span
          ({Polynomial.map (algebraMap A (Localization.Away (algebraMap R A f))) q} : Set _)) := by
  let e := localized_polynomial_algEquiv (R := R) (A := A) f
  let P : Ideal (Localization.Away (algebraMap R (Polynomial A) f)) :=
    Ideal.map
      (algebraMap (Polynomial A)
        (Localization.Away (algebraMap R (Polynomial A) f)))
      (Ideal.span ({q} : Set (Polynomial A)))
  let Q : Ideal (Polynomial (Localization.Away (algebraMap R A f))) :=
    Ideal.span
      ({Polynomial.map (algebraMap A (Localization.Away (algebraMap R A f))) q} : Set _)
  let p : Ideal R :=
    Ideal.comap (algebraMap R (Polynomial (Localization.Away (algebraMap R A f)))) Q
  have hP : Ideal.comap
      (algebraMap R (Localization.Away (algebraMap R (Polynomial A) f))) P = p := by
    -- Both quotient rings contract to the same ideal of `R` after the polynomial-localization
    -- transport.
    simpa [P, Q, p] using
      localized_cyclic_quotient_transport_comap_eq (R := R) (A := A) q f
  have hQ : Ideal.map e.toRingHom P = Q := by
    -- The localized principal relation ideal maps to the singleton span of the localized
    -- polynomial.
    simpa [P, Q, e] using
      localized_quotient_ideal_map_eq_mapped_singleton_span (R := R) (A := A) q f
  letI : Q.LiesOver p := ⟨rfl⟩
  letI : P.LiesOver p := ⟨hP.symm⟩
  -- Once both quotients lie over the same ideal of `R`, the transport is exactly the canonical
  -- quotient equivalence induced by `localized_polynomial_algEquiv`.
  let eQ :
      (Localization.Away (algebraMap R (Polynomial A) f) ⧸ P) ≃ₐ[R]
        (Polynomial (Localization.Away (algebraMap R A f)) ⧸ Q) :=
    ((Ideal.Quotient.algEquivOfEqMap (p := p) (σ := e) hQ.symm).restrictScalars R)
  exact by
    simpa [P, Q, p, e] using eQ

/-- Helper for Lemma 10.118.7: the transport half of the cyclic-quotient bridge sends the class in
the quotient of the localized polynomial ring to the class of the localized polynomial. -/
private lemma localized_cyclic_quotient_transport_apply_mk
    {A : Type*} [CommRing A] [Algebra R A] (q p : Polynomial A) (f : R) :
    localized_cyclic_quotient_transport_algEquiv (R := R) (A := A) q f
      (Ideal.Quotient.mk _
        (algebraMap (Polynomial A) (Localization.Away (algebraMap R (Polynomial A) f)) p)) =
      Ideal.Quotient.mk _ (Polynomial.map (algebraMap A (Localization.Away (algebraMap R A f))) p) := by
  let e := localized_polynomial_algEquiv (R := R) (A := A) f
  let P : Ideal (Localization.Away (algebraMap R (Polynomial A) f)) :=
    Ideal.map
      (algebraMap (Polynomial A)
        (Localization.Away (algebraMap R (Polynomial A) f)))
      (Ideal.span ({q} : Set (Polynomial A)))
  let Q : Ideal (Polynomial (Localization.Away (algebraMap R A f))) :=
    Ideal.span
      ({Polynomial.map (algebraMap A (Localization.Away (algebraMap R A f))) q} : Set _)
  let pR : Ideal R :=
    Ideal.comap (algebraMap R (Polynomial (Localization.Away (algebraMap R A f)))) Q
  have hP : Ideal.comap
      (algebraMap R (Localization.Away (algebraMap R (Polynomial A) f))) P = pR := by
    -- This is the shared base ideal over which the quotient transport is defined.
    simpa [P, Q, pR] using
      localized_cyclic_quotient_transport_comap_eq (R := R) (A := A) q f
  have hQ : Ideal.map e.toRingHom P = Q := by
    -- The transported source ideal is exactly the singleton-span target ideal.
    simpa [P, Q, e] using
      localized_quotient_ideal_map_eq_mapped_singleton_span (R := R) (A := A) q f
  letI : Q.LiesOver pR := ⟨rfl⟩
  letI : P.LiesOver pR := ⟨hP.symm⟩
  -- Evaluate the quotient transport on the generator and then identify the polynomial image using
  -- the localized polynomial comparison formula.
  have htransport :
      localized_cyclic_quotient_transport_algEquiv (R := R) (A := A) q f
        (Ideal.Quotient.mk _
          (algebraMap (Polynomial A) (Localization.Away (algebraMap R (Polynomial A) f)) p)) =
        Ideal.Quotient.mk _
          (e (algebraMap (Polynomial A) (Localization.Away (algebraMap R (Polynomial A) f)) p)) := by
    simpa [localized_cyclic_quotient_transport_algEquiv, P, Q, pR, e] using
      (Ideal.Quotient.algEquivOfEqMap_apply (p := pR) (σ := e) hQ.symm
        (algebraMap (Polynomial A) (Localization.Away (algebraMap R (Polynomial A) f)) p))
  -- The polynomial-localization equivalence sends the coefficientwise image to the mapped
  -- polynomial in the localized coefficient ring.
  rw [localized_polynomial_algEquiv_algebraMap (R := R) (A := A) f p] at htransport
  simpa using htransport

/-- Helper for Lemma 10.118.7: the cyclic-quotient transport sends the class of a constant
polynomial to the class of the corresponding localized constant polynomial. -/
lemma localized_cyclic_quotient_transport_apply_C
    {A : Type*} [CommRing A] [Algebra R A] (q : Polynomial A) (a : A) (f : R) :
    localized_cyclic_quotient_transport_algEquiv (R := R) (A := A) q f
      (Ideal.Quotient.mk _
        (algebraMap (Polynomial A) (Localization.Away (algebraMap R (Polynomial A) f))
          (Polynomial.C a))) =
      Ideal.Quotient.mk _ (Polynomial.C (algebraMap A (Localization.Away (algebraMap R A f)) a)) := by
  -- Specialize the generator-transport formula to the constant polynomial `C a`.
  simpa using
    (localized_cyclic_quotient_transport_apply_mk
      (R := R) (A := A) q (Polynomial.C a) f)

/-- Helper for Lemma 10.118.7: the transported cyclic-quotient target receives the explicit
localized source-polynomial-ring map used to define its source algebra structure. -/
private noncomputable def localized_cyclic_quotient_target_source_algebra_hom
    {A : Type*} [CommRing A] [Algebra R A] (q : Polynomial A) (f : R) :
    Localization.Away (algebraMap R (Polynomial A) f) →+*
      (Polynomial (Localization.Away (algebraMap R A f)) ⧸
        Ideal.span
          ({Polynomial.map (algebraMap A (Localization.Away (algebraMap R A f))) q} : Set _)) :=
  (localized_cyclic_quotient_transport_algEquiv (R := R) (A := A) q f).toRingHom.comp
    (Ideal.Quotient.mk
      (Ideal.map
        (algebraMap (Polynomial A)
          (Localization.Away (algebraMap R (Polynomial A) f)))
        (Ideal.span ({q} : Set (Polynomial A)))))

/-- Helper for Lemma 10.118.7: the transported cyclic-quotient target also carries the canonical
localized base-ring map through localized coefficients and constant polynomials. -/
private noncomputable def localized_cyclic_quotient_target_base_algebra_hom
    {A : Type*} [CommRing A] [Algebra R A] (q : Polynomial A) (f : R) :
    Localization.Away f →+*
      (Polynomial (Localization.Away (algebraMap R A f)) ⧸
        Ideal.span
          ({Polynomial.map (algebraMap A (Localization.Away (algebraMap R A f))) q} : Set _)) :=
  (Ideal.Quotient.mk
      (Ideal.span
        ({Polynomial.map (algebraMap A (Localization.Away (algebraMap R A f))) q} : Set _))).comp
    (Polynomial.C.comp
      (algebraMap (Localization.Away f)
        (Localization.Away (algebraMap R A f))))

/-- Helper for Lemma 10.118.7: for any `R`-algebra `B`, the canonical away-localization map
`R_f → B_f` agrees with the ambient algebra map. -/
private theorem localized_away_map_eq_algebraMap
    {B : Type*} [CommRing B] [Algebra R B] (f : R) :
    IsLocalization.Away.map (S := Localization.Away f)
      (Q := Localization.Away (algebraMap R B f)) (algebraMap R B) f =
      algebraMap (Localization.Away f) (Localization.Away (algebraMap R B f)) := by
  -- Both ring homs are maps out of `R_f`, so localization extensionality reduces the comparison
  -- to the image of the original ring `R`.
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  ext r
  symm
  simpa [IsLocalization.Away.map] using
    (IsLocalization.map_eq
      (M := Submonoid.powers f)
      (S := Localization.Away f)
      (Q := Localization.Away (algebraMap R B f))
      (g := algebraMap R B)
      (hy := by
        intro x hx
        rcases hx with ⟨n, rfl⟩
        simpa [map_pow] using
          (show (algebraMap R B f) ^ n ∈ Submonoid.powers (algebraMap R B f) from ⟨n, rfl⟩))
      r)

/-- Helper for Lemma 10.118.7: the canonical map `R_f → (A[X])_f` sends a base generator to the
corresponding constant polynomial over the localized coefficient ring. -/
private theorem localized_polynomial_away_generator_eq_constant
    {A : Type*} [CommRing A] [Algebra R A] (f : R) (r : R) :
    algebraMap (Localization.Away f)
      (Localization.Away (algebraMap R (Polynomial A) f))
      (algebraMap R (Localization.Away f) r) =
      algebraMap (Polynomial A)
        (Localization.Away (algebraMap R (Polynomial A) f))
        (Polynomial.C (algebraMap R A r)) := by
  -- Identify the canonical map `R_f → (A[X])_f` with the ambient map from `R`.
  calc
    algebraMap (Localization.Away f)
        (Localization.Away (algebraMap R (Polynomial A) f))
        (algebraMap R (Localization.Away f) r) =
      algebraMap (Polynomial A)
        (Localization.Away (algebraMap R (Polynomial A) f))
        (algebraMap R (Polynomial A) r) := by
        calc
          algebraMap (Localization.Away f)
              (Localization.Away (algebraMap R (Polynomial A) f))
              (algebraMap R (Localization.Away f) r) =
            IsLocalization.Away.map (S := Localization.Away f)
              (Q := Localization.Away (algebraMap R (Polynomial A) f))
              (algebraMap R (Polynomial A)) f
              (algebraMap R (Localization.Away f) r) := by
                symm
                exact DFunLike.congr_fun
                  (localized_away_map_eq_algebraMap (R := R) (B := Polynomial A) f)
                  (algebraMap R (Localization.Away f) r)
          _ =
            algebraMap (Polynomial A)
              (Localization.Away (algebraMap R (Polynomial A) f))
              (algebraMap R (Polynomial A) r) := by
                simpa [IsLocalization.Away.map] using
                  (IsLocalization.map_eq
                    (M := Submonoid.powers f)
                    (S := Localization.Away f)
                    (P := Polynomial A)
                    (T := Submonoid.powers (algebraMap R (Polynomial A) f))
                    (Q := Localization.Away (algebraMap R (Polynomial A) f))
                    (g := algebraMap R (Polynomial A))
                    (hy := by
                      intro x hx
                      rcases hx with ⟨n, rfl⟩
                      exact ⟨n, by simp [map_pow]⟩)
                    r)
    _ =
      algebraMap (Polynomial A)
        (Localization.Away (algebraMap R (Polynomial A) f))
        (Polynomial.C (algebraMap R A r)) := by
        simp

/-- Helper for Lemma 10.118.7: the explicit localized base map agrees with the transported source
map after restricting scalars along `R_f → (A[X])_f`. -/
private theorem localized_cyclic_quotient_target_base_action_ext
    {A : Type*} [CommRing A] [Algebra R A] (q : Polynomial A) (f : R) :
    localized_cyclic_quotient_target_base_algebra_hom (R := R) (A := A) q f =
      (localized_cyclic_quotient_target_source_algebra_hom (R := R) (A := A) q f).comp
        (algebraMap (Localization.Away f)
          (Localization.Away (algebraMap R (Polynomial A) f))) := by
  -- Compare the two maps out of `R_f` on generators from `R`.
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  ext r
  have hcoeff :
      algebraMap (Localization.Away f) (Localization.Away (algebraMap R A f))
          (algebraMap R (Localization.Away f) r) =
        algebraMap A (Localization.Away (algebraMap R A f)) (algebraMap R A r) := by
    -- Compute the coefficient-localization map on the generator `r / 1`.
    calc
      algebraMap (Localization.Away f) (Localization.Away (algebraMap R A f))
          (algebraMap R (Localization.Away f) r) =
        IsLocalization.Away.map (S := Localization.Away f)
          (Q := Localization.Away (algebraMap R A f))
          (algebraMap R A) f
          (algebraMap R (Localization.Away f) r) := by
            symm
            exact DFunLike.congr_fun
              (localized_away_map_eq_algebraMap (R := R) (B := A) f)
              (algebraMap R (Localization.Away f) r)
      _ =
        algebraMap A (Localization.Away (algebraMap R A f)) (algebraMap R A r) := by
          simpa [IsLocalization.Away.map] using
            (IsLocalization.map_eq
              (M := Submonoid.powers f)
              (S := Localization.Away f)
              (P := A)
              (T := Submonoid.powers (algebraMap R A f))
              (Q := Localization.Away (algebraMap R A f))
              (g := algebraMap R A)
              (hy := fun x hx ↦
                match hx with
                | ⟨n, hn⟩ => ⟨n, hn⟩)
              r)
  have hbase :
      localized_cyclic_quotient_target_base_algebra_hom (R := R) (A := A) q f
        (algebraMap R (Localization.Away f) r) =
      Ideal.Quotient.mk _
        (Polynomial.C
          (algebraMap A (Localization.Away (algebraMap R A f)) (algebraMap R A r))) := by
    -- Unfold the explicit base map and rewrite the coefficient localization on the generator
    -- `r / 1`.
    simp only [localized_cyclic_quotient_target_base_algebra_hom, RingHom.comp_apply]
    congr 1
    exact congrArg Polynomial.C hcoeff
  have hsource :
      ((localized_cyclic_quotient_target_source_algebra_hom (R := R) (A := A) q f).comp
          (algebraMap (Localization.Away f)
            (Localization.Away (algebraMap R (Polynomial A) f))))
        (algebraMap R (Localization.Away f) r) =
      Ideal.Quotient.mk _
        (Polynomial.C
          (algebraMap A (Localization.Away (algebraMap R A f)) (algebraMap R A r))) := by
    -- Rewrite the source-side generator as a localized constant polynomial, then evaluate the
    -- transported quotient map on that constant polynomial.
    calc
      ((localized_cyclic_quotient_target_source_algebra_hom (R := R) (A := A) q f).comp
          (algebraMap (Localization.Away f)
            (Localization.Away (algebraMap R (Polynomial A) f))))
          (algebraMap R (Localization.Away f) r) =
        localized_cyclic_quotient_target_source_algebra_hom (R := R) (A := A) q f
          (algebraMap (Localization.Away f)
            (Localization.Away (algebraMap R (Polynomial A) f))
            (algebraMap R (Localization.Away f) r)) := by
          rfl
      _ =
        localized_cyclic_quotient_target_source_algebra_hom (R := R) (A := A) q f
          (algebraMap (Polynomial A)
            (Localization.Away (algebraMap R (Polynomial A) f))
            (Polynomial.C (algebraMap R A r))) := by
          rw [localized_polynomial_away_generator_eq_constant (R := R) (A := A) f r]
      _ =
        Ideal.Quotient.mk _
          (Polynomial.C
            (algebraMap A (Localization.Away (algebraMap R A f)) (algebraMap R A r))) := by
          simpa [localized_cyclic_quotient_target_source_algebra_hom, RingHom.comp_apply] using
            (localized_cyclic_quotient_transport_apply_C
              (R := R) (A := A) q (algebraMap R A r) f)
  have hfinal :
      ((localized_cyclic_quotient_target_base_algebra_hom (R := R) (A := A) q f).comp
          (algebraMap R (Localization.Away f))) r =
      (((localized_cyclic_quotient_target_source_algebra_hom (R := R) (A := A) q f).comp
            (algebraMap (Localization.Away f)
              (Localization.Away (algebraMap R (Polynomial A) f)))).comp
          (algebraMap R (Localization.Away f))) r := by
    simpa [RingHom.comp_apply] using hbase.trans hsource.symm
  exact hfinal

/-- Helper for Lemma 10.118.7: the transported cyclic-quotient target inherits the scalar action
of the localized source polynomial ring via `localized_polynomial_algEquiv`. -/
noncomputable instance localized_cyclic_quotient_target_algebra_over_source
    {A : Type*} [CommRing A] [Algebra R A] (q : Polynomial A) (f : R) :
    Algebra (Localization.Away (algebraMap R (Polynomial A) f))
      (Polynomial (Localization.Away (algebraMap R A f)) ⧸
        Ideal.span
          ({Polynomial.map (algebraMap A (Localization.Away (algebraMap R A f))) q} : Set _)) := by
  -- Use the explicit transported source map so later scalar comparisons refer to a fixed hom.
  exact
    (localized_cyclic_quotient_target_source_algebra_hom
      (R := R) (A := A) q f).toAlgebra

/-- Helper for Lemma 10.118.7: the transported cyclic-quotient target also inherits the scalar
action of `R_f` by composing the localized source-ring action with the canonical map
`R_f → (A[X])_f`. -/
noncomputable instance localized_cyclic_quotient_target_algebra_over_base
    {A : Type*} [CommRing A] [Algebra R A] (q : Polynomial A) (f : R) :
    Algebra (Localization.Away f)
      (Polynomial (Localization.Away (algebraMap R A f)) ⧸
        Ideal.span
          ({Polynomial.map (algebraMap A (Localization.Away (algebraMap R A f))) q} : Set _)) := by
  -- Use the explicit base map so the `R_f`-action is independent of instance-search choices.
  exact
    (localized_cyclic_quotient_target_base_algebra_hom
      (R := R) (A := A) q f).toAlgebra

/-- Helper for Lemma 10.118.7: record the localized source-polynomial-ring module structure on the
transported cyclic-quotient target so later declarations do not trigger expensive instance search. -/
noncomputable instance localized_cyclic_quotient_target_module_over_source
    {A : Type*} [CommRing A] [Algebra R A] (q : Polynomial A) (f : R) :
    Module (Localization.Away (algebraMap R (Polynomial A) f))
      (Polynomial (Localization.Away (algebraMap R A f)) ⧸
        Ideal.span
          ({Polynomial.map (algebraMap A (Localization.Away (algebraMap R A f))) q} : Set _)) :=
by
  -- Recover the module structure from the stabilized source algebra structure.
  let _ := localized_cyclic_quotient_target_algebra_over_source (R := R) (A := A) q f
  exact Algebra.toModule

/-- Helper for Lemma 10.118.7: record the `R_f`-module structure on the transported cyclic-quotient
target so later declarations can restrict scalars without re-running quotient instance search. -/
noncomputable instance localized_cyclic_quotient_target_module_over_base
    {A : Type*} [CommRing A] [Algebra R A] (q : Polynomial A) (f : R) :
    Module (Localization.Away f)
      (Polynomial (Localization.Away (algebraMap R A f)) ⧸
        Ideal.span
          ({Polynomial.map (algebraMap A (Localization.Away (algebraMap R A f))) q} : Set _)) :=
by
  -- Recover the module structure from the stabilized base algebra structure.
  let _ := localized_cyclic_quotient_target_algebra_over_base (R := R) (A := A) q f
  exact Algebra.toModule

/-- Helper for Lemma 10.118.7: the transported cyclic-quotient target sits in the expected scalar
tower from `R_f` through the localized source polynomial ring. -/
private theorem localized_cyclic_quotient_target_algebraMap_base_eq
    {A : Type*} [CommRing A] [Algebra R A] (q : Polynomial A) (f : R)
    (r : Localization.Away f) :
    let T :=
      Polynomial (Localization.Away (algebraMap R A f)) ⧸
        Ideal.span
          ({Polynomial.map (algebraMap A (Localization.Away (algebraMap R A f))) q} : Set _)
    algebraMap (Localization.Away f) T r =
      algebraMap (Localization.Away (algebraMap R (Polynomial A) f)) T
        (algebraMap (Localization.Away f)
          (Localization.Away (algebraMap R (Polynomial A) f)) r) := by
  -- This is exactly the pointwise evaluation of the ring-hom equality proved above.
  simpa [localized_cyclic_quotient_target_algebra_over_base,
    localized_cyclic_quotient_target_algebra_over_source] using
    DFunLike.congr_fun
      (localized_cyclic_quotient_target_base_action_ext (R := R) (A := A) q f) r

/-- Helper for Lemma 10.118.7: the transported cyclic-quotient target sits in the expected scalar
tower from `R_f` through the localized source polynomial ring. -/
noncomputable instance localized_cyclic_quotient_target_isScalarTower
    {A : Type*} [CommRing A] [Algebra R A] (q : Polynomial A) (f : R) :
    @IsScalarTower (Localization.Away f)
      (Localization.Away (algebraMap R (Polynomial A) f))
      (Polynomial (Localization.Away (algebraMap R A f)) ⧸
        Ideal.span
          ({Polynomial.map (algebraMap A (Localization.Away (algebraMap R A f))) q} : Set _))
      (inferInstance : SMul (Localization.Away f)
        (Localization.Away (algebraMap R (Polynomial A) f)))
      (localized_cyclic_quotient_target_algebra_over_source (R := R) (A := A) q f).toSMul
      (localized_cyclic_quotient_target_algebra_over_base (R := R) (A := A) q f).toSMul :=
by
  -- The explicit base and source algebra maps now agree pointwise, so the scalar tower follows
  -- from the standard `algebraMap` criterion.
  refine IsScalarTower.of_algebraMap_eq ?_
  intro r
  simpa using
    localized_cyclic_quotient_target_algebraMap_base_eq (R := R) (A := A) q f r

/-- Helper for Lemma 10.118.7: the quotient-transport equivalence is linear over the localized
source polynomial ring once the target quotient carries the transported scalar action. -/
noncomputable def localized_cyclic_quotient_transport_algEquiv_over_source
    {A : Type*} [CommRing A] [Algebra R A] (q : Polynomial A) (f : R) :
    (Localization.Away (algebraMap R (Polynomial A) f) ⧸
        Ideal.map
          (algebraMap (Polynomial A)
            (Localization.Away (algebraMap R (Polynomial A) f)))
          (Ideal.span ({q} : Set (Polynomial A)))) ≃ₐ[
        Localization.Away (algebraMap R (Polynomial A) f)]
      (Polynomial (Localization.Away (algebraMap R A f)) ⧸
        Ideal.span
          ({Polynomial.map (algebraMap A (Localization.Away (algebraMap R A f))) q} : Set _)) :=
  -- The target source action was defined so the transport ring equivalence becomes source-linear
  -- by construction.
  AlgEquiv.ofRingEquiv
    (f := (localized_cyclic_quotient_transport_algEquiv (R := R) (A := A) q f).toRingEquiv)
    fun x ↦ by
      -- Unfold the transported source action and identify it with quotienting followed by
      -- `localized_cyclic_quotient_transport_algEquiv`.
      change localized_cyclic_quotient_transport_algEquiv (R := R) (A := A) q f
          (Ideal.Quotient.mk _ x) =
        localized_cyclic_quotient_transport_algEquiv (R := R) (A := A) q f
          (Ideal.Quotient.mk _ x)
      rfl

/-- Helper for Lemma 10.118.7: localizing a cyclic polynomial quotient identifies it with the
quotient of the localized polynomial ring by the localized defining equation. -/
noncomputable def localized_cyclic_quotient_algEquiv
    {A : Type*} [CommRing A] [Algebra R A] (q : Polynomial A) (f : R) :
    Localization.Away
        (algebraMap R (Polynomial A ⧸ Ideal.span ({q} : Set (Polynomial A))) f) ≃ₐ[R]
      (Polynomial (Localization.Away (algebraMap R A f)) ⧸
        Ideal.span
          ({Polynomial.map (algebraMap A (Localization.Away (algebraMap R A f))) q} : Set _)) :=
  -- Compose the localization step with the transport across the polynomial-localization
  -- equivalence.
  (localized_cyclic_quotient_localization_algEquiv (R := R) (A := A) q f).trans
    (localized_cyclic_quotient_transport_algEquiv (R := R) (A := A) q f)

/-- Helper for Lemma 10.118.7: the localized cyclic-quotient comparison sends the class of a
polynomial to the class of its coefficientwise localized image. -/
lemma localized_cyclic_quotient_algEquiv_apply_mk
    {A : Type*} [CommRing A] [Algebra R A] (q p : Polynomial A) (f : R) :
    localized_cyclic_quotient_algEquiv (R := R) (A := A) q f
      (algebraMap (Polynomial A ⧸ Ideal.span ({q} : Set (Polynomial A)))
        (Localization.Away (algebraMap R (Polynomial A ⧸ Ideal.span ({q} : Set (Polynomial A))) f))
        (Ideal.Quotient.mk _ p)) =
      Ideal.Quotient.mk _ (Polynomial.map (algebraMap A (Localization.Away (algebraMap R A f))) p) := by
  -- Evaluate the composite equivalence by first applying the localization comparison and then the
  -- transport across the localized polynomial equivalence.
  change localized_cyclic_quotient_transport_algEquiv (R := R) (A := A) q f
      (localized_cyclic_quotient_localization_algEquiv (R := R) (A := A) q f
        (algebraMap (Polynomial A ⧸ Ideal.span ({q} : Set (Polynomial A)))
          (Localization.Away
            (algebraMap R (Polynomial A ⧸ Ideal.span ({q} : Set (Polynomial A))) f))
          (Ideal.Quotient.mk _ p))) = _
  rw [localized_cyclic_quotient_localization_apply_mk]
  exact localized_cyclic_quotient_transport_apply_mk (R := R) (A := A) q p f

/-- Helper for Lemma 10.118.7: the cyclic quotient ring `A[X] / (q)` is the same module quotient
as `A[X] / (q)A[X]` for the ambient polynomial-ring self-module. -/
private noncomputable abbrev cyclic_quotient_module_quotient_linearEquiv
    {A : Type*} [CommRing A] (q : Polynomial A) :
    (Polynomial A ⧸ Ideal.span ({q} : Set (Polynomial A))) ≃ₗ[Polynomial A]
      ((Polynomial A) ⧸
        (Ideal.span ({q} : Set (Polynomial A)) •
          (⊤ : Submodule (Polynomial A) (Polynomial A)))) := by
  -- Rewrite the ideal quotient as the quotient by the corresponding self-module relation.
  refine Submodule.quotEquivOfEq _ _ ?_
  simpa using
    (Ideal.smul_top_eq_map (R := Polynomial A) (S := Polynomial A)
      (Ideal.span ({q} : Set (Polynomial A)))).symm

/-- Helper for Lemma 10.118.7: localizing the cyclic quotient module can be rewritten as
localizing the polynomial self-module and then quotienting by the localized relation submodule. -/
private noncomputable abbrev localized_cyclic_quotient_source_linearEquiv
    {A : Type*} [CommRing A] [Algebra R A] (q : Polynomial A) (f : R) :
    LocalizedModule.Away (algebraMap R (Polynomial A) f)
      (Polynomial A ⧸ Ideal.span ({q} : Set (Polynomial A))) ≃ₗ[
        Localization.Away (algebraMap R (Polynomial A) f)]
      (LocalizedModule.Away (algebraMap R (Polynomial A) f) (Polynomial A) ⧸
        ((Ideal.map
            (algebraMap (Polynomial A)
              (Localization.Away (algebraMap R (Polynomial A) f)))
            (Ideal.span ({q} : Set (Polynomial A)))) •
          (⊤ : Submodule
            (Localization.Away (algebraMap R (Polynomial A) f))
            (LocalizedModule.Away (algebraMap R (Polynomial A) f) (Polynomial A))))) := by
  let I : Ideal (Polynomial A) := Ideal.span ({q} : Set (Polynomial A))
  let s : Polynomial A := algebraMap R (Polynomial A) f
  let e :
      (Polynomial A ⧸ I) ≃ₗ[Polynomial A]
        ((Polynomial A) ⧸ (I • (⊤ : Submodule (Polynomial A) (Polynomial A)))) :=
    cyclic_quotient_module_quotient_linearEquiv (A := A) q
  let eLoc :
      LocalizedModule.Away s (Polynomial A ⧸ I) ≃ₗ[Localization.Away s]
        LocalizedModule.Away s ((Polynomial A) ⧸ (I • (⊤ : Submodule (Polynomial A) (Polynomial A)))) :=
    LinearEquiv.ofBijective
      (LocalizedModule.map (Submonoid.powers s) e.toLinearMap) <| by
        constructor
        · simpa using
            LocalizedModule.map_injective (Submonoid.powers s) e.toLinearMap e.injective
        · simpa using
            LocalizedModule.map_surjective (Submonoid.powers s) e.toLinearMap e.surjective
  have hlocalized :
      ((I • (⊤ : Submodule (Polynomial A) (Polynomial A))).localized (Submonoid.powers s)) =
        ((Ideal.map (algebraMap (Polynomial A) (Localization.Away s)) I) •
          (⊤ : Submodule (Localization.Away s) (LocalizedModule.Away s (Polynomial A)))) := by
    -- Rewrite the localized self-module relation into the standard localized ideal action.
    rw [Submodule.localized, Submodule.localized'_smul, Ideal.localized'_eq_map,
      Submodule.localized'_top]
  -- The public quotient-localization equivalence now produces the required source-side rewrite.
  exact eLoc.trans <|
    (localizedQuotientEquiv (Submonoid.powers s) (I • (⊤ : Submodule (Polynomial A) (Polynomial A)))).symm.trans
      (Submodule.quotEquivOfEq _ _ hlocalized)

/-- Helper for Lemma 10.118.7: the owner localized self-module comparison over `B`. -/
private noncomputable abbrev localized_self_module_linearEquiv_over_base_aux
    {B : Type*} [CommRing B] [Algebra R B] (f : R) :
    LocalizedModule.Away (algebraMap R B f) B ≃ₗ[B]
      Localization.Away (algebraMap R B f) :=
  IsLocalizedModule.linearEquiv
    (.powers (algebraMap R B f))
    (LocalizedModule.mkLinearMap (.powers (algebraMap R B f)) B)
    (Algebra.linearMap B (Localization.Away (algebraMap R B f)))

/-- Helper for Lemma 10.118.7: after extending scalars, the localized self-module comparison for
`A[X]` becomes linear over the localized source polynomial ring. -/
private noncomputable abbrev localized_self_module_linearEquiv_over_source
    {A : Type*} [CommRing A] [Algebra R A] (f : R) :
    LocalizedModule.Away (algebraMap R (Polynomial A) f) (Polynomial A) ≃ₗ[
        Localization.Away (algebraMap R (Polynomial A) f)]
      Localization.Away (algebraMap R (Polynomial A) f) :=
  LinearEquiv.extendScalarsOfIsLocalization
    (.powers (algebraMap R (Polynomial A) f))
    (Localization.Away (algebraMap R (Polynomial A) f))
    (localized_self_module_linearEquiv_over_base_aux
      (R := R) (B := Polynomial A) f)

/-- Helper for Lemma 10.118.7: the localized self-module equivalence sends the localized relation
submodule for the cyclic quotient to the corresponding ideal in the localized source ring. -/
private theorem localized_cyclic_quotient_source_relation_map_eq
    {A : Type*} [CommRing A] [Algebra R A] (q : Polynomial A) (f : R) :
    let B := Localization.Away (algebraMap R (Polynomial A) f)
    let P : Ideal B := Ideal.map (algebraMap (Polynomial A) B) (Ideal.span ({q} : Set (Polynomial A)))
    ((P • (⊤ : Submodule B (LocalizedModule.Away (algebraMap R (Polynomial A) f) (Polynomial A)))).map
      (localized_self_module_linearEquiv_over_source (R := R) (A := A) f).toLinearMap) =
      (P • (⊤ : Submodule B B)) := by
  -- Push the localized relation submodule through the self-module comparison and collapse the
  -- image of the ambient top submodule to the full localized source ring.
  let B := Localization.Away (algebraMap R (Polynomial A) f)
  let P : Ideal B := Ideal.map (algebraMap (Polynomial A) B) (Ideal.span ({q} : Set (Polynomial A)))
  let e := localized_self_module_linearEquiv_over_source (R := R) (A := A) f
  have hmap :
      Submodule.map e.toLinearMap
          (P • (⊤ : Submodule B (LocalizedModule.Away (algebraMap R (Polynomial A) f) (Polynomial A)))) =
        P • (⊤ : Submodule B B) := by
    calc
      Submodule.map e.toLinearMap
          (P • (⊤ : Submodule B (LocalizedModule.Away (algebraMap R (Polynomial A) f) (Polynomial A)))) =
        P • Submodule.map e.toLinearMap
          (⊤ : Submodule B (LocalizedModule.Away (algebraMap R (Polynomial A) f) (Polynomial A))) := by
            simpa using
              (Submodule.map_smul'' (f := e.toLinearMap)
                (I := P)
                (N := (⊤ : Submodule B
                  (LocalizedModule.Away (algebraMap R (Polynomial A) f) (Polynomial A)))))
      _ = P • (⊤ : Submodule B B) := by
            rw [Submodule.map_top, LinearMap.range_eq_top.2 e.surjective]
  simpa [B, P, e] using hmap

/-- Helper for Lemma 10.118.7: quotienting the localized source ring by the ideal action
submodule is the same as quotienting by the ideal itself. -/
private theorem localized_cyclic_quotient_source_ring_relation_eq
    {A : Type*} [CommRing A] [Algebra R A] (q : Polynomial A) (f : R) :
    let B := Localization.Away (algebraMap R (Polynomial A) f)
    let P : Ideal B := Ideal.map (algebraMap (Polynomial A) B) (Ideal.span ({q} : Set (Polynomial A)))
    (P • (⊤ : Submodule B B)) = (P : Submodule B B) := by
  -- For a ring viewed as a module over itself, the ideal action on `⊤` recovers the ideal.
  let B := Localization.Away (algebraMap R (Polynomial A) f)
  let P : Ideal B := Ideal.map (algebraMap (Polynomial A) B) (Ideal.span ({q} : Set (Polynomial A)))
  change (P • (⊤ : Submodule B B)) = (P : Submodule B B)
  ext x
  change x ∈ P • (⊤ : Submodule B B) ↔ x ∈ (P : Submodule B B)
  simpa [Ideal.smul_top_eq_map]

/-- Helper for Lemma 10.118.7: after identifying the localized polynomial self-module with the
localized source ring, the source-side cyclic quotient becomes the ordinary quotient ring. -/
private noncomputable abbrev localized_cyclic_quotient_source_module_to_ring_quotient_linearEquiv
    {A : Type*} [CommRing A] [Algebra R A] (q : Polynomial A) (f : R) :
    (LocalizedModule.Away (algebraMap R (Polynomial A) f) (Polynomial A) ⧸
        ((Ideal.map
            (algebraMap (Polynomial A)
              (Localization.Away (algebraMap R (Polynomial A) f)))
            (Ideal.span ({q} : Set (Polynomial A)))) •
          (⊤ : Submodule
            (Localization.Away (algebraMap R (Polynomial A) f))
            (LocalizedModule.Away (algebraMap R (Polynomial A) f) (Polynomial A))))) ≃ₗ[
        Localization.Away (algebraMap R (Polynomial A) f)]
      (Localization.Away (algebraMap R (Polynomial A) f) ⧸
        Ideal.map
          (algebraMap (Polynomial A)
            (Localization.Away (algebraMap R (Polynomial A) f)))
          (Ideal.span ({q} : Set (Polynomial A)))) :=
  (Submodule.Quotient.equiv _ _
      (localized_self_module_linearEquiv_over_source (R := R) (A := A) f)
      (localized_cyclic_quotient_source_relation_map_eq (R := R) (A := A) q f)).trans
    (Submodule.quotEquivOfEq _ _
      (localized_cyclic_quotient_source_ring_relation_eq (R := R) (A := A) q f))

/-- Helper for Lemma 10.118.7: localizing a ring viewed as a module over itself identifies that
localized module with the localized ring, after restricting scalars from `B_f` to `R_f`. -/
private noncomputable abbrev localized_self_module_linearEquiv_aux
    {B : Type*} [CommRing B] [Algebra R B] (f : R) :
    LocalizedModule.Away (algebraMap R B f) B ≃ₗ[Localization.Away f]
      Localization.Away (algebraMap R B f) :=
  LinearEquiv.restrictScalars (Localization.Away f)
    (LinearEquiv.extendScalarsOfIsLocalization
      (.powers (algebraMap R B f))
      (Localization.Away (algebraMap R B f))
      (localized_self_module_linearEquiv_over_base_aux (R := R) (B := B) f))

/-- Helper for Lemma 10.118.7: the localized cyclic quotient module agrees with the canonical
localized monic-quotient model after passing through the quotient of the localized polynomial ring. -/
noncomputable abbrev localized_cyclic_quotient_module_linearEquiv_over_source
    {A : Type*} [CommRing A] [Algebra R A] (q : Polynomial A) (f : R) :
    LocalizedModule.Away (algebraMap R (Polynomial A) f)
      (Polynomial A ⧸ Ideal.span ({q} : Set (Polynomial A))) ≃ₗ[
        Localization.Away (algebraMap R (Polynomial A) f)]
      (Polynomial (Localization.Away (algebraMap R A f)) ⧸
        Ideal.span
          ({Polynomial.map (algebraMap A (Localization.Away (algebraMap R A f))) q} : Set _)) :=
  -- Compose the source localized-quotient rewrite, the localized self-module/ring comparison, and
  -- the transported quotient equivalence over the localized source ring.
  localized_cyclic_quotient_source_linearEquiv (R := R) (A := A) q f ≪≫ₗ
    localized_cyclic_quotient_source_module_to_ring_quotient_linearEquiv
      (R := R) (A := A) q f ≪≫ₗ
    (localized_cyclic_quotient_transport_algEquiv_over_source
      (R := R) (A := A) q f).toLinearEquiv

end GenericFlatness

end
