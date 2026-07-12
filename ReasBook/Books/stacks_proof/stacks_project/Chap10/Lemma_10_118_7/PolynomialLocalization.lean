import StacksProject_2024.Chap10.Lemma_10_118_7.GoodLocusDensity
import StacksProject_2024.Chap10.Lemma_10_6_4

universe u v w

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module S M]

namespace GenericFlatness

/-- Helper for Lemma 10.118.7: quotienting a polynomial ring by one equation gives a finitely
presented module over the ambient polynomial ring. -/
theorem polynomial_singleton_quotient_finitePresentation_over_polynomial
    {A : Type*} [CommRing A] (q : Polynomial A) :
    Module.FinitePresentation (Polynomial A)
      (Polynomial A ⧸ Ideal.span ({q} : Set (Polynomial A))) := by
  -- The quotient is cyclic over `A[X]`, so it is finite over the ambient polynomial ring.
  let _ : Module.Finite (Polynomial A)
      (Polynomial A ⧸ Ideal.span ({q} : Set (Polynomial A))) :=
    Module.Finite.of_surjective
      (Algebra.linearMap (Polynomial A)
        (Polynomial A ⧸ Ideal.span ({q} : Set (Polynomial A))))
      (Ideal.Quotient.mk_surjective (I := Ideal.span ({q} : Set (Polynomial A))))
  -- The quotient algebra is finitely presented because it is cut out by one equation.
  let _ : Algebra.FinitePresentation (Polynomial A)
      (Polynomial A ⧸ Ideal.span ({q} : Set (Polynomial A))) :=
    Algebra.FinitePresentation.quotient (R := Polynomial A) (A := Polynomial A)
      (Submodule.fg_span_singleton q)
  -- Finite plus finitely presented algebra implies finite presentation as a module.
  exact Module.FinitePresentation.of_finite_of_finitePresentation (R := Polynomial A)
    (S := Polynomial A ⧸ Ideal.span ({q} : Set (Polynomial A)))

/-- Helper for Lemma 10.118.7: a module that is finitely presented over the coefficient ring
remains finitely presented after extending scalars to a polynomial ring. -/
theorem finitePresentation_over_polynomial_of_finitePresentation_over_base
    {A : Type*} [CommRing A]
    {N : Type*} [AddCommGroup N] [Module (Polynomial A) N] [Module A N]
    [IsScalarTower A (Polynomial A) N] [Module.FinitePresentation A N] :
    Module.FinitePresentation (Polynomial A) N := by
  -- The polynomial ring is of finite type over its coefficient ring, so Lemma `10.6.4`
  -- upgrades finite presentation along that scalar extension.
  exact Module.FinitePresentation.of_restrictScalars_finiteType (R := A)

/-- Helper for Lemma 10.118.7: a monic polynomial quotient is free over the coefficient ring. -/
theorem monic_polynomial_quotient_free_over_base
    {A : Type*} [CommRing A] {q : Polynomial A} (hq : q.Monic) :
    Module.Free A (Polynomial A ⧸ Ideal.span ({q} : Set (Polynomial A))) := by
  -- The power-basis package for monic quotients gives the required free module structure.
  simpa using hq.free_quotient

/-- Helper for Lemma 10.118.7: a monic polynomial quotient is finitely presented over the
coefficient ring. -/
theorem monic_polynomial_quotient_finitePresentation_over_base
    {A : Type*} [CommRing A] {q : Polynomial A} (hq : q.Monic) :
    Module.FinitePresentation A (Polynomial A ⧸ Ideal.span ({q} : Set (Polynomial A))) := by
  -- Monicity makes the quotient finite over `A`.
  let _ : Module.Finite A (Polynomial A ⧸ Ideal.span ({q} : Set (Polynomial A))) :=
    hq.finite_quotient
  -- The quotient algebra is still finitely presented over `A`.
  let _ : Algebra.FinitePresentation A
      (Polynomial A ⧸ Ideal.span ({q} : Set (Polynomial A))) := by
    let _ : Algebra.FinitePresentation A (Polynomial A) := inferInstance
    exact Algebra.FinitePresentation.quotient (R := A) (A := Polynomial A)
      (Submodule.fg_span_singleton q)
  -- Finite plus finitely presented algebra gives finite presentation over the base ring.
  exact Module.FinitePresentation.of_finite_of_finitePresentation (R := A)
    (S := Polynomial A ⧸ Ideal.span ({q} : Set (Polynomial A)))

/-- Helper for Lemma 10.118.7: after localizing the coefficient ring, the polynomial ring over the
localized coefficients is another localization of the original polynomial ring away from the same
image of `f`. -/
noncomputable def localized_polynomial_algEquiv
    {A : Type*} [CommRing A] [Algebra R A] (f : R) :
    Localization.Away (algebraMap R (Polynomial A) f) ≃ₐ[R]
      Polynomial (Localization.Away (algebraMap R A f)) := by
  letI : Algebra (Polynomial A) (Polynomial (Localization.Away (algebraMap R A f))) :=
    Polynomial.algebra (R := A) (A := Localization.Away (algebraMap R A f))
  letI : IsScalarTower R (Polynomial A) (Polynomial (Localization.Away (algebraMap R A f))) := by
    infer_instance
  letI : IsLocalization (Submonoid.powers (algebraMap R (Polynomial A) f))
      (Polynomial (Localization.Away (algebraMap R A f))) := by
    -- `Polynomial.isLocalization` localizes `A[X]` at the image of `a ∈ A`; here `a` is the image
    -- of `f` in `A`.
    simpa using
      (Polynomial.isLocalization (Submonoid.powers (algebraMap R A f))
        (Localization.Away (algebraMap R A f)))
  -- Both rings localize `A[X]` away from the same powers of the image of `f`, so uniqueness of
  -- localization gives the comparison. We then forget from `A[X]`-algebras to `R`-algebras.
  exact
    (IsLocalization.algEquiv
      (Submonoid.powers (algebraMap R (Polynomial A) f))
      (Localization.Away (algebraMap R (Polynomial A) f))
      (Polynomial (Localization.Away (algebraMap R A f)))).restrictScalars R

/-- Helper for Lemma 10.118.7: for any `R`-algebra `B`, the canonical away-localization map
`R_f → B_f` agrees with the ambient algebra map. -/
private theorem localized_away_map_eq_algebraMap_aux
    {B : Type*} [CommRing B] [Algebra R B] (f : R) :
    IsLocalization.Away.map (S := Localization.Away f)
      (Q := Localization.Away (algebraMap R B f)) (algebraMap R B) f =
      algebraMap (Localization.Away f) (Localization.Away (algebraMap R B f)) := by
  -- Both maps out of `R_f` are determined by the images of generators from `R`.
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

/-- Helper for Lemma 10.118.7: the canonical map `R_f → (A[X])_f` sends a generator from `R`
to the corresponding localized constant polynomial. -/
private theorem localized_polynomial_away_generator_eq_constant_aux
    {A : Type*} [CommRing A] [Algebra R A] (f : R) (r : R) :
    algebraMap (Localization.Away f)
      (Localization.Away (algebraMap R (Polynomial A) f))
      (algebraMap R (Localization.Away f) r) =
      algebraMap (Polynomial A)
        (Localization.Away (algebraMap R (Polynomial A) f))
        (Polynomial.C (algebraMap R A r)) := by
  -- Rewrite the base-localization map through the canonical away map and evaluate it on `r / 1`.
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
            (localized_away_map_eq_algebraMap_aux (R := R) (B := Polynomial A) f)
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

/-- Helper for Lemma 10.118.7: the localized polynomial comparison sends the image of a polynomial
from `A[X]` to its coefficientwise localized polynomial. -/
private lemma localized_polynomial_algEquiv_algebraMap_aux
    {A : Type*} [CommRing A] [Algebra R A] (f : R) (p : Polynomial A) :
    localized_polynomial_algEquiv (R := R) (A := A) f
      (algebraMap (Polynomial A)
        (Localization.Away (algebraMap R (Polynomial A) f)) p) =
      Polynomial.map (algebraMap A (Localization.Away (algebraMap R A f))) p := by
  letI : Algebra (Polynomial A) (Polynomial (Localization.Away (algebraMap R A f))) :=
    Polynomial.algebra (R := A) (A := Localization.Away (algebraMap R A f))
  letI : IsScalarTower R (Polynomial A) (Polynomial (Localization.Away (algebraMap R A f))) := by
    infer_instance
  letI : IsLocalization (Submonoid.powers (algebraMap R (Polynomial A) f))
      (Polynomial (Localization.Away (algebraMap R A f))) := by
    simpa using
      (Polynomial.isLocalization (Submonoid.powers (algebraMap R A f))
        (Localization.Away (algebraMap R A f)))
  -- Rewrite the source polynomial as the class `p / 1`, then evaluate the localization
  -- equivalence on that generator.
  rw [← IsLocalization.mk'_one
      (M := Submonoid.powers (algebraMap R (Polynomial A) f))
      (S := Localization.Away (algebraMap R (Polynomial A) f)) p]
  change (IsLocalization.algEquiv (Submonoid.powers (algebraMap R (Polynomial A) f))
      (Localization.Away (algebraMap R (Polynomial A) f))
      (Polynomial (Localization.Away (algebraMap R A f))))
      (IsLocalization.mk' (Localization.Away (algebraMap R (Polynomial A) f)) p 1) = _
  rw [IsLocalization.algEquiv_mk']
  rw [IsLocalization.mk'_one
      (M := Submonoid.powers (algebraMap R (Polynomial A) f))
      (S := Polynomial (Localization.Away (algebraMap R A f))) p]
  rfl

/-- Helper for Lemma 10.118.7: the localized polynomial comparison is compatible with the
localized base ring `R_f`. -/
noncomputable def localized_polynomial_algEquiv_over_base
    {A : Type*} [CommRing A] [Algebra R A] (f : R) :
    Localization.Away (algebraMap R (Polynomial A) f) ≃ₐ[Localization.Away f]
      Polynomial (Localization.Away (algebraMap R A f)) := by
  let e := localized_polynomial_algEquiv (R := R) (A := A) f
  have hcomm :
      e.toRingHom.comp
          (algebraMap (Localization.Away f)
            (Localization.Away (algebraMap R (Polynomial A) f))) =
        algebraMap (Localization.Away f)
          (Polynomial (Localization.Away (algebraMap R A f))) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    apply RingHom.ext
    intro x
    simp only [RingHom.comp_apply]
    calc
      e.toRingHom
          (algebraMap (Localization.Away f)
            (Localization.Away (algebraMap R (Polynomial A) f))
            (algebraMap R (Localization.Away f) x)) =
        e.toRingHom
          (algebraMap (Polynomial A)
            (Localization.Away (algebraMap R (Polynomial A) f))
            (Polynomial.C (algebraMap R A x))) := by
              rw [localized_polynomial_away_generator_eq_constant_aux (R := R) (A := A) f x]
      _ =
        Polynomial.C
          (algebraMap A (Localization.Away (algebraMap R A f)) (algebraMap R A x)) := by
              simpa [e] using
                localized_polynomial_algEquiv_algebraMap_aux (R := R) (A := A) f
                  (Polynomial.C (algebraMap R A x))
      _ =
        Polynomial.C
          (algebraMap (Localization.Away f) (Localization.Away (algebraMap R A f))
            (algebraMap R (Localization.Away f) x)) := by
              congr 1
              calc
                algebraMap A (Localization.Away (algebraMap R A f)) (algebraMap R A x) =
                  IsLocalization.Away.map (S := Localization.Away f)
                    (Q := Localization.Away (algebraMap R A f))
                    (algebraMap R A) f
                    (algebraMap R (Localization.Away f) x) := by
                      symm
                      simpa [IsLocalization.Away.map] using
                        (IsLocalization.map_eq
                          (M := Submonoid.powers f)
                          (S := Localization.Away f)
                          (Q := Localization.Away (algebraMap R A f))
                          (g := algebraMap R A)
                          (hy := fun y hy ↦
                            match hy with
                            | ⟨n, hn⟩ => hn ▸ ⟨n, map_pow (algebraMap R A) f n⟩)
                          x)
                _ =
                  algebraMap (Localization.Away f) (Localization.Away (algebraMap R A f))
                    (algebraMap R (Localization.Away f) x) := by
                      exact DFunLike.congr_fun
                        (localized_away_map_eq_algebraMap_aux (R := R) (B := A) f)
                        (algebraMap R (Localization.Away f) x)
      _ =
        algebraMap (Localization.Away f)
          (Polynomial (Localization.Away (algebraMap R A f)))
          (algebraMap R (Localization.Away f) x) := by
              simp
  refine AlgEquiv.ofRingEquiv (f := e.toRingEquiv) ?_
  -- The base-scalar compatibility is exactly the pointwise form of the ring-hom equality above.
  intro r
  exact DFunLike.congr_fun hcomm r

/-- Helper for Lemma 10.118.7: if `A_f` is finitely presented over `R_f`, then the localized
polynomial ring `(A[X])_f` is finitely presented over `R_f`. -/
theorem localized_polynomial_finitePresentation_over_base
    {A : Type*} [CommRing A] [Algebra R A]
    {N : Type*} [AddCommGroup N] [Module A N] (f : R) [LocalizationCondition R A N f] :
    Algebra.FinitePresentation (Localization.Away f)
      (Localization.Away (algebraMap R (Polynomial A) f)) := by
  let B := Localization.Away (algebraMap R A f)
  let e := localized_polynomial_algEquiv_over_base (R := R) (A := A) f
  let _ : Algebra.FinitePresentation (Localization.Away f) B := inferInstance
  let _ : Algebra.FinitePresentation (Localization.Away f) (Polynomial B) := inferInstance
  -- First make the polynomial ring over `A_f` finitely presented over `R_f`, then transport that
  -- structure back across the explicit `R_f`-algebra equivalence.
  exact Algebra.FinitePresentation.equiv e.symm

/-- Helper for Lemma 10.118.7: if `A_f` is finitely presented over `R_f`, then the polynomial ring
over `A_f` is of finite type over `R_f`. -/
theorem localized_polynomial_finiteType_over_base
    {A : Type*} [CommRing A] [Algebra R A]
    {N : Type*} [AddCommGroup N] [Module A N] (f : R) [LocalizationCondition R A N f] :
    Algebra.FiniteType (Localization.Away f)
      (Polynomial (Localization.Away (algebraMap R A f))) := by
  let B := Localization.Away (algebraMap R A f)
  have hB :
      Algebra.FiniteType (Localization.Away f) B := by
    let _ : Algebra.FinitePresentation (Localization.Away f) B := inferInstance
    exact Algebra.FiniteType.of_finitePresentation
  let _ : Algebra.FiniteType B (Polynomial B) := inferInstance
  -- First the coefficients are of finite type over `R_f`, then adjoin one polynomial variable.
  exact Algebra.FiniteType.trans hB inferInstance

/-- Helper for Lemma 10.118.7: if `A_f` is free over `R_f`, then the localized polynomial ring
`(A[X])_f` is free over `R_f`. -/
theorem localized_polynomial_free_over_base
    {A : Type*} [CommRing A] [Algebra R A]
    {N : Type*} [AddCommGroup N] [Module A N] (f : R) [LocalizationCondition R A N f] :
    Module.Free (Localization.Away f)
      (Localization.Away (algebraMap R (Polynomial A) f)) := by
  let e := localized_polynomial_algEquiv_over_base (R := R) (A := A) f
  let hc : LocalizationCondition R A N f := inferInstance
  have hfreeA :
      Module.Free (Localization.Away f) (Localization.Away (algebraMap R A f)) :=
    hc.free_algebra
  have hpoly :
      Module.Free (Localization.Away f)
        (Polynomial (Localization.Away (algebraMap R A f))) := by
    letI : Module.Free (Localization.Away (algebraMap R A f))
        (Polynomial (Localization.Away (algebraMap R A f))) := inferInstance
    exact
      @Module.Free.trans
        (Localization.Away f)
        (Localization.Away (algebraMap R A f))
        (Polynomial (Localization.Away (algebraMap R A f)))
        inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
        inferInstance inferInstance hfreeA
  -- The source ring is free because it is `R_f`-linearly equivalent to the polynomial ring over
  -- the free `R_f`-algebra `A_f`.
  exact Module.Free.of_equiv' hpoly e.symm.toLinearEquiv

/-- Helper for Lemma 10.118.7: transporting the localized principal relation ideal through the
localized polynomial comparison identifies it with the singleton span of the mapped polynomial. -/
lemma localized_polynomial_algEquiv_algebraMap
    {A : Type*} [CommRing A] [Algebra R A] (f : R) (p : Polynomial A) :
    localized_polynomial_algEquiv (R := R) (A := A) f
      (algebraMap (Polynomial A)
        (Localization.Away (algebraMap R (Polynomial A) f)) p) =
      Polynomial.map (algebraMap A (Localization.Away (algebraMap R A f))) p := by
  letI : Algebra (Polynomial A) (Polynomial (Localization.Away (algebraMap R A f))) :=
    Polynomial.algebra (R := A) (A := Localization.Away (algebraMap R A f))
  letI : IsScalarTower R (Polynomial A) (Polynomial (Localization.Away (algebraMap R A f))) := by
    infer_instance
  letI : IsLocalization (Submonoid.powers (algebraMap R (Polynomial A) f))
      (Polynomial (Localization.Away (algebraMap R A f))) := by
    simpa using
      (Polynomial.isLocalization (Submonoid.powers (algebraMap R A f))
        (Localization.Away (algebraMap R A f)))
  -- Rewrite the source `algebraMap` as the localization class `p / 1`, then evaluate the
  -- canonical localization comparison on that class.
  rw [← IsLocalization.mk'_one
      (M := Submonoid.powers (algebraMap R (Polynomial A) f))
      (S := Localization.Away (algebraMap R (Polynomial A) f)) p]
  change (IsLocalization.algEquiv (Submonoid.powers (algebraMap R (Polynomial A) f))
      (Localization.Away (algebraMap R (Polynomial A) f))
      (Polynomial (Localization.Away (algebraMap R A f))))
      (IsLocalization.mk' (Localization.Away (algebraMap R (Polynomial A) f)) p 1) = _
  rw [IsLocalization.algEquiv_mk']
  -- The target localization class `p / 1` is exactly the coefficientwise polynomial map.
  rw [IsLocalization.mk'_one
      (M := Submonoid.powers (algebraMap R (Polynomial A) f))
      (S := Polynomial (Localization.Away (algebraMap R A f))) p]
  rfl

end GenericFlatness

end
