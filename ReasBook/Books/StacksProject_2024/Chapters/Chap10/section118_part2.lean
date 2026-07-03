import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Localization
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_118_7 (from Chap10) -/
universe u v w

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module S M]

namespace GenericFlatness

/- Domain triage:
* primary domain: the generic-flatness good locus on `Spec(R)`;
* source-facing owner: `goodLocus R S M` from `10_118_3_2`;
* core/canonical topological owners: `IsOpen` and `Dense` for subsets of `Spec(R)`;
* bridge/view target of this file: openness comes directly from the owner description
  `goodLocus_eq_iUnion`, while density under `[IsReduced R]` is the source-facing consequence
  obtained by combining the domain case `Lemma_10_118_3` with the dense-standard-open bridge
  `dense_goodLocus_of_dense_standardOpen_cover` from `Lemma_10_118_6`. -/

/-- The generic-flatness good locus `U(R → S, M)` is open in `Spec(R)`. -/
-- Proof sketch: `goodLocus R S M` is defined as a union of basic opens `D(f)`, and each basic
-- open is open in `Spec(R)`.
theorem isOpen_goodLocus :
    IsOpen (goodLocus R S M) := by
  -- Reuse the canonical owner statement proved in the dense-cover file.
  simpa using GenericFlatness.isOpen_goodLocus_aux (R := R) (S := S) (M := M)

/-- Helper for Lemma 10.118.7: over a domain, the generic-flatness good locus contains a dense
basic open coming from the nonzero witness of Lemma `10.118.3`. -/
theorem dense_goodLocus_of_isDomain
    [IsDomain R] [Algebra.FiniteType R S] [Module.Finite S M] :
    Dense (goodLocus R S M) := by
  obtain ⟨f, hf, hcond⟩ :
      ∃ f : R, f ≠ 0 ∧ LocalizationCondition R S M f :=
    exists_nonzero_localization_away_free_and_finitePresentation_of_finiteType
  have hsubset : (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆ goodLocus R S M := by
    -- The witness `f` contributes its basic open directly to the defining union of the good locus.
    intro p hp
    rw [goodLocus_eq_iUnion]
    exact Set.mem_iUnion.mpr ⟨⟨f, hcond⟩, hp⟩
  -- A nonzero basic open is dense over a domain, so the larger good locus is dense as well.
  exact Dense.mono hsubset (basicOpen_dense_of_nonzero_of_isDomain f hf)

/-- Helper for Lemma 10.118.7: density of the good locus propagates across a short exact sequence
from the two endpoint modules to the middle module. -/
theorem dense_goodLocus_middle_of_shortExact
    {T : CategoryTheory.ShortComplex (ModuleCat.{max u v} S)} (hT : T.ShortExact)
    (h₁ : Dense (goodLocus R S T.X₁)) (h₃ : Dense (goodLocus R S T.X₃)) :
    Dense (goodLocus R S T.X₂) := by
  have hinter :
      Dense (goodLocus R S T.X₁ ∩ goodLocus R S T.X₃) := by
    -- The endpoint good loci are open, so their intersection is dense.
    exact h₁.inter_of_isOpen_right h₃ (isOpen_goodLocus (R := R) (S := S) (M := T.X₃))
  -- Lemma `10.118.4` identifies this dense intersection as a subset of the middle good locus.
  exact Dense.mono
    (CategoryTheory.ShortComplex.ShortExact.goodLocus_inter_subset_of_shortExact
      (R := R) (S := S) (T := T) hT)
    hinter

/-- Helper for Lemma 10.118.7: an `S`-linear equivalence transports the localized
generic-flatness condition at a fixed element of `R`. -/
theorem localizationCondition_of_linearEquiv
    {N : Type*} [AddCommGroup N] [Module S N]
    (f : R) (e : M ≃ₗ[S] N) [h : LocalizationCondition R S M f] :
    LocalizationCondition R S N f := by
  -- Localize the linear equivalence and transport the finite-presentation and freeness fields.
  let e' : LocalizedModule.Away (algebraMap R S f) M ≃ₗ[Localization.Away (algebraMap R S f)]
      LocalizedModule.Away (algebraMap R S f) N := by
    refine LinearEquiv.ofBijective
      (LocalizedModule.map (.powers (algebraMap R S f)) e.toLinearMap) ?_
    constructor
    · simpa using
        LocalizedModule.map_injective (.powers (algebraMap R S f)) e.toLinearMap e.injective
    · simpa using
        LocalizedModule.map_surjective (.powers (algebraMap R S f)) e.toLinearMap e.surjective
  let e'' : LocalizedModule.Away (algebraMap R S f) M ≃ₗ[Localization.Away f]
      LocalizedModule.Away (algebraMap R S f) N :=
    { toFun := e'
      invFun := e'.symm
      left_inv := e'.left_inv
      right_inv := e'.right_inv
      map_add' := e'.map_add
      map_smul' := fun r x ↦ by
        -- Rewrite the base-scalar action through the canonical map into the localized target ring,
        -- then apply linearity of the localized equivalence.
        change e' ((algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f)) r) • x) =
          (algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f)) r) • e' x
        simpa using
          e'.map_smulₛₗ (algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f)) r) x }
  letI : Module.FinitePresentation (Localization.Away (algebraMap R S f))
      (LocalizedModule.Away (algebraMap R S f) N) := Module.FinitePresentation.of_equiv e'
  letI : Module.Free (Localization.Away f) (LocalizedModule.Away (algebraMap R S f) N) :=
    Module.Free.of_equiv' h.free_module e''
  exact
    { finitePresentation_algebra := h.finitePresentation_algebra
      finitePresentation_module := inferInstance
      free_algebra := h.free_algebra
      free_module := inferInstance }

/-- Helper for Lemma 10.118.7: the good locus is unchanged by `S`-linear equivalence of the
module argument. -/
theorem goodLocus_eq_of_linearEquiv
    {N : Type*} [AddCommGroup N] [Module S N] (e : M ≃ₗ[S] N) :
    goodLocus R S M = goodLocus R S N := by
  ext p
  -- Rewrite membership as the existence of one localization witness and transport that witness
  -- across the localized linear equivalence.
  rw [mem_goodLocus_iff, mem_goodLocus_iff]
  constructor
  · rintro ⟨f, hf, hfp⟩
    exact
      ⟨f,
        localizationCondition_of_linearEquiv (R := R) (S := S) (M := M) (N := N) f e,
        hfp⟩
  · rintro ⟨f, hf, hfp⟩
    exact
      ⟨f,
        localizationCondition_of_linearEquiv (R := R) (S := S) (M := N) (N := M) f e.symm,
        hfp⟩

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
private noncomputable def localized_cyclic_quotient_transport_algEquiv_over_source
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
private noncomputable abbrev localized_cyclic_quotient_module_linearEquiv_over_source
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

/-- Helper for Lemma 10.118.7: localizing a finite-type `R`-algebra at a prime of `R` preserves
finite type over the localized base ring. -/
private theorem finiteType_localizationAtPrime
    [Algebra.FiniteType R S] (p : PrimeSpectrum R) :
    let Rp := Localization.AtPrime p.asIdeal
    let Sp := Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
    Algebra.FiniteType Rp Sp := by
  -- TODO: localize a finite generating set for `S` and rewrite every element of `S_𝔭` as a
  -- localized numerator times a base scalar from `R_𝔭`. This is the finite-type half of the
  -- prime-localization bridge needed below.
  sorry

/-- Helper for Lemma 10.118.7: if `𝔭` is minimal, then `Spec(R_𝔭) → Spec(R)` has image `{𝔭}`. -/
private theorem localizationAtPrime_comap_range_eq_singleton_of_mem_minimalPrimes
    (p : PrimeSpectrum R) (hp : p.asIdeal ∈ minimalPrimes R) :
    Set.range (PrimeSpectrum.comap (algebraMap R (Localization.AtPrime p.asIdeal))) =
      ({p} : Set (PrimeSpectrum R)) := by
  have hpmin : IsMin p := PrimeSpectrum.isMin_iff.mpr hp
  rw [PrimeSpectrum.localization_comap_range
    (S := Localization.AtPrime p.asIdeal) (M := p.asIdeal.primeCompl)]
  ext q
  constructor
  · intro hq
    have hleIdeal : q.asIdeal ≤ p.asIdeal := by
      intro r hrq
      by_contra hrp
      exact (Set.disjoint_left.mp hq) hrp hrq
    have hle : q ≤ p := (PrimeSpectrum.asIdeal_le_asIdeal q p).mp hleIdeal
    exact Set.mem_singleton_iff.mpr (le_antisymm hle (hpmin hle))
  · rintro rfl
    exact Set.disjoint_left.2 fun r hrp hrq ↦ hrp hrq

/-- Helper for Lemma 10.118.7: a subset of `Spec(R)` is dense once its closure contains every
minimal prime. -/
private theorem dense_of_minimalPrimes_mem_closure
    {U : Set (PrimeSpectrum R)}
    (hmin : ∀ p : PrimeSpectrum R, p.asIdeal ∈ minimalPrimes R → p ∈ closure U) :
    Dense U := by
  rw [dense_iff_closure_eq]
  ext x
  constructor
  · intro hx
    trivial
  · intro hx
    obtain ⟨q, hq, hqx⟩ := Ideal.exists_minimalPrimes_le
      (J := x.asIdeal) (show (⊥ : Ideal R) ≤ x.asIdeal from bot_le)
    let q' : PrimeSpectrum R := ⟨q, Ideal.minimalPrimes_isPrime hq⟩
    have hq_mem : q' ∈ closure U := hmin q' hq
    have hq_le : q' ≤ x := (PrimeSpectrum.asIdeal_le_asIdeal q' x).mp hqx
    have hq_spec : q' ⤳ x := (PrimeSpectrum.le_iff_specializes q' x).mp hq_le
    -- A closed set containing every minimal prime contains all their specializations, hence every
    -- point of the spectrum.
    exact hq_spec.mem_closed isClosed_closure hq_mem

/-- Helper for Lemma 10.118.7: the remaining reduced-case density argument is to show that every
minimal prime lies in the closure of the good locus by passing to `Localization.AtPrime`. -/
private theorem minimalPrime_mem_closure_goodLocus
    [Algebra.FiniteType R S] [Module.Finite S M] [IsReduced R]
    (p : PrimeSpectrum R) (hp : p.asIdeal ∈ minimalPrimes R) :
    p ∈ closure (goodLocus R S M) := by
  -- Route correction: stabilize the prime-localization route first.  The localized pair
  -- `(R_𝔭 → S_𝔭, M_𝔭)` is a genuine finite-type/domain case, so the remaining gap is only the
  -- compatibility of `goodLocus` with arbitrary prime localization.
  let Rp := Localization.AtPrime p.asIdeal
  let Sp := Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
  let Mp := LocalizedModule (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl) M
  have hsubsingleton : Subsingleton (PrimeSpectrum Rp) := by
    -- Minimality of `p` makes the prime spectrum of `R_𝔭` a singleton.
    simpa [Rp] using
      (IsLocalization.subsingleton_primeSpectrum_of_mem_minimalPrimes p.asIdeal hp Rp)
  have hfield : IsField Rp := by
    -- A reduced ring with singleton spectrum is a field.
    letI : Subsingleton (PrimeSpectrum Rp) := hsubsingleton
    exact (PrimeSpectrum.subsingleton_iff_isField_of_isReduced (R := Rp)).mp inferInstance
  letI : IsField Rp := hfield
  letI : IsDomain Rp := hfield.isDomain
  letI : Algebra Rp Sp := inferInstance
  letI : Algebra.FiniteType Rp Sp := finiteType_localizationAtPrime (R := R) (S := S) p
  letI : Module.Finite Sp Mp := inferInstance
  have hDenseLoc : Dense (goodLocus Rp Sp Mp) := by
    -- After localizing at the minimal prime, the domain case applies to the localized pair.
    exact dense_goodLocus_of_isDomain (R := Rp) (S := Sp) (M := Mp)
  let q : PrimeSpectrum Rp := ⟨⊥, Ideal.isPrime_bot⟩
  have hqMem : q ∈ closure (goodLocus Rp Sp Mp) := hDenseLoc q
  have hqImage : PrimeSpectrum.comap (algebraMap R Rp) q = p := by
    have hqRange :
        PrimeSpectrum.comap (algebraMap R Rp) q ∈
          Set.range (PrimeSpectrum.comap (algebraMap R Rp)) := ⟨q, rfl⟩
    rw [localizationAtPrime_comap_range_eq_singleton_of_mem_minimalPrimes (R := R) p hp] at hqRange
    simpa using hqRange
  -- TODO: prove the prime-localization analogue of `goodLocus_localizationAway_eq_preimage`.
  -- Concretely, transport `hqMem` across `Spec(R_𝔭) → Spec(R)` using
  -- `goodLocus Rp Sp Mp = PrimeSpectrum.comap (algebraMap R Rp) ⁻¹' goodLocus R S M`.
  -- Then `hqImage` identifies the image point with `p`.
  sorry

/-- Lemma 10.118.7: if `R → S` is of finite type, `M` is a finite `S`-module, and `R` is
reduced, then the generic-flatness good locus `U(R → S, M)` is dense in `Spec(R)`. This is the
canonical reformulation of the textbook statement asserting the existence of an open dense subset
on which, Zariski-locally, `S_f` is a finitely presented free `R_f`-algebra and `M_f` is a
finitely presented free `S_f`-module over `R_f`. -/
-- Proof sketch: this is the density statement proved in the text for the good locus
-- `U(R → S, M)`, first for polynomial algebras by induction and Noether normalization and then in
-- general by passing to a polynomial presentation of `S`.
theorem dense_goodLocus_of_finiteType_finiteModule_reduced
    [Algebra.FiniteType R S] [Module.Finite S M] [IsReduced R] :
    Dense (goodLocus R S M) := by
  -- Reduce density to a pointwise closure statement on minimal primes.
  exact dense_of_minimalPrimes_mem_closure (R := R) (U := goodLocus R S M) fun p hp ↦
    minimalPrime_mem_closure_goodLocus (R := R) (S := S) (M := M) p hp

end GenericFlatness

end
