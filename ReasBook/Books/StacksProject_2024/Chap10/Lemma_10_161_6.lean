import Mathlib
import StacksProject_2024.Chap10.Definition_10_161_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped LaurentPolynomial

universe u

/-
Domain triage:
- primary domain: `N-1` rings under Laurent-polynomial extension;
- layer: `source-facing`;
- core/canonical owner: `IsN1Ring`;
- sampled bridge/view declarations:
  `R[T;T⁻¹]`, `IsLocalization.Away (X : R[X]) R[T;T⁻¹]`, and `Polynomial.toLaurentAlg`;
- primitive data: the base ring `R` and the canonical Laurent-polynomial ring `R[T;T⁻¹]`;
- derived API: `IsN1Ring.integralClosure_finite`.

The public surface should therefore speak directly about `IsN1Ring R[T;T⁻¹]`, while leaving the
localization presentation as an internal bridge rather than a second owner-level wrapper.
-/

section

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- Helper for Lemma 10.161.6: the constant-term inclusion `R → R[T;T⁻¹]` is injective. -/
lemma laurentPolynomial_constant_injective :
    Function.Injective (algebraMap R R[T;T⁻¹]) := by
  intro x y hxy
  -- Compare the coefficients at exponent `0` to recover the original constant.
  have hcoeff : (algebraMap R R[T;T⁻¹] x) 0 = (algebraMap R R[T;T⁻¹] y) 0 :=
    congrArg (fun p : R[T;T⁻¹] => p 0) hxy
  simpa [LaurentPolynomial.C_apply] using hcoeff

/-- Helper for Lemma 10.161.6: the coefficientwise map to Laurent polynomials over the fraction
field is injective. -/
lemma laurentPolynomial_fractionCoeffMap_injective :
    Function.Injective
      (AddMonoidAlgebra.mapAlgHom (M := ℤ) (Algebra.ofId R (FractionRing R)) :
        R[T;T⁻¹] →ₐ[R] (FractionRing R)[T;T⁻¹]) := by
  intro p q hpq
  -- Equality of Laurent polynomials is coefficientwise equality, and coefficients embed
  -- injectively into the fraction field.
  ext n
  have hcoeff :
      (AddMonoidAlgebra.mapAlgHom (M := ℤ) (Algebra.ofId R (FractionRing R)) p) n =
        (AddMonoidAlgebra.mapAlgHom (M := ℤ) (Algebra.ofId R (FractionRing R)) q) n :=
    congrArg (fun f : (FractionRing R)[T;T⁻¹] => f n) hpq
  exact FaithfulSMul.algebraMap_injective R (FractionRing R) <| by
    simpa [AddMonoidAlgebra.mapAlgHom_apply] using hcoeff

/-- Helper for Lemma 10.161.6: Laurent polynomials over the fraction field of `R` are
integrally closed. -/
lemma fractionRing_laurentPolynomial_isIntegrallyClosed :
    IsIntegrallyClosed ((FractionRing R)[T;T⁻¹]) := by
  let K := FractionRing R
  let hX : (Polynomial.X : Polynomial K) ≠ 0 := Polynomial.X_ne_zero
  let hM : Submonoid.powers (Polynomial.X : Polynomial K) ≤ nonZeroDivisors (Polynomial K) :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hX
  letI : IsLocalization.Away (Polynomial.X : Polynomial K) K[T;T⁻¹] :=
    LaurentPolynomial.isLocalization
  -- Laurent polynomials are the localization of `K[X]` away from `X`, so we localize the
  -- integrally closed polynomial ring.
  exact isIntegrallyClosed_of_isLocalization
    (S := K[T;T⁻¹]) (R := Polynomial K) (M := Submonoid.powers (Polynomial.X : Polynomial K)) hM

/-- Helper for Lemma 10.161.6: the constant map from `R` into the Laurent fraction field is
injective. -/
lemma laurentFraction_constant_injective :
    Function.Injective (algebraMap R (FractionRing R[T;T⁻¹])) := by
  -- Factor the constant map through the Laurent polynomial ring and use injectivity at each
  -- stage.
  exact (IsFractionRing.injective R[T;T⁻¹] (FractionRing R[T;T⁻¹])).comp
    laurentPolynomial_constant_injective

/-- Helper for Lemma 10.161.6: the fraction field of `R` maps to the Laurent fraction field by
viewing elements as constant Laurent rational functions. -/
noncomputable def fractionRingToLaurentFraction :
    FractionRing R →ₐ[R] FractionRing R[T;T⁻¹] :=
  IsFractionRing.liftAlgHom
    (g := Algebra.ofId R (FractionRing R[T;T⁻¹]))
    laurentFraction_constant_injective

/-- Helper for Lemma 10.161.6: an element integral over `R` stays integral after the constant map
to the Laurent fraction field. -/
lemma isIntegral_fractionRingToLaurentFraction {x : FractionRing R} (hx : IsIntegral R x) :
    IsIntegral R[T;T⁻¹] (fractionRingToLaurentFraction (R := R) x) := by
  -- Keep the same monic relation over `R`, then enlarge scalars to the Laurent polynomial ring.
  have hxR :
      IsIntegral R (fractionRingToLaurentFraction (R := R) x) :=
    hx.map (fractionRingToLaurentFraction (R := R))
  exact IsIntegral.tower_top (A := R[T;T⁻¹]) hxR

/-- Helper for Lemma 10.161.6: the normalization of `R` maps into the normalization of the
Laurent polynomial ring by viewing elements as constant Laurent rational functions. -/
noncomputable def integralClosure_constants_map_to_laurent_normalization
    (x : integralClosure R (FractionRing R)) :
    integralClosure R[T;T⁻¹] (FractionRing R[T;T⁻¹]) :=
  ⟨fractionRingToLaurentFraction (R := R) (x : FractionRing R),
    isIntegral_fractionRingToLaurentFraction (R := R) x.2⟩

/-- Helper for Lemma 10.161.6: the `R`-span of finitely many fraction-field coefficients is a
finite `R`-module. -/
lemma coeff_span_finite {s : Set (FractionRing R)} (hs : s.Finite) :
    Module.Finite R (Submodule.span R s) := by
  -- The ambient ring is Noetherian, so a span on a finite set is finitely generated.
  exact Module.Finite.span_of_finite R hs

/-- Helper for Lemma 10.161.6: coefficientwise Laurent extension into the common ambient fraction
field. -/
noncomputable def laurent_fraction_base_map :
    R[T;T⁻¹] →+* FractionRing ((FractionRing R)[T;T⁻¹]) :=
  (algebraMap ((FractionRing R)[T;T⁻¹]) (FractionRing ((FractionRing R)[T;T⁻¹]))).comp
    (AddMonoidAlgebra.mapAlgHom (M := ℤ) (Algebra.ofId R (FractionRing R))).toRingHom

/-- Helper for Lemma 10.161.6: the Laurent fraction field over `R` maps into the fraction field of
Laurent polynomials over `FractionRing R`. -/
noncomputable def laurent_fraction_comparison :
    FractionRing R[T;T⁻¹] →+* FractionRing ((FractionRing R)[T;T⁻¹]) :=
  -- Route correction: package the comparison as a plain fraction-field lift so evaluation on
  -- numerators is definitionally `IsFractionRing.lift_algebraMap`.
  IsFractionRing.lift
    (A := R[T;T⁻¹]) (K := FractionRing R[T;T⁻¹])
    (L := FractionRing ((FractionRing R)[T;T⁻¹]))
    (g := laurent_fraction_base_map (R := R))
    ((IsFractionRing.injective ((FractionRing R)[T;T⁻¹])
      (FractionRing ((FractionRing R)[T;T⁻¹]))).comp
      (laurentPolynomial_fractionCoeffMap_injective (R := R))
    )

/-- Helper for Lemma 10.161.6: the comparison map agrees with the coefficientwise Laurent map on
honest Laurent polynomials. -/
lemma laurent_fraction_comparison_algebraMap (p : R[T;T⁻¹]) :
    laurent_fraction_comparison (R := R) (algebraMap R[T;T⁻¹] (FractionRing R[T;T⁻¹]) p) =
      algebraMap ((FractionRing R)[T;T⁻¹]) (FractionRing ((FractionRing R)[T;T⁻¹]))
        ((AddMonoidAlgebra.mapAlgHom (M := ℤ) (Algebra.ofId R (FractionRing R))) p) := by
  -- Evaluate the fraction-field lift on a numerator before introducing any transport.
  rw [laurent_fraction_comparison]
  rw [IsFractionRing.lift_algebraMap]
  rfl

/-- Helper for Lemma 10.161.6: on base elements of `R`, the two constant routes into the common
Laurent fraction field agree. -/
lemma fractionRingToLaurentFraction_algebraMap_C (r : R) :
    laurent_fraction_comparison (R := R)
      (fractionRingToLaurentFraction (R := R) (algebraMap R (FractionRing R) r)) =
      algebraMap ((FractionRing R)[T;T⁻¹]) (FractionRing ((FractionRing R)[T;T⁻¹]))
        (LaurentPolynomial.C (algebraMap R (FractionRing R) r)) := by
  -- Evaluate the first fraction-field lift on a base scalar and rewrite it as the Laurent
  -- numerator `C r`.
  have hconst :
      fractionRingToLaurentFraction (R := R) (algebraMap R (FractionRing R) r) =
        algebraMap R[T;T⁻¹] (FractionRing R[T;T⁻¹]) (LaurentPolynomial.C r) := by
    rw [fractionRingToLaurentFraction, IsFractionRing.liftAlgHom_apply]
    rw [IsFractionRing.lift_algebraMap]
    -- Rewrite the constant Laurent polynomial through the scalar tower
    -- `R → R[T;T⁻¹] → FractionRing R[T;T⁻¹]`.
    calc
      algebraMap R (FractionRing R[T;T⁻¹]) r =
          algebraMap R[T;T⁻¹] (FractionRing R[T;T⁻¹]) (algebraMap R R[T;T⁻¹] r) := by
            simpa using
              congrArg (fun f : R →+* FractionRing R[T;T⁻¹] => f r)
                (IsScalarTower.algebraMap_eq R R[T;T⁻¹] (FractionRing R[T;T⁻¹]))
      _ =
          algebraMap R[T;T⁻¹] (FractionRing R[T;T⁻¹]) (LaurentPolynomial.C r) := by
            rw [LaurentPolynomial.C_eq_algebraMap]
  rw [hconst, laurent_fraction_comparison_algebraMap]
  -- Compare coefficients after the coefficientwise Laurent extension over `FractionRing R`.
  have hmap :
      (AddMonoidAlgebra.mapAlgHom (M := ℤ) (Algebra.ofId R (FractionRing R)))
          (LaurentPolynomial.C r) =
        LaurentPolynomial.C (algebraMap R (FractionRing R) r) := by
    ext n
    by_cases h : n = 0
    · simp [AddMonoidAlgebra.mapAlgHom_apply, LaurentPolynomial.C_apply, h]
    · simp [AddMonoidAlgebra.mapAlgHom_apply, LaurentPolynomial.C_apply, h]
  exact congrArg
    (algebraMap ((FractionRing R)[T;T⁻¹]) (FractionRing ((FractionRing R)[T;T⁻¹]))) hmap

/-- Helper for Lemma 10.161.6: the comparison map sends Laurent-normalization elements to
elements integral over `K[T;T⁻¹]`, where `K = FractionRing R`. -/
lemma laurent_fraction_comparison_isIntegral_over_fractionLaurent
    (y : integralClosure R[T;T⁻¹] (FractionRing R[T;T⁻¹])) :
    IsIntegral ((FractionRing R)[T;T⁻¹])
      (laurent_fraction_comparison (R := R) (y : FractionRing R[T;T⁻¹])) := by
  have hcomp :
      (algebraMap ((FractionRing R)[T;T⁻¹]) (FractionRing ((FractionRing R)[T;T⁻¹]))).comp
          ((AddMonoidAlgebra.mapAlgHom (M := ℤ) (Algebra.ofId R (FractionRing R))).toRingHom) =
        (laurent_fraction_comparison (R := R)).comp
          (algebraMap R[T;T⁻¹] (FractionRing R[T;T⁻¹])) := by
    apply RingHom.ext
    intro p
    exact (laurent_fraction_comparison_algebraMap (R := R) p).symm
  -- Transport the monic relation defining integrality across the comparison of fraction fields.
  exact IsIntegral.map_of_comp_eq
    (((AddMonoidAlgebra.mapAlgHom (M := ℤ) (Algebra.ofId R (FractionRing R))).toRingHom))
    (laurent_fraction_comparison (R := R)) hcomp y.2

/-- Helper for Lemma 10.161.6: every Laurent-normalization generator becomes an honest Laurent
polynomial over `FractionRing R` inside the common ambient fraction field. -/
lemma laurent_normalization_generator_lift
    (y : integralClosure R[T;T⁻¹] (FractionRing R[T;T⁻¹])) :
    ∃ g : (FractionRing R)[T;T⁻¹],
      algebraMap ((FractionRing R)[T;T⁻¹]) (FractionRing ((FractionRing R)[T;T⁻¹])) g =
        laurent_fraction_comparison (R := R) (y : FractionRing R[T;T⁻¹]) := by
  letI : IsIntegrallyClosed ((FractionRing R)[T;T⁻¹]) :=
    fractionRing_laurentPolynomial_isIntegrallyClosed (R := R)
  -- The transported normalization element lies in the integrally closed Laurent ring over `K`.
  exact IsIntegrallyClosed.algebraMap_eq_of_integral
    (laurent_fraction_comparison_isIntegral_over_fractionLaurent (R := R) y)

/-- Helper for Lemma 10.161.6: after passing to the common ambient fraction field, a constant
element of `FractionRing R` becomes the constant Laurent polynomial with that coefficient. -/
lemma laurent_fraction_comparison_constant (x : FractionRing R) :
    laurent_fraction_comparison (R := R) (fractionRingToLaurentFraction (R := R) x) =
      algebraMap ((FractionRing R)[T;T⁻¹]) (FractionRing ((FractionRing R)[T;T⁻¹]))
        (LaurentPolynomial.C x) := by
  let f₁ : FractionRing R →+* FractionRing ((FractionRing R)[T;T⁻¹]) :=
    (laurent_fraction_comparison (R := R)).comp
      (fractionRingToLaurentFraction (R := R)).toRingHom
  let f₂ : FractionRing R →+* FractionRing ((FractionRing R)[T;T⁻¹]) :=
    (algebraMap ((FractionRing R)[T;T⁻¹]) (FractionRing ((FractionRing R)[T;T⁻¹]))).comp
      (LaurentPolynomial.C : FractionRing R →+* (FractionRing R)[T;T⁻¹])
  have hmaps : f₁ = f₂ := by
    -- Both maps out of the fraction field are determined by their values on the base ring `R`.
    apply IsFractionRing.ringHom_ext (A := R)
    intro r
    -- The base case is the direct constant computation proved above.
    simpa [f₁, f₂] using fractionRingToLaurentFraction_algebraMap_C (R := R) r
  -- Evaluate the identified ring-hom equality at the chosen fraction-field element.
  simpa [f₁, f₂] using congrArg
    (fun f : FractionRing R →+* FractionRing ((FractionRing R)[T;T⁻¹]) => f x) hmaps

/-- Helper for Lemma 10.161.6: the normalization embeds linearly into any submodule containing
all of its elements. -/
noncomputable def integralClosure_to_submodule
    (P : Submodule R (FractionRing R))
    (hP : ∀ x : integralClosure R (FractionRing R), (x : FractionRing R) ∈ P) :
    integralClosure R (FractionRing R) →ₗ[R] P where
  toFun x := ⟨x, hP x⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

/-- Helper for Lemma 10.161.6: the linear map into a containing submodule is injective because
the normalization is a subtype of the fraction field. -/
lemma integralClosure_to_submodule_injective
    (P : Submodule R (FractionRing R))
    (hP : ∀ x : integralClosure R (FractionRing R), (x : FractionRing R) ∈ P) :
    Function.Injective (integralClosure_to_submodule (R := R) P hP) := by
  intro x y hxy
  apply Subtype.ext
  exact congrArg (fun z : P => (z : FractionRing R)) hxy

/-- Helper for Lemma 10.161.6: left multiplication by a single Laurent monomial shifts
coefficients by the monomial exponent. -/
lemma laurent_single_mul_apply
    (a : FractionRing R) (m k : ℤ) (g : (FractionRing R)[T;T⁻¹]) :
    ((AddMonoidAlgebra.single m a : (FractionRing R)[T;T⁻¹]) * g) k = a * g (k - m) := by
  -- Use the additive-group monoid-algebra coefficient formula and normalize the index.
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    (AddMonoidAlgebra.single_mul_apply (x := g) (r := a) (g := m) (h := k))

/-- Helper for Lemma 10.161.6: if every coefficient of `g` lies in an `R`-submodule `P`, then
multiplying `g` by a Laurent monomial with coefficient in `R` keeps every coefficient in `P`. -/
lemma coeff_C_mul_T_mul_mem_submodule
    {P : Submodule R (FractionRing R)} {g : (FractionRing R)[T;T⁻¹]}
    (hg : ∀ m : ℤ, g m ∈ P) (r : R) (m k : ℤ) :
    ((((LaurentPolynomial.C (algebraMap R (FractionRing R) r)) * LaurentPolynomial.T m) * g :
      (FractionRing R)[T;T⁻¹]) k) ∈ P := by
  -- Rewrite the Laurent monomial as a single-support term, then use `R`-submodule closure.
  rw [← LaurentPolynomial.single_eq_C_mul_T]
  rw [laurent_single_mul_apply]
  simpa [Algebra.smul_def] using P.smul_mem r (hg (k - m))

/-- Helper for Lemma 10.161.6: the coefficientwise Laurent extension is the canonical finite sum
of mapped Laurent monomials. -/
lemma mapAlgHom_laurent_eq_sum_single (p : R[T;T⁻¹]) :
    AddMonoidAlgebra.mapAlgHom (M := ℤ) (Algebra.ofId R (FractionRing R)) p =
      p.sum (fun m r ↦ AddMonoidAlgebra.single m (algebraMap R (FractionRing R) r)) := by
  classical
  ext k
  rw [Finsupp.sum]
  let ev : (FractionRing R)[T;T⁻¹] →+ FractionRing R :=
    { toFun := fun f ↦ f k
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  have hsum_apply :
      (∑ a ∈ p.support, AddMonoidAlgebra.single a (algebraMap R (FractionRing R) (p a))) k =
        ∑ a ∈ p.support,
          (AddMonoidAlgebra.single a (algebraMap R (FractionRing R) (p a)) :
            (FractionRing R)[T;T⁻¹]) k := by
    change
      ev (∑ a ∈ p.support,
        (AddMonoidAlgebra.single a (algebraMap R (FractionRing R) (p a)) :
          (FractionRing R)[T;T⁻¹])) =
        ∑ a ∈ p.support,
          ev (AddMonoidAlgebra.single a (algebraMap R (FractionRing R) (p a)) :
            (FractionRing R)[T;T⁻¹])
    exact map_sum ev
      (fun x ↦
        (AddMonoidAlgebra.single x (algebraMap R (FractionRing R) (p x)) :
          (FractionRing R)[T;T⁻¹]))
      p.support
  rw [hsum_apply]
  by_cases hk : k ∈ p.support
  · have hsum :
        ∑ x ∈ p.support,
            (AddMonoidAlgebra.single x (algebraMap R (FractionRing R) (p x)) :
              (FractionRing R)[T;T⁻¹]) k =
            (AddMonoidAlgebra.single k (algebraMap R (FractionRing R) (p k)) :
              (FractionRing R)[T;T⁻¹]) k := by
      refine Finset.sum_eq_single k ?_ ?_
      · intro x hx hxk
        simpa only [Finsupp.single_apply, hxk, if_false]
      · intro hk'
        exact (hk' hk).elim
    have hsingle :
        (AddMonoidAlgebra.single k (algebraMap R (FractionRing R) (p k)) :
          (FractionRing R)[T;T⁻¹]) k =
          algebraMap R (FractionRing R) (p k) := by
      simpa only [Finsupp.single_apply, if_true]
    calc
      (AddMonoidAlgebra.mapAlgHom (M := ℤ) (Algebra.ofId R (FractionRing R)) p) k =
          algebraMap R (FractionRing R) (p k) := by
            simp [AddMonoidAlgebra.mapAlgHom_apply]
      _ =
          (AddMonoidAlgebra.single k (algebraMap R (FractionRing R) (p k)) :
            (FractionRing R)[T;T⁻¹]) k := by
            exact hsingle.symm
      _ =
          ∑ x ∈ p.support,
            (AddMonoidAlgebra.single x (algebraMap R (FractionRing R) (p x)) :
              (FractionRing R)[T;T⁻¹]) k := by
            exact hsum.symm
  · have hsum :
        ∑ x ∈ p.support,
            (AddMonoidAlgebra.single x (algebraMap R (FractionRing R) (p x)) :
              (FractionRing R)[T;T⁻¹]) k = 0 := by
      refine Finset.sum_eq_zero ?_
      intro x hx
      have hxk : x ≠ k := by
        intro h
        apply hk
        simpa [h] using hx
      simpa only [Finsupp.single_apply, hxk, if_false]
    calc
      (AddMonoidAlgebra.mapAlgHom (M := ℤ) (Algebra.ofId R (FractionRing R)) p) k = 0 := by
        simp [AddMonoidAlgebra.mapAlgHom_apply, Finsupp.notMem_support_iff.mp hk]
      _ =
          ∑ x ∈ p.support,
            (AddMonoidAlgebra.single x (algebraMap R (FractionRing R) (p x)) :
              (FractionRing R)[T;T⁻¹]) k := by
            simpa using hsum.symm

/-- Helper for Lemma 10.161.6: if every coefficient of `g` lies in an `R`-submodule `P`, then
the same holds after left multiplication by any Laurent polynomial coming from `R[T;T⁻¹]`. -/
lemma coeff_mem_submodule_of_laurent_mul
    {P : Submodule R (FractionRing R)} {g : (FractionRing R)[T;T⁻¹]}
    (hg : ∀ m : ℤ, g m ∈ P) (p : R[T;T⁻¹]) (k : ℤ) :
    (((AddMonoidAlgebra.mapAlgHom (M := ℤ) (Algebra.ofId R (FractionRing R)) p) * g) k) ∈ P := by
  -- Decompose the Laurent multiplier into finitely many mapped monomials.
  rw [mapAlgHom_laurent_eq_sum_single]
  rw [Finsupp.sum, Finset.sum_mul]
  let ev : (FractionRing R)[T;T⁻¹] →+ FractionRing R :=
    { toFun := fun f ↦ f k
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  have hsum_apply :
      (∑ i ∈ p.support, AddMonoidAlgebra.single i (algebraMap R (FractionRing R) (p i)) * g) k =
        ∑ i ∈ p.support,
          ((AddMonoidAlgebra.single i (algebraMap R (FractionRing R) (p i)) * g :
            (FractionRing R)[T;T⁻¹]) k) := by
    change
      ev (∑ i ∈ p.support,
        (AddMonoidAlgebra.single i (algebraMap R (FractionRing R) (p i)) * g :
          (FractionRing R)[T;T⁻¹])) =
        ∑ i ∈ p.support,
          ev (AddMonoidAlgebra.single i (algebraMap R (FractionRing R) (p i)) * g :
            (FractionRing R)[T;T⁻¹])
    exact map_sum ev
      (fun x ↦
        (AddMonoidAlgebra.single x (algebraMap R (FractionRing R) (p x)) * g :
          (FractionRing R)[T;T⁻¹]))
      p.support
  rw [hsum_apply]
  -- Each monomial summand preserves coefficient membership by the previous lemma.
  exact Submodule.sum_mem P fun m hm ↦ by
    simpa [← LaurentPolynomial.single_eq_C_mul_T] using
      (coeff_C_mul_T_mul_mem_submodule (R := R) (P := P) (g := g) hg (p m) m k)

/-- Helper for Lemma 10.161.6: every coefficient of the chosen Laurent lifts lies in the span of
the finite coefficient set obtained by collecting the support coefficients of all lifts. -/
lemma coeff_mem_span_of_generator_coeffs
    {n : ℕ} (g : Fin n → (FractionRing R)[T;T⁻¹]) (i : Fin n) (m : ℤ) :
    g i m ∈
      Submodule.span R
        {a : FractionRing R | ∃ j : Fin n, ∃ k ∈ (g j).support, g j k = a} := by
  by_cases hm : m ∈ (g i).support
  · -- A supported coefficient appears explicitly in the finite union of coefficient images.
    exact Submodule.subset_span ⟨i, m, hm, rfl⟩
  · -- Outside the support the coefficient vanishes, so it lies in the span automatically.
    have hzero : g i m = 0 := Finsupp.notMem_support_iff.mp hm
    simpa [hzero] using
      (Submodule.zero_mem
        (Submodule.span R
          {a : FractionRing R | ∃ j : Fin n, ∃ k ∈ (g j).support, g j k = a}))

/-- Helper for Lemma 10.161.6: coefficients of Laurent combinations of chosen generators stay in
the `R`-submodule already spanned by the generator coefficients. -/
lemma coeff_mem_span_of_laurent_linear_combination
    {n : ℕ} (g : Fin n → (FractionRing R)[T;T⁻¹]) (coeffs : Finset (FractionRing R))
    (hg : ∀ i : Fin n, ∀ m : ℤ, g i m ∈ Submodule.span R (↑coeffs : Set (FractionRing R)))
    (c : Fin n → R[T;T⁻¹]) (k : ℤ) :
    ((∑ i, (AddMonoidAlgebra.mapAlgHom (M := ℤ) (Algebra.ofId R (FractionRing R)) (c i)) * g i) k) ∈
      Submodule.span R (↑coeffs : Set (FractionRing R)) := by
  let P : Submodule R (FractionRing R) := Submodule.span R (↑coeffs : Set (FractionRing R))
  have hsummand :
      ∀ i : Fin n, (((AddMonoidAlgebra.mapAlgHom (M := ℤ)
        (Algebra.ofId R (FractionRing R)) (c i)) * g i) k) ∈ P := by
    intro i
    -- Apply the one-generator coefficient-closure lemma to the `i`-th summand.
    exact coeff_mem_submodule_of_laurent_mul (R := R) (P := P) (g := g i) (hg i) (c i) k
  let ev : (FractionRing R)[T;T⁻¹] →+ FractionRing R :=
    { toFun := fun f ↦ f k
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  have hsum_apply :
      (∑ i, (AddMonoidAlgebra.mapAlgHom (M := ℤ) (Algebra.ofId R (FractionRing R)) (c i)) * g i) k =
        ∑ i,
          (((AddMonoidAlgebra.mapAlgHom (M := ℤ) (Algebra.ofId R (FractionRing R)) (c i)) * g i) k) := by
    change
      ev (∑ i,
        ((AddMonoidAlgebra.mapAlgHom (M := ℤ) (Algebra.ofId R (FractionRing R)) (c i)) * g i :
          (FractionRing R)[T;T⁻¹])) =
        ∑ i,
          ev ((AddMonoidAlgebra.mapAlgHom (M := ℤ) (Algebra.ofId R (FractionRing R)) (c i)) * g i :
            (FractionRing R)[T;T⁻¹])
    exact map_sum ev
      (fun i : Fin n ↦
        ((AddMonoidAlgebra.mapAlgHom (M := ℤ) (Algebra.ofId R (FractionRing R)) (c i)) * g i :
          (FractionRing R)[T;T⁻¹]))
      Finset.univ
  rw [hsum_apply]
  exact Submodule.sum_mem P (fun i _ ↦ hsummand i)

/-- Helper for Lemma 10.161.6: reading off coefficient `0` from a Laurent identity shows that the
constant term belongs to the coefficient span. -/
lemma coeff_zero_mem_span_after_transport
    {n : ℕ} (g : Fin n → (FractionRing R)[T;T⁻¹]) (coeffs : Finset (FractionRing R))
    (hg : ∀ i : Fin n, ∀ m : ℤ, g i m ∈ Submodule.span R (↑coeffs : Set (FractionRing R)))
    {x : FractionRing R} {c : Fin n → R[T;T⁻¹]}
    (hEq : LaurentPolynomial.C x =
      ∑ i, (AddMonoidAlgebra.mapAlgHom (M := ℤ) (Algebra.ofId R (FractionRing R)) (c i)) * g i) :
    x ∈ Submodule.span R (↑coeffs : Set (FractionRing R)) := by
  let P : Submodule R (FractionRing R) := Submodule.span R (↑coeffs : Set (FractionRing R))
  have hcoeff :
      x = ((∑ i, (AddMonoidAlgebra.mapAlgHom (M := ℤ)
        (Algebra.ofId R (FractionRing R)) (c i)) * g i) 0) := by
    -- Coefficient `0` of a constant Laurent polynomial is the constant itself.
    simpa [LaurentPolynomial.C_apply] using congrArg
      (fun p : (FractionRing R)[T;T⁻¹] => p 0) hEq
  have hspan :
      ((∑ i, (AddMonoidAlgebra.mapAlgHom (M := ℤ)
        (Algebra.ofId R (FractionRing R)) (c i)) * g i) 0) ∈ P :=
    coeff_mem_span_of_laurent_linear_combination (R := R) g coeffs hg c 0
  exact hcoeff.symm ▸ hspan

/-- Helper for Lemma 10.161.6: the Laurent combination obtained by applying the coefficientwise
map to the chosen coefficients and multiplying by the lifted generators. -/
noncomputable def lifted_generator_combination {n : ℕ}
    (lifted : Fin n → (FractionRing R)[T;T⁻¹]) (c : Fin n → R[T;T⁻¹]) :
    (FractionRing R)[T;T⁻¹] :=
  ∑ i, (AddMonoidAlgebra.mapAlgHom (M := ℤ) (Algebra.ofId R (FractionRing R)) (c i)) * lifted i

-- Proof sketch: let `R'` be the integral closure of `R` in `FractionRing R`, and let `S'` be the
-- integral closure of `R[T;T⁻¹]` in its fraction field. The `N-1` hypothesis makes `S'` finite
-- over the Laurent polynomial ring. Expanding finitely many generators as finite Laurent sums
-- shows every element of `R'` lies in a finite `R`-submodule of `FractionRing R`; since `R` is
-- Noetherian, `R'` is finite over `R`.
set_option maxHeartbeats 1000000 in
/-- Lemma 10.161.6: if `R` is a Noetherian domain and the Laurent polynomial ring
`R[z, z^{-1}]`, formalized by the canonical owner `R[T;T⁻¹]`, is `N-1`, then `R` is `N-1`. -/
theorem isN1Ring_of_isN1Ring_laurentPolynomial
    (hLaurent : IsN1Ring R[T;T⁻¹]) :
    IsN1Ring R := by
  classical
  letI : IsN1Ring R[T;T⁻¹] := hLaurent
  let K := FractionRing R
  let S := integralClosure R[T;T⁻¹] (FractionRing R[T;T⁻¹])
  refine ⟨?_⟩
  -- Use the Laurent `N-1` hypothesis to choose finitely many generators of the Laurent
  -- normalization.
  have hfiniteS : Module.Finite R[T;T⁻¹] S := by
    change Module.Finite R[T;T⁻¹]
      (integralClosure R[T;T⁻¹] (FractionRing R[T;T⁻¹]))
    infer_instance
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R[T;T⁻¹] S
  let generators : Fin n → S := fun i => f (Pi.single i 1)
  have hconst :
      ∀ x : integralClosure R K,
        ∃ c : Fin n → R[T;T⁻¹],
          f c = integralClosure_constants_map_to_laurent_normalization (R := R) x := by
    intro x
    exact hf _
  choose lifted hlifted using fun i : Fin n ↦
    laurent_normalization_generator_lift (R := R) (generators i)
  let coeffs : Finset (FractionRing R) :=
    Finset.univ.biUnion fun i ↦ (lifted i).support.image fun m ↦ lifted i m
  let P : Submodule R K := Submodule.span R (↑coeffs : Set K)
  have hcoeffs :
      ∀ i : Fin n, ∀ m : ℤ, lifted i m ∈ P := by
    intro i m
    by_cases hm : m ∈ (lifted i).support
    · -- Supported coefficients are explicit members of the finite coefficient set.
      exact Submodule.subset_span <| by
        change lifted i m ∈ (↑coeffs : Set K)
        refine Finset.mem_biUnion.mpr ?_
        exact ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ⟨m, hm, rfl⟩⟩
    · -- Off-support coefficients vanish, so they lie in the span automatically.
      have hzero : lifted i m = 0 := Finsupp.notMem_support_iff.mp hm
      simpa [P, hzero] using (Submodule.zero_mem P)
  have hcontain :
      ∀ x : integralClosure R K, (x : K) ∈ P := by
    intro x
    obtain ⟨c, hc⟩ := hconst x
    have hPi :
        c = ∑ i, Pi.single i (c i) := by
      simpa using
        (LinearMap.sum_single_apply (φ := fun _ : Fin n ↦ R[T;T⁻¹]) (v := c)).symm
    have hsum :
        f c = ∑ i, c i • generators i := by
      calc
        f c = f (∑ i, Pi.single i (c i)) := by
          exact congrArg f hPi
        _ = ∑ i, f (Pi.single i (c i)) := by
          simpa using (map_sum f (fun i : Fin n ↦ Pi.single i (c i)) Finset.univ)
        _ = ∑ i, c i • generators i := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          have hsingle :
              Pi.single i (c i) =
                c i • (Pi.single i (1 : R[T;T⁻¹]) : Fin n → R[T;T⁻¹]) := by
            ext j
            by_cases hji : j = i
            · subst hji
              simp
            · simp [Pi.single, hji]
          -- Rewrite each basis-vector image as the chosen generator.
          rw [hsingle, LinearMap.map_smul]
    have hdecomp :
        integralClosure_constants_map_to_laurent_normalization (R := R) x =
          ∑ i, c i • generators i := by
      exact hc.symm.trans hsum
    have htransport :
        LaurentPolynomial.C (x : K) =
          lifted_generator_combination (R := R) lifted c := by
      let rhs : (FractionRing R)[T;T⁻¹] := lifted_generator_combination (R := R) lifted c
      have hambient :
          algebraMap ((FractionRing R)[T;T⁻¹]) (FractionRing ((FractionRing R)[T;T⁻¹]))
              (LaurentPolynomial.C (x : FractionRing R)) =
            algebraMap ((FractionRing R)[T;T⁻¹]) (FractionRing ((FractionRing R)[T;T⁻¹])) rhs := by
        let transport :
            integralClosure R[T;T⁻¹] (FractionRing R[T;T⁻¹]) →
              FractionRing ((FractionRing R)[T;T⁻¹]) :=
          fun s ↦ laurent_fraction_comparison (R := R) (s : FractionRing R[T;T⁻¹])
        have htransport :
            laurent_fraction_comparison (R := R)
                ((∑ i, c i • generators i :
                  integralClosure R[T;T⁻¹] (FractionRing R[T;T⁻¹])) :
                  FractionRing R[T;T⁻¹]) =
              algebraMap ((FractionRing R)[T;T⁻¹]) (FractionRing ((FractionRing R)[T;T⁻¹])) rhs := by
          have hcoe :
              ((∑ i, c i • generators i :
                integralClosure R[T;T⁻¹] (FractionRing R[T;T⁻¹])) :
                FractionRing R[T;T⁻¹]) =
                ∑ i, algebraMap R[T;T⁻¹] (FractionRing R[T;T⁻¹]) (c i) *
                  (generators i : FractionRing R[T;T⁻¹]) := by
            simpa [Algebra.smul_def]
          calc
            laurent_fraction_comparison (R := R)
                ((∑ i, c i • generators i :
                  integralClosure R[T;T⁻¹] (FractionRing R[T;T⁻¹])) :
                  FractionRing R[T;T⁻¹]) =
                laurent_fraction_comparison (R := R)
                  (∑ i, algebraMap R[T;T⁻¹] (FractionRing R[T;T⁻¹]) (c i) *
                    (generators i : FractionRing R[T;T⁻¹])) := by
                      rw [hcoe]
            _ = ∑ i, laurent_fraction_comparison (R := R)
                  (algebraMap R[T;T⁻¹] (FractionRing R[T;T⁻¹]) (c i) *
                    (generators i : FractionRing R[T;T⁻¹])) := by
                  exact map_sum (laurent_fraction_comparison (R := R)).toAddMonoidHom
                    (fun i : Fin n ↦
                      (algebraMap R[T;T⁻¹] (FractionRing R[T;T⁻¹]) (c i) *
                        (generators i : FractionRing R[T;T⁻¹]) :
                          FractionRing R[T;T⁻¹]))
                    Finset.univ
            _ = ∑ i,
                  algebraMap ((FractionRing R)[T;T⁻¹]) (FractionRing ((FractionRing R)[T;T⁻¹]))
                    ((AddMonoidAlgebra.mapAlgHom (M := ℤ)
                      (Algebra.ofId R (FractionRing R)) (c i)) * lifted i) := by
                  refine Finset.sum_congr rfl fun i _ ↦ ?_
                  calc
                    laurent_fraction_comparison (R := R)
                        (algebraMap R[T;T⁻¹] (FractionRing R[T;T⁻¹]) (c i) *
                          (generators i : FractionRing R[T;T⁻¹])) =
                        laurent_fraction_comparison (R := R)
                          (algebraMap R[T;T⁻¹] (FractionRing R[T;T⁻¹]) (c i)) *
                            laurent_fraction_comparison (R := R)
                              (generators i : FractionRing R[T;T⁻¹]) := by
                                rw [map_mul]
                    _ =
                        algebraMap ((FractionRing R)[T;T⁻¹])
                          (FractionRing ((FractionRing R)[T;T⁻¹]))
                          ((AddMonoidAlgebra.mapAlgHom (M := ℤ)
                            (Algebra.ofId R (FractionRing R)) (c i))) *
                            algebraMap ((FractionRing R)[T;T⁻¹])
                              (FractionRing ((FractionRing R)[T;T⁻¹])) (lifted i) := by
                                rw [laurent_fraction_comparison_algebraMap, ← hlifted i]
                    _ =
                        algebraMap ((FractionRing R)[T;T⁻¹]) (FractionRing ((FractionRing R)[T;T⁻¹]))
                          ((AddMonoidAlgebra.mapAlgHom (M := ℤ)
                            (Algebra.ofId R (FractionRing R)) (c i)) * lifted i) := by
                                symm
                                rw [map_mul]
            _ = algebraMap ((FractionRing R)[T;T⁻¹]) (FractionRing ((FractionRing R)[T;T⁻¹])) rhs := by
                  dsimp [rhs, lifted_generator_combination]
                  exact (map_sum
                    (RingHom.toAddMonoidHom
                      (algebraMap ((FractionRing R)[T;T⁻¹])
                        (FractionRing ((FractionRing R)[T;T⁻¹]))))
                    (fun i : Fin n ↦
                      ((AddMonoidAlgebra.mapAlgHom (M := ℤ)
                        (Algebra.ofId R (FractionRing R)) (c i)) * lifted i :
                          (FractionRing R)[T;T⁻¹]))
                    Finset.univ).symm
        -- Transport the normalization identity into the common Laurent fraction field.
        calc
          algebraMap ((FractionRing R)[T;T⁻¹]) (FractionRing ((FractionRing R)[T;T⁻¹]))
              (LaurentPolynomial.C (x : FractionRing R)) =
            laurent_fraction_comparison (R := R)
              (integralClosure_constants_map_to_laurent_normalization (R := R) x :
                FractionRing R[T;T⁻¹]) := by
                  symm
                  exact laurent_fraction_comparison_constant (R := R) (x : FractionRing R)
          _ =
            laurent_fraction_comparison (R := R)
              ((∑ i, c i • generators i :
                integralClosure R[T;T⁻¹] (FractionRing R[T;T⁻¹])) :
                FractionRing R[T;T⁻¹]) := by
                  exact congrArg transport hdecomp
          _ =
            algebraMap ((FractionRing R)[T;T⁻¹]) (FractionRing ((FractionRing R)[T;T⁻¹])) rhs := htransport
      simpa [rhs] using
        (IsFractionRing.injective ((FractionRing R)[T;T⁻¹])
          (FractionRing ((FractionRing R)[T;T⁻¹]))) hambient
    -- Taking coefficient `0` of the transported Laurent identity lands back in the coefficient
    -- span generated by the finitely many chosen Laurent lifts.
    simpa [lifted_generator_combination] using
      (coeff_zero_mem_span_after_transport (R := R) lifted coeffs hcoeffs htransport)
  have hfiniteP : Module.Finite R P :=
    coeff_span_finite (R := R) (s := (↑coeffs : Set K)) coeffs.finite_toSet
  letI : Module.Finite R P := hfiniteP
  -- Embed the normalization into the finite submodule that contains all of its elements.
  exact Module.Finite.of_injective
    (integralClosure_to_submodule (R := R) P hcontain)
    (integralClosure_to_submodule_injective (R := R) P hcontain)

end
