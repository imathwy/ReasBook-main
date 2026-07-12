import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule
import Mathlib.RingTheory.GradedAlgebra.RingHom
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Subsemiring
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped Polynomial

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {𝒜 : ℕ → AddSubgroup R} [GradedRing 𝒜]
variable {ℬ : ℕ → AddSubgroup S} [GradedRing ℬ]

/-- Helper for Lemma 10.56.3: the zeroth graded projection commutes with the structure map of a
graded ring homomorphism. -/
lemma proj_zero_algebraMap_eq [Algebra R S]
    (hgraded : ∀ i {r : R}, r ∈ 𝒜 i → algebraMap R S r ∈ ℬ i) (r : R) :
    GradedRing.projZeroRingHom ℬ (algebraMap R S r) =
      algebraMap R S (GradedRing.projZeroRingHom 𝒜 r) := by
  let f : 𝒜 →+*ᵍ ℬ :=
    { __ := algebraMap R S
      map_mem := fun {i} {x} hx => hgraded i hx }
  -- The graded ring map commutes with direct-sum decomposition, hence also with the degree-zero
  -- projection.
  rw [GradedRing.projZeroRingHom_apply, GradedRing.projZeroRingHom_apply]
  exact (GradedRingHom.map_directSumDecompose (𝒜 := 𝒜) (ℬ := ℬ) f (x := r) (i := 0)).symm

/-- Helper for Lemma 10.56.3: the degree-zero component of an integral element is still integral
over the base ring. -/
lemma isIntegral_proj_zero [Algebra R S]
    (hgraded : ∀ i {r : R}, r ∈ 𝒜 i → algebraMap R S r ∈ ℬ i) {x : S}
    (hx : IsIntegral R x) :
    IsIntegral R (GradedRing.proj ℬ 0 x) := by
  have hcomp :
      (algebraMap R S).comp (GradedRing.projZeroRingHom 𝒜) =
        (GradedRing.projZeroRingHom ℬ).comp (algebraMap R S) := by
    -- The compatibility needed by `IsIntegral.map_of_comp_eq` is exactly the gradedness of the
    -- structure map at degree zero.
    ext r
    simpa [RingHom.comp_apply] using (proj_zero_algebraMap_eq hgraded r).symm
  -- Apply the integral polynomial through the compatible degree-zero projection map.
  have hzero : IsIntegral R (GradedRing.projZeroRingHom ℬ x) :=
    IsIntegral.map_of_comp_eq (φ := GradedRing.projZeroRingHom 𝒜)
      (ψ := GradedRing.projZeroRingHom ℬ) hcomp hx
  simpa [GradedRing.proj_apply, GradedRing.projZeroRingHom_apply] using hzero

/-- Helper for Lemma 10.56.3: every graded ring homomorphism preserves each homogeneous
projection. -/
lemma proj_algebraMap_eq [Algebra R S]
    (hgraded : ∀ i {r : R}, r ∈ 𝒜 i → algebraMap R S r ∈ ℬ i) (i : ℕ) (r : R) :
    GradedRing.proj ℬ i (algebraMap R S r) =
      algebraMap R S (GradedRing.proj 𝒜 i r) := by
  let f : 𝒜 →+*ᵍ ℬ :=
    { __ := algebraMap R S
      map_mem := fun {j} {x} hx => hgraded j hx }
  -- The graded ring map commutes with the direct-sum decomposition degree by degree.
  exact (GradedRingHom.map_directSumDecompose (𝒜 := 𝒜) (ℬ := ℬ) f (x := r) (i := i)).symm

/-- Helper for Lemma 10.56.3: the degree-zero generator of the direct sum maps to the constant
polynomial `1`. -/
lemma gradingToPolynomial_hone (ℬ : ℕ → AddSubgroup S) [GradedRing ℬ] :
    ((Polynomial.monomial 0).toAddMonoidHom.comp (AddSubgroupClass.subtype (ℬ 0)))
      (1 : ℬ 0) = (1 : S[X]) := by
  -- The degree-zero homogeneous unit gives the constant polynomial.
  simp

/-- Helper for Lemma 10.56.3: multiplication of homogeneous pieces becomes multiplication of the
corresponding monomials. -/
lemma gradingToPolynomial_hmul (ℬ : ℕ → AddSubgroup S) [GradedRing ℬ]
    {i j : ℕ} (ai : ℬ i) (aj : ℬ j) :
    ((Polynomial.monomial (i + j)).toAddMonoidHom.comp
        (AddSubgroupClass.subtype (ℬ (i + j))))
        ⟨(ai : S) * (aj : S), SetLike.GradedMul.mul_mem ai.2 aj.2⟩ =
      ((Polynomial.monomial i).toAddMonoidHom.comp (AddSubgroupClass.subtype (ℬ i))) ai *
        ((Polynomial.monomial j).toAddMonoidHom.comp (AddSubgroupClass.subtype (ℬ j))) aj := by
  -- Multiplication of monomials records both the degree sum and the coefficient product.
  simpa using (Polynomial.monomial_mul_monomial i j (ai : S) (aj : S)).symm

/-- Helper for Lemma 10.56.3: the canonical polynomial attached to a graded element is the sum of
its homogeneous components placed in the corresponding degrees. -/
noncomputable def gradingToPolynomialRingHom (ℬ : ℕ → AddSubgroup S) [GradedRing ℬ] :
    S →+* S[X] :=
  let f : ∀ i, ℬ i →+ S[X] :=
    fun i => (Polynomial.monomial i).toAddMonoidHom.comp (AddSubgroupClass.subtype (ℬ i))
  (DirectSum.toSemiring f (gradingToPolynomial_hone (ℬ := ℬ))
      fun {_ _} ai aj => gradingToPolynomial_hmul (ℬ := ℬ) ai aj).comp
    (DirectSum.decomposeRingEquiv ℬ).toRingHom

/-- Helper for Lemma 10.56.3: the coefficient of degree `i` in the grading polynomial is the `i`th
homogeneous projection. -/
lemma coeff_gradingToPolynomialRingHom (i : ℕ) (x : S) :
    (gradingToPolynomialRingHom (ℬ := ℬ) x).coeff i = GradedRing.proj ℬ i x := by
  letI : ∀ j (y : ℬ j), Decidable (y ≠ 0) := fun _ y => by
    classical
    exact inferInstance
  -- Expand the direct-sum decomposition of `x`, then read off the `i`th coefficient.
  change
    ((DirectSum.toSemiring
        (fun i =>
          (Polynomial.monomial i).toAddMonoidHom.comp (AddSubgroupClass.subtype (ℬ i)))
        (gradingToPolynomial_hone (ℬ := ℬ))
        (fun {i j} ai aj => gradingToPolynomial_hmul (ℬ := ℬ) ai aj))
      (DirectSum.decompose ℬ x)).coeff i = GradedRing.proj ℬ i x
  rw [← DirectSum.sum_support_of (DirectSum.decompose ℬ x), map_sum, Polynomial.finset_sum_coeff]
  by_cases hi : i ∈ (DirectSum.decompose ℬ x).support
  · rw [Finset.sum_eq_single i]
    · simpa [DirectSum.toSemiring_of, AddMonoidHom.comp_apply, Polynomial.coeff_monomial,
        GradedRing.proj_apply]
    · intro j hj hji
      simpa [DirectSum.toSemiring_of, AddMonoidHom.comp_apply, Polynomial.coeff_monomial, hji]
    · intro hnot
      exact (hnot hi).elim
  · have hzero : GradedRing.proj ℬ i x = 0 := by
      by_contra hne
      exact hi ((GradedRing.mem_support_iff (𝒜 := ℬ) x i).2 hne)
    rw [Finset.sum_eq_zero]
    · simpa [hzero]
    · intro j hj
      by_cases hji : j = i
      · subst hji
        exact (hi hj).elim
      · simpa [DirectSum.toSemiring_of, AddMonoidHom.comp_apply, Polynomial.coeff_monomial, hji]

/-- Helper for Lemma 10.56.3: expanding the grading polynomial recovers the finite sum over the
direct-sum support. -/
lemma gradingToPolynomialRingHom_apply [∀ i (x : ℬ i), Decidable (x ≠ 0)] (x : S) :
    gradingToPolynomialRingHom (ℬ := ℬ) x =
      ∑ i ∈ (DirectSum.decompose ℬ x).support, Polynomial.monomial i (GradedRing.proj ℬ i x) := by
  ext i
  -- Equality of polynomials is equality of their coefficients, and the coefficient formula is
  -- exactly the previous helper.
  rw [coeff_gradingToPolynomialRingHom, Polynomial.finset_sum_coeff]
  by_cases hi : i ∈ (DirectSum.decompose ℬ x).support
  · rw [Finset.sum_eq_single i]
    · rw [Polynomial.coeff_monomial]
      simp
    · intro j hj hji
      rw [Polynomial.coeff_monomial]
      simp [hji]
    · intro hnot
      exact (hnot hi).elim
  · rw [Finset.sum_eq_zero]
    · have hzero : GradedRing.proj ℬ i x = 0 := by
        by_contra hne
        exact hi ((GradedRing.mem_support_iff (𝒜 := ℬ) x i).2 hne)
      simpa [hzero]
    · intro j hj
      rw [Polynomial.coeff_monomial]
      by_cases hji : j = i
      · subst hji
        exact (hi hj).elim
      · simp [hji]

/-- Helper for Lemma 10.56.3: the grading polynomial commutes with the structure map of a graded
ring homomorphism. -/
lemma gradingToPolynomialRingHom_algebraMap [Algebra R S]
    (hgraded : ∀ i {r : R}, r ∈ 𝒜 i → algebraMap R S r ∈ ℬ i) (r : R) :
    gradingToPolynomialRingHom (ℬ := ℬ) (algebraMap R S r) =
      Polynomial.map (algebraMap R S) (gradingToPolynomialRingHom (ℬ := 𝒜) r) := by
  ext i
  -- Equality of coefficients reduces the compatibility to the projection-level commutation lemma.
  rw [Polynomial.coeff_map, coeff_gradingToPolynomialRingHom, coeff_gradingToPolynomialRingHom]
  exact proj_algebraMap_eq hgraded i r

/-- Helper for Lemma 10.56.3: every homogeneous projection of an integral element is integral. -/
lemma isIntegral_proj [Algebra R S]
    (hgraded : ∀ i {r : R}, r ∈ 𝒜 i → algebraMap R S r ∈ ℬ i) {i : ℕ} {x : S}
    (hx : IsIntegral R x) :
    IsIntegral R (GradedRing.proj ℬ i x) := by
  letI : Algebra R[X] S[X] := Polynomial.algebra R S
  have hcomp :
      (algebraMap R[X] S[X]).comp (gradingToPolynomialRingHom (ℬ := 𝒜)) =
        (gradingToPolynomialRingHom (ℬ := ℬ)).comp (algebraMap R S) := by
    -- The grading polynomial construction is functorial for the graded structure map.
    ext r n
    change
      (Polynomial.map (algebraMap R S) ((gradingToPolynomialRingHom (ℬ := 𝒜)) r)).coeff n =
        ((gradingToPolynomialRingHom (ℬ := ℬ)) ((algebraMap R S) r)).coeff n
    rw [Polynomial.coeff_map, coeff_gradingToPolynomialRingHom, coeff_gradingToPolynomialRingHom]
    exact (proj_algebraMap_eq hgraded n r).symm
  have hpoly : IsIntegral R[X] (gradingToPolynomialRingHom (ℬ := ℬ) x) :=
    IsIntegral.map_of_comp_eq (φ := gradingToPolynomialRingHom (ℬ := 𝒜))
      (ψ := gradingToPolynomialRingHom (ℬ := ℬ)) hcomp hx
  -- Once the whole grading polynomial is integral over `R[X]`, each coefficient is integral over
  -- `R`.
  have hcoeff :
      IsIntegral R ((gradingToPolynomialRingHom (ℬ := ℬ) x).coeff i) :=
    (Polynomial.isIntegral_iff_isIntegral_coeff.mp hpoly) i
  simpa [coeff_gradingToPolynomialRingHom] using hcoeff

/-- Lemma 10.56.3: if the structure map `R → S` preserves the `ℕ`-gradings, then the integral
closure of `R` in `S` is a graded `R`-subalgebra of `S`. The canonical owner-level Lean form is
that the underlying subsemiring of `integralClosure R S` is homogeneous for the grading on `S`. -/
-- Proof sketch: equip the target with the algebra structure coming from the graded ring
-- homomorphism, then package all homogeneous pieces into a single grading polynomial; integrality
-- of that polynomial forces integrality of each coefficient.
@[stacks 077G]
lemma integralClosure_isHomogeneous [Algebra R S]
    (hgraded : ∀ i {r : R}, r ∈ 𝒜 i → algebraMap R S r ∈ ℬ i) :
    DirectSum.SetLike.IsHomogeneous ℬ (integralClosure R S).toSubsemiring := by
  intro i x hx
  -- Route correction: instead of reconstructing the Laurent-polynomial induction inline, use the
  -- canonical grading polynomial whose coefficients are exactly the homogeneous projections.
  change IsIntegral R (GradedRing.proj ℬ i x)
  exact isIntegral_proj hgraded hx

/-- Companion bridge: the owner-level homogeneous-subsemiring statement implies the homogeneous
`R`-submodule statement for the same integral closure. -/
theorem integralClosure_toSubmodule_isHomogeneous [Algebra R S]
    (hgraded : ∀ i {r : R}, r ∈ 𝒜 i → algebraMap R S r ∈ ℬ i) :
    (integralClosure R S).toSubmodule.IsHomogeneous ℬ := by
  simpa [Submodule.IsHomogeneous] using integralClosure_isHomogeneous hgraded

end
