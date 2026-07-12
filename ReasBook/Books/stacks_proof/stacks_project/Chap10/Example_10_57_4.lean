import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped DirectSum
open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace Polynomial

variable (R : Type u) [CommRing R]

/-- The standard `ℕ`-grading on `R[X]`, transported from the canonical grading on the additive
monoid algebra model `R[ℕ]` via `Polynomial.toFinsuppIsoLinear`. -/
abbrev standardGrading (n : ℕ) : Submodule R R[X] :=
  Submodule.map (Polynomial.toFinsuppIsoLinear R).symm.toLinearMap (AddMonoidAlgebra.grade R n)

instance instSetLikeGradedMonoidStandardGrading : SetLike.GradedMonoid (standardGrading R) where
  one_mem := by
    refine ⟨AddMonoidAlgebra.single 0 (1 : R), AddMonoidAlgebra.single_mem_grade 0 1, ?_⟩
    ext n
    change
      ((Polynomial.toFinsuppIso R).symm (AddMonoidAlgebra.single 0 (1 : R))).coeff n =
        (1 : R[X]).coeff n
    rw [Polynomial.toFinsuppIso_symm_apply, Polynomial.coeff_ofFinsupp, AddMonoidAlgebra.single_apply]
    simp [coeff_one, eq_comm]
  mul_mem {i j} a b ha hb := by
    rcases ha with ⟨a', ha', rfl⟩
    rcases hb with ⟨b', hb', rfl⟩
    refine ⟨a' * b', SetLike.mul_mem_graded ha' hb', ?_⟩
    ext n
    exact congrArg (fun p : R[X] ↦ p.coeff n) ((Polynomial.toFinsuppIso R).symm.map_mul a' b')

/-- Helper for Example 10.57.4: a homogeneous polynomial of degree `n` in the standard grading
is a scalar multiple of `X ^ n`. -/
theorem standardGrading_eq_C_mul_X_pow_of_mem {n : ℕ} {f : R[X]}
    (hf : f ∈ standardGrading R n) :
    f = Polynomial.C (f.coeff n) * Polynomial.X ^ n := by
  rcases hf with ⟨g, hg, rfl⟩
  -- Compare coefficients: outside degree `n` everything vanishes, and at degree `n` we keep
  -- exactly the `n`-th coefficient.
  ext i
  change ((Polynomial.toFinsuppIso R).symm g).coeff i =
    (Polynomial.C (((Polynomial.toFinsuppIso R).symm g).coeff n) * Polynomial.X ^ n).coeff i
  rw [Polynomial.toFinsuppIso_symm_apply, Polynomial.coeff_ofFinsupp,
    Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial]
  by_cases hi : i = n
  · subst hi
    simp
  · have hmem := (AddMonoidAlgebra.mem_grade_iff R n g).mp hg
    have hnot : i ∉ g.support := by
      intro hi_support
      exact hi (by simpa using hmem hi_support)
    have hgi : g i = 0 := Finsupp.notMem_support_iff.mp hnot
    have hni : ¬n = i := by simpa [eq_comm] using hi
    simp [hgi, hni]

/-- Helper for Example 10.57.4: the `n`-th graded piece of the standard grading is canonically a
copy of `R`, represented by the monomial `a X^n`. -/
private noncomputable def standardGradingCoeffEquiv (n : ℕ) :
    R ≃ₗ[R] standardGrading R n where
  toFun a := by
    refine ⟨Polynomial.C a * Polynomial.X ^ n, ?_⟩
    refine ⟨AddMonoidAlgebra.single n a, AddMonoidAlgebra.single_mem_grade n a, ?_⟩
    ext i
    change ((Polynomial.toFinsuppIso R).symm (AddMonoidAlgebra.single n a)).coeff i =
      (Polynomial.C a * Polynomial.X ^ n).coeff i
    rw [Polynomial.toFinsuppIso_symm_apply, Polynomial.coeff_ofFinsupp,
      Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial, AddMonoidAlgebra.single_apply]
  invFun f := f.1.coeff n
  left_inv a := by
    simp
  right_inv f := by
    apply Subtype.ext
    exact (Polynomial.standardGrading_eq_C_mul_X_pow_of_mem R f.2).symm
  map_add' a b := by
    apply Subtype.ext
    simp [add_mul]
  map_smul' c a := by
    apply Subtype.ext
    simp [Algebra.smul_def, mul_assoc]

/-- Helper for Example 10.57.4: the coefficient representation identifies `R[X]` with the direct
sum of its standard graded pieces. -/
private noncomputable def standardGradingComponentEquiv (n : ℕ) :
    AddMonoidAlgebra.grade R n ≃ₗ[R] standardGrading R n :=
  Submodule.equivMapOfInjective (Polynomial.toFinsuppIsoLinear R).symm.toLinearMap
    (Polynomial.toFinsuppIsoLinear R).symm.injective (AddMonoidAlgebra.grade R n)

/-- Helper for Example 10.57.4: the standard grading inherits the canonical decomposition of the
additive monoid algebra grading through `Polynomial.toFinsuppIsoLinear`. -/
private noncomputable abbrev standardGradingDecomposeLinearEquiv :
    R[X] ≃ₗ[R] ⨁ n, standardGrading R n :=
  (Polynomial.toFinsuppIsoLinear R).trans <|
    (DirectSum.decomposeLinearEquiv (AddMonoidAlgebra.grade R : ℕ → Submodule R _)).trans <|
      DirectSum.congrLinearEquiv fun n ↦ standardGradingComponentEquiv R n

/-- Helper for Example 10.57.4: the inverse of the transported decomposition is the canonical
recomposition map from the direct sum of graded pieces. -/
private theorem standardGradingDecomposeLinearEquiv_symm_eq_coe :
    (standardGradingDecomposeLinearEquiv R).symm.toLinearMap =
      DirectSum.coeLinearMap (standardGrading R) := by
  apply DirectSum.linearMap_ext
  intro n
  ext x i
  have hx :
      (standardGradingDecomposeLinearEquiv R).symm
          ((DirectSum.lof R ℕ (fun j ↦ ↥(standardGrading R j)) n) x) = x := by
    have hcongr :
        ((DirectSum.congrLinearEquiv fun j ↦ standardGradingComponentEquiv R j).symm
            ((DirectSum.lof R ℕ (fun j ↦ ↥(standardGrading R j)) n) x)) =
          DirectSum.lof R ℕ (fun j ↦ ↥(AddMonoidAlgebra.grade R j)) n
            ((standardGradingComponentEquiv R n).symm x) := by
      change DirectSum.lmap (fun j ↦ (standardGradingComponentEquiv R j).symm.toLinearMap)
          ((DirectSum.lof R ℕ (fun j ↦ ↥(standardGrading R j)) n) x) =
        DirectSum.lof R ℕ (fun j ↦ ↥(AddMonoidAlgebra.grade R j)) n
          ((standardGradingComponentEquiv R n).symm x)
      simpa using
        (DirectSum.lmap_lof (R := R)
          (f := fun j ↦ (standardGradingComponentEquiv R j).symm.toLinearMap) n x)
    change
      (Polynomial.toFinsuppIsoLinear R).symm
          (((DirectSum.decomposeLinearEquiv (AddMonoidAlgebra.grade R)).symm
              ((DirectSum.congrLinearEquiv fun j ↦ standardGradingComponentEquiv R j).symm
                ((DirectSum.lof R ℕ (fun j ↦ ↥(standardGrading R j)) n) x))) :
            AddMonoidAlgebra R ℕ) = x
    rw [hcongr]
    rw [DirectSum.decomposeLinearEquiv_symm_lof]
    exact Submodule.map_equivMapOfInjective_symm_apply
      (Polynomial.toFinsuppIsoLinear R).symm.toLinearMap
      (Polynomial.toFinsuppIsoLinear R).symm.injective (AddMonoidAlgebra.grade R n) x
  simpa using congrArg (fun p : Polynomial R ↦ p.coeff i) hx

theorem standardGrading_isInternal : DirectSum.IsInternal (standardGrading R) := by
  unfold DirectSum.IsInternal
  change Function.Bijective (DirectSum.coeLinearMap (standardGrading R))
  rw [← standardGradingDecomposeLinearEquiv_symm_eq_coe R]
  exact ⟨(standardGradingDecomposeLinearEquiv R).symm.injective,
    (standardGradingDecomposeLinearEquiv R).symm.surjective⟩

instance instGradedAlgebraStandardGrading : GradedAlgebra (standardGrading R) :=
  DirectSum.IsInternal.gradedAlgebra (standardGrading_isInternal R)

/-- Helper for Example 10.57.4: the chosen decomposition sends a polynomial to its monomial
homogeneous pieces. -/
theorem standardGrading_decompose_eq_C_coeff_mul_X_pow (f : R[X]) (n : ℕ) :
    ((DirectSum.decompose (standardGrading R) f) n : Polynomial R) =
      Polynomial.C (f.coeff n) * Polynomial.X ^ n := by
  classical
  have hsum :
      (∑ i ∈ DFinsupp.support (DirectSum.decompose (standardGrading R) f),
          (((DirectSum.decompose (standardGrading R) f) i : Polynomial R).coeff n)) = f.coeff n := by
    simpa [Polynomial.coeff_sum] using
      congrArg (fun p : Polynomial R ↦ p.coeff n)
        (DirectSum.sum_support_decompose (standardGrading R) f)
  have hcoeff :
      (((DirectSum.decompose (standardGrading R) f) n : Polynomial R).coeff n) = f.coeff n := by
    rw [Finset.sum_eq_single n ?_ ?_] at hsum
    · simpa using hsum
    · intro j hj hjn
      have hzero :
          (((DirectSum.decompose (standardGrading R) f) j : Polynomial R).coeff n) = 0 := by
        have hmono :=
          Polynomial.standardGrading_eq_C_mul_X_pow_of_mem R
            (DirectSum.decompose (standardGrading R) f j).2
        rw [hmono]
        rw [Polynomial.coeff_C_mul_X_pow]
        simpa [hjn.symm] using (if_neg (h := hjn.symm) :
          (if n = j then (↑((DirectSum.decompose (standardGrading R) f j)).coeff j) else 0) = 0)
      simp [hzero]
    · intro hn
      have hzero : DirectSum.decompose (standardGrading R) f n = 0 :=
        DFinsupp.notMem_support_iff.mp hn
      have hzero' : ((DirectSum.decompose (standardGrading R) f n : standardGrading R n) :
          Polynomial R) = 0 := by
        simpa using congrArg Subtype.val hzero
      simp [hzero']
  have hmono :=
    Polynomial.standardGrading_eq_C_mul_X_pow_of_mem R
      (DirectSum.decompose (standardGrading R) f n).2
  rw [hmono]
  simp [hcoeff]

/-- The degree-zero piece of the standard grading is canonically `R`, via constant polynomials. -/
private theorem eq_single_zero_of_mem_grade_zero {x : AddMonoidAlgebra R ℕ}
    (hx : x ∈ AddMonoidAlgebra.grade R 0) :
    x = AddMonoidAlgebra.single 0 (x 0) := by
  ext n
  by_cases hn : n = 0
  · subst hn
    simp
  · have hx' := (AddMonoidAlgebra.mem_grade_iff R 0 x).mp hx
    have hnot : n ∉ x.support := by
      intro hn'
      exact hn (by simpa using hx' hn')
    simp [hn, Finsupp.notMem_support_iff.mp hnot]

private noncomputable def addMonoidAlgebraGradeZeroRingEquiv :
    ↥(AddMonoidAlgebra.grade R 0) ≃+* R where
  toFun x := x.1 0
  invFun r := ⟨AddMonoidAlgebra.single 0 r, AddMonoidAlgebra.single_mem_grade 0 r⟩
  left_inv x := by
    apply Subtype.ext
    exact (eq_single_zero_of_mem_grade_zero R x.2).symm
  right_inv r := by
    simp
  map_mul' x y := by
    change (x.1 * y.1) 0 = x.1 0 * y.1 0
    rw [eq_single_zero_of_mem_grade_zero R x.2, eq_single_zero_of_mem_grade_zero R y.2]
    simp
  map_add' x y := by
    simp

private noncomputable def standardGradingDegreeZeroToAddMonoidAlgebra :
    ↥(standardGrading R 0) ≃+* ↥(AddMonoidAlgebra.grade R 0) where
  toFun p := by
    refine ⟨Polynomial.toFinsuppIso R p.1, ?_⟩
    rcases p.2 with ⟨q, hq, hq'⟩
    have h : q = Polynomial.toFinsuppIso R p.1 := by
      simpa using congrArg (Polynomial.toFinsuppIso R) hq'
    simpa [h] using hq
  invFun q := ⟨(Polynomial.toFinsuppIso R).symm q.1, ⟨q.1, q.2, rfl⟩⟩
  left_inv p := by
    apply Subtype.ext
    simp
  right_inv q := by
    apply Subtype.ext
    simp
  map_mul' p q := by
    rfl
  map_add' p q := by
    rfl

private noncomputable def standardGradingDegreeZeroRingEquiv : ↥(standardGrading R 0) ≃+* R :=
  (standardGradingDegreeZeroToAddMonoidAlgebra R).trans (addMonoidAlgebraGradeZeroRingEquiv R)

end Polynomial

section

variable (R : Type u) [CommRing R]

local notation "𝒮" => Polynomial.standardGrading R

private noncomputable def standardGradingDegreeZeroSpecIso :
    Spec (.of ↥(𝒮 0)) ≅ Spec (.of R) :=
  (Scheme.Spec.mapIso (Polynomial.standardGradingDegreeZeroRingEquiv R).toCommRingCatIso.op).symm

/-- Helper for Example 10.57.4: the polynomial `X` is homogeneous of degree `1` for the standard
grading. -/
private theorem standardGrading_X_mem : (Polynomial.X : Polynomial R) ∈ 𝒮 1 := by
  refine ⟨AddMonoidAlgebra.single 1 (1 : R), AddMonoidAlgebra.single_mem_grade 1 1, ?_⟩
  ext n
  change
    ((Polynomial.toFinsuppIso R).symm (AddMonoidAlgebra.single 1 (1 : R))).coeff n =
      Polynomial.X.coeff n
  rw [Polynomial.toFinsuppIso_symm_apply, Polynomial.coeff_ofFinsupp, AddMonoidAlgebra.single_apply]
  by_cases hn : n = 1
  · subst hn
    simp
  · simp [Polynomial.coeff_X]

/-- Helper for Example 10.57.4: every positive-degree homogeneous polynomial is divisible by `X`,
so the irrelevant ideal lies in `(X)`. -/
private theorem standardGrading_irrelevant_le_span_X :
    (HomogeneousIdeal.irrelevant 𝒮).toIdeal ≤
      Ideal.span ({(Polynomial.X : Polynomial R)} : Set (Polynomial R)) := by
  refine (HomogeneousIdeal.toIdeal_irrelevant_le (𝒜 := 𝒮)
    (I := Ideal.span ({(Polynomial.X : Polynomial R)} : Set (Polynomial R)))).2 ?_
  intro i hi f hf
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi) with ⟨n, rfl⟩
  -- Rewrite a positive-degree homogeneous polynomial as a multiple of `X`.
  have hX : (Polynomial.X : Polynomial R) ∈
      Ideal.span ({(Polynomial.X : Polynomial R)} : Set (Polynomial R)) :=
    Ideal.subset_span (by simp)
  have hmul :
      (Polynomial.C (f.coeff (Nat.succ n)) * Polynomial.X ^ n) * Polynomial.X ∈
        Ideal.span ({(Polynomial.X : Polynomial R)} : Set (Polynomial R)) :=
    Ideal.mul_mem_left (Ideal.span ({(Polynomial.X : Polynomial R)} : Set (Polynomial R)))
      (Polynomial.C (f.coeff (Nat.succ n)) * Polynomial.X ^ n) hX
  rw [Polynomial.standardGrading_eq_C_mul_X_pow_of_mem R hf, pow_succ]
  simpa [mul_assoc] using hmul

/-- Helper for Example 10.57.4: a relevant homogeneous prime of the standard grading cannot
contain `X`. -/
private theorem standardGrading_X_not_mem_asHomogeneousIdeal (p : ProjectiveSpectrum 𝒮) :
    (Polynomial.X : Polynomial R) ∉ p.asHomogeneousIdeal := by
  intro hX
  refine p.not_irrelevant_le ?_
  exact (standardGrading_irrelevant_le_span_X R).trans <| Ideal.span_le.mpr fun f hf ↦ by
    simpa [Set.mem_singleton_iff.mp hf] using hX

/-- Helper for Example 10.57.4: constant polynomials are exactly the degree-zero part of the
standard grading. -/
private theorem standardGrading_C_mem_zero (r : R) : Polynomial.C r ∈ 𝒮 0 := by
  simpa using SetLike.algebraMap_mem_graded (Polynomial.standardGrading R) r

/-- Helper for Example 10.57.4: the single chart `D₊(X)` already covers the whole projective
spectrum for the standard grading. -/
private theorem standard_grading_basicOpen_X_eq_top :
    Proj.basicOpen 𝒮 (Polynomial.X : Polynomial R) = ⊤ := by
  -- Check the defining condition of the basic open set pointwise.
  apply TopologicalSpace.Opens.ext
  ext p
  simp [standardGrading_X_not_mem_asHomogeneousIdeal]

/-- Helper for Example 10.57.4: a homogeneous fraction `a / X^n` in the unique chart is equal to
the constant fraction determined by the coefficient of `a` in degree `n`. -/
private theorem standard_grading_away_X_mk_eq_fromZeroRingHom
    (n : ℕ) (a : Polynomial R) (ha : a ∈ 𝒮 n) :
    HomogeneousLocalization.Away.mk 𝒮 (standardGrading_X_mem R) n a
        (by simpa [nsmul_eq_mul] using ha) =
      HomogeneousLocalization.fromZeroRingHom 𝒮 (Submonoid.powers (Polynomial.X : Polynomial R))
        ⟨Polynomial.C (a.coeff n), standardGrading_C_mem_zero R (a.coeff n)⟩ := by
  -- Compare both classes in the ordinary localization away from `X`.
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.Away.val_mk, Polynomial.standardGrading_eq_C_mul_X_pow_of_mem R ha,
    Localization.mk_eq_mk'_apply]
  -- After rewriting `a`, the numerator already has the form `C(a_n) * X^n`.
  have hrhs :
      ((HomogeneousLocalization.fromZeroRingHom 𝒮 (Submonoid.powers (Polynomial.X : Polynomial R)))
          ⟨Polynomial.C ((Polynomial.C (a.coeff n) * Polynomial.X ^ n).coeff n),
            standardGrading_C_mem_zero R ((Polynomial.C (a.coeff n) * Polynomial.X ^ n).coeff n)⟩).val =
        algebraMap (Polynomial R) (Localization.Away (Polynomial.X : Polynomial R))
          (Polynomial.C (a.coeff n)) := by
    simpa [HomogeneousLocalization.fromZeroRingHom, HomogeneousLocalization.val_mk,
      Localization.mk_eq_mk'_apply] using
      (IsLocalization.mk'_one (M := Submonoid.powers (Polynomial.X : Polynomial R))
        (S := Localization.Away (Polynomial.X : Polynomial R))
        (Polynomial.C (a.coeff n)))
  rw [hrhs]
  symm
  exact IsLocalization.eq_mk'_of_mul_eq (S := Localization.Away (Polynomial.X : Polynomial R))
    (z := Polynomial.C (a.coeff n)) (by simp)

/-- Helper for Example 10.57.4: every degree-zero class in `S[X]_X` comes from a constant
polynomial. -/
private theorem standard_grading_away_X_fromZeroRingHom_surjective :
    Function.Surjective
      (HomogeneousLocalization.fromZeroRingHom 𝒮
        (Submonoid.powers (Polynomial.X : Polynomial R))) := by
  intro z
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒮
    (standardGrading_X_mem R) z
  have ha' : a ∈ 𝒮 n := by
    simpa [nsmul_eq_mul] using ha
  -- Normalize the given fraction `a / X^n` to the constant fraction `C(a_n) / 1`.
  refine ⟨⟨Polynomial.C (a.coeff n), standardGrading_C_mem_zero R (a.coeff n)⟩, ?_⟩
  simpa using (standard_grading_away_X_mk_eq_fromZeroRingHom R n a ha').symm

/-- Helper for Example 10.57.4: multiplying a constant polynomial by `X^n` cannot annihilate it
unless the constant itself is zero. -/
private theorem X_pow_mul_C_eq_zero_iff (n : ℕ) (r : R) :
    Polynomial.X ^ n * Polynomial.C r = 0 ↔ r = 0 := by
  constructor
  · intro h
    have h' : Polynomial.C r * Polynomial.X ^ n = 0 := by
      rw [mul_comm] at h
      exact h
    have hcoeff := congrArg (fun p : Polynomial R ↦ p.coeff n) h'
    simpa [Polynomial.coeff_C_mul_X_pow] using hcoeff
  · intro hr
    simp [hr]

/-- Helper for Example 10.57.4: the chart map from the degree-zero piece into the localization
away from `X` is injective. -/
private theorem standard_grading_away_X_fromZeroRingHom_injective :
    Function.Injective
      (HomogeneousLocalization.fromZeroRingHom 𝒮
        (Submonoid.powers (Polynomial.X : Polynomial R))) := by
  intro a b hab
  apply Subtype.ext
  -- Rewrite equality of homogeneous fractions as equality in the ordinary localization.
  have hval := congrArg HomogeneousLocalization.val hab
  change
    Localization.mk a.1 (1 : Submonoid.powers (Polynomial.X : Polynomial R)) =
      Localization.mk b.1 (1 : Submonoid.powers (Polynomial.X : Polynomial R)) at hval
  have hmap :
      algebraMap (Polynomial R) (Localization.Away (Polynomial.X : Polynomial R)) a.1 =
        algebraMap (Polynomial R) (Localization.Away (Polynomial.X : Polynomial R)) b.1 := by
    rw [Localization.mk_one_eq_algebraMap, Localization.mk_one_eq_algebraMap] at hval
    exact hval
  have hzero :
      algebraMap (Polynomial R) (Localization.Away (Polynomial.X : Polynomial R)) (a.1 - b.1) =
        0 := by
    rw [map_sub, hmap, sub_self]
  obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff
    (M := Submonoid.powers (Polynomial.X : Polynomial R))
    (S := Localization.Away (Polynomial.X : Polynomial R)) (a.1 - b.1)).mp hzero
  rcases m with ⟨m, hm_mem⟩
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff m (Polynomial.X : Polynomial R)).mp hm_mem
  have hconst : a.1 - b.1 ∈ 𝒮 0 := (𝒮 0).sub_mem a.2 b.2
  have hconst_eq :
      a.1 - b.1 = Polynomial.C ((a.1 - b.1).coeff 0) := by
    simpa using Polynomial.standardGrading_eq_C_mul_X_pow_of_mem R hconst
  have hcoeff_zero : (a.1 - b.1).coeff 0 = 0 := by
    -- Clear the localization denominator by a power of `X`, then inspect coefficient `n`.
    have hmul_zero :
        Polynomial.X ^ n * Polynomial.C ((a.1 - b.1).coeff 0) = 0 := by
      rw [hconst_eq] at hm
      exact hm
    exact (X_pow_mul_C_eq_zero_iff R n ((a.1 - b.1).coeff 0)).mp hmul_zero
  have hsub : a.1 - b.1 = 0 := by
    calc
      a.1 - b.1 = Polynomial.C ((a.1 - b.1).coeff 0) := hconst_eq
      _ = 0 := by simp [hcoeff_zero]
  exact sub_eq_zero.mp hsub

/-- Helper for Example 10.57.4: the degree-zero ring of the localization away from `X` is exactly
the degree-zero graded piece. -/
private noncomputable def standard_grading_away_X_equiv_degree_zero :
    HomogeneousLocalization.Away 𝒮 (Polynomial.X : Polynomial R) ≃+* ↥(𝒮 0) :=
  (RingEquiv.ofBijective
    (HomogeneousLocalization.fromZeroRingHom 𝒮
      (Submonoid.powers (Polynomial.X : Polynomial R)))
    ⟨standard_grading_away_X_fromZeroRingHom_injective R,
      standard_grading_away_X_fromZeroRingHom_surjective R⟩).symm

/-- Example 10.57.4 (1), map form: if `S = R[X]` with `deg(X) = 1`, then the natural map
`Proj(S) → Spec(R)` is the degree-zero structure morphism followed by the canonical identification
`Spec(S₀) ≅ Spec(R)`. -/
@[stacks 00JQ]
noncomputable def polynomial_standardGrading_toSpec :
    Proj 𝒮 ⟶ Spec (.of R) :=
  Proj.toSpecZero 𝒮 ≫ (standardGradingDegreeZeroSpecIso R).hom

private instance : IsIso (Proj.toSpecZero 𝒮) := by
  let hm : 0 < (1 : ℕ) := zero_lt_one
  let e :
      ↥(𝒮 0) ≃+* HomogeneousLocalization.Away 𝒮 (Polynomial.X : Polynomial R) :=
    (standard_grading_away_X_equiv_degree_zero R).symm
  have haway_top :
      (Proj.awayι 𝒮 (Polynomial.X : Polynomial R) (standardGrading_X_mem R) hm).opensRange = ⊤ := by
    -- The single chart `D₊(X)` already covers the whole projective spectrum.
    rw [Proj.opensRange_awayι]
    exact standard_grading_basicOpen_X_eq_top R
  haveI :
      IsIso (Proj.awayι 𝒮 (Polynomial.X : Polynomial R) (standardGrading_X_mem R) hm) :=
    AlgebraicGeometry.isIso_of_isOpenImmersion_of_opensRange_eq_top _ haway_top
  haveI :
      IsIso
        (Spec.map (CommRingCat.ofHom
          (HomogeneousLocalization.fromZeroRingHom 𝒮
            (Submonoid.powers (Polynomial.X : Polynomial R))))) := by
    -- The chart ring is canonically identified with the degree-zero piece.
    simpa [e, standard_grading_away_X_equiv_degree_zero] using
      (inferInstance : IsIso (Scheme.Spec.mapIso e.toCommRingCatIso.op).hom)
  let g : Spec (.of ↥(𝒮 0)) ⟶ Proj 𝒮 :=
    (asIso (Spec.map (CommRingCat.ofHom
      (HomogeneousLocalization.fromZeroRingHom 𝒮
        (Submonoid.powers (Polynomial.X : Polynomial R)))))).inv ≫
      Proj.awayι 𝒮 (Polynomial.X : Polynomial R) (standardGrading_X_mem R) hm
  -- Route correction: use the single chart `D₊(X)=Proj`, then identify its coordinate ring with
  -- the degree-zero piece by the normalized-fraction equivalence above.
  refine isIso_of_hom_comp_eq_id g ?_
  simp [g, Proj.awayι_toSpecZero]

instance : IsIso (polynomial_standardGrading_toSpec R) := by
  change IsIso (Proj.toSpecZero 𝒮 ≫ (standardGradingDegreeZeroSpecIso R).hom)
  infer_instance

/-- Example 10.57.4 (1), canonical form: `Proj(R[X])` with `deg(X) = 1` is canonically isomorphic
to `Spec(R)`. -/
@[stacks 00JQ]
noncomputable def polynomial_standardGrading_isoSpec :
    Proj 𝒮 ≅ Spec (.of R) :=
  asIso (polynomial_standardGrading_toSpec R)

-- Example 10.57.4 (2): if `p` is a point of `Proj(R[X])` for the standard grading, equivalently a
-- relevant homogeneous prime ideal of `R[X]`, then `p` is the extension of its contraction to `R`.
-- Equivalently, for `p₀ = p ∩ R`, one has `p = p₀R[X]`.
-- Proof sketch: under `polynomial_standardGrading_isoSpec R`, the point `p` corresponds to its
-- contraction along `C : R →+* R[X]`, so its underlying ideal is the extension of that contracted
-- prime.
/-- Helper for Example 10.57.4: if a polynomial belongs to a projective point, then every
coefficient lies in the contracted prime of the base ring. -/
private theorem polynomial_standardGrading_coeff_mem_comap_of_mem_point
    (p : ProjectiveSpectrum 𝒮) {f : Polynomial R}
    (hf : f ∈ p.asHomogeneousIdeal.toIdeal) (n : ℕ) :
    f.coeff n ∈ Ideal.comap Polynomial.C p.asHomogeneousIdeal.toIdeal := by
  -- Homogeneity lets us test membership coefficientwise on the graded summands.
  have hcomp :
      ((DirectSum.decompose 𝒮 f) n : Polynomial R) ∈ p.asHomogeneousIdeal.toIdeal :=
    (Ideal.IsHomogeneous.mem_iff 𝒮 p.asHomogeneousIdeal.isHomogeneous).mp hf n
  rw [Polynomial.standardGrading_decompose_eq_C_coeff_mul_X_pow R f n] at hcomp
  have hprime : Ideal.IsPrime p.asHomogeneousIdeal.toIdeal := inferInstance
  have hXpow :
      (Polynomial.X : Polynomial R) ^ n ∉ p.asHomogeneousIdeal.toIdeal := by
    cases n with
    | zero =>
        have hne : p.asHomogeneousIdeal.toIdeal ≠ ⊤ := Ideal.IsPrime.ne_top (I := _) hprime
        simpa using (Ideal.ne_top_iff_one _).mp hne
    | succ k =>
        intro hpow
        have hX :
            (Polynomial.X : Polynomial R) ∈ p.asHomogeneousIdeal.toIdeal :=
          (Ideal.IsPrime.pow_mem_iff_mem (I := p.asHomogeneousIdeal.toIdeal)
            (r := (Polynomial.X : Polynomial R)) hprime (Nat.succ k) (Nat.succ_pos k)).mp hpow
        exact standardGrading_X_not_mem_asHomogeneousIdeal R p hX
  -- Primality removes the `X ^ n` factor, leaving only the constant coefficient.
  simpa [Ideal.mem_comap] using (hprime.mem_or_mem hcomp).resolve_right hXpow

theorem polynomial_standardGrading_point_asIdeal_eq_map_comap_C
    (p : ProjectiveSpectrum 𝒮) :
    p.asHomogeneousIdeal.toIdeal =
      Ideal.map Polynomial.C (Ideal.comap Polynomial.C p.asHomogeneousIdeal.toIdeal) := by
  apply le_antisymm
  · intro f hf
    -- Check membership in the extension ideal coefficientwise.
    rw [Ideal.mem_map_C_iff]
    intro n
    exact polynomial_standardGrading_coeff_mem_comap_of_mem_point R p hf n
  · -- Extension after contraction is always contained in the original ideal.
    exact Ideal.map_comap_le

end
