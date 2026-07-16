import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_46_7
import stacks_proof.stacks_project.Chap10.Lemma_10_161_11
import stacks_proof.stacks_project.Chap10.Lemma_10_161_12
universe u

open Ideal
open IntermediateField Polynomial

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

section

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]

omit [IsIntegrallyClosed R] in
/-- Helper for Lemma 10.161.16 (Tate): if the quotient by the zero ideal is `N-2`, then `R`
itself is `N-2`. -/
lemma isN2Ring_of_isN2Ring_quotient_bot [IsDomain (R ⧸ (⊥ : Ideal R))]
    [IsN2Ring (R ⧸ (⊥ : Ideal R))] :
    IsN2Ring R := by
  have h_injective : Function.Injective (algebraMap R (R ⧸ (⊥ : Ideal R))) := by
    intro a b hab
    -- Apply the canonical quotient-by-zero equivalence to recover equality in `R`.
    simpa using congrArg (RingEquiv.quotientBot R) hab
  letI : Module.Finite R (R ⧸ (⊥ : Ideal R)) := by
    -- The quotient is a surjective image of the finite free rank-one `R`-module `R`.
    exact Module.Finite.of_surjective
      (Ideal.Quotient.mkₐ R (⊥ : Ideal R)).toLinearMap
      (Ideal.Quotient.mkₐ_surjective R (⊥ : Ideal R))
  -- Descend `N-2` along the finite extension `R → R ⧸ (0)`.
  exact isN2Ring_of_finite_extension (R := R) (S := R ⧸ (⊥ : Ideal R)) h_injective

omit [IsDomain R] [IsNoetherianRing R] in
/-- Helper for Lemma 10.161.16 (Tate): a normal Noetherian domain is `N-1`. -/
lemma isN1Ring_of_isIntegrallyClosed_noetherian_domain :
    IsN1Ring R := by
  let e : integralClosure R (FractionRing R) ≃ₐ[R] R :=
    -- An integrally closed domain identifies with its normalization inside the fraction field.
    (Subalgebra.equivOfEq _ _
      (IsIntegrallyClosed.integralClosure_eq_bot (R := R) (K := FractionRing R))).trans
        (Algebra.botEquivOfInjective (R := R) (A := FractionRing R)
          (IsFractionRing.injective R (FractionRing R)))
  -- Identify the normalization with `R` itself and transport finite generation across that
  -- algebra equivalence.
  exact IsN1Ring.mk <| Module.Finite.equiv e.toLinearEquiv.symm

omit [IsNoetherianRing R] [IsIntegrallyClosed R] in
/-- Helper for Lemma 10.161.16 (Tate): a finite purely inseparable extension of the fraction field
has a uniform `p^e`-power sending every element back into the base fraction field. -/
lemma exists_common_qpow_in_fractionRing_of_finite_purelyInseparable
    (p : ℕ) [Fact p.Prime] [CharP (FractionRing R) p]
    (L : Type u) [Field L] [Algebra R L] [Algebra (FractionRing R) L]
    [IsScalarTower R (FractionRing R) L] [FiniteDimensional (FractionRing R) L]
    [IsPurelyInseparable (FractionRing R) L] :
    ∃ e : ℕ, ∀ z : L, z ^ (p ^ e) ∈ Set.range (algebraMap (FractionRing R) L) := by
  refine ⟨IsPurelyInseparable.exponent (FractionRing R) L, ?_⟩
  intro z
  -- The canonical purely inseparable exponent works simultaneously for every element.
  simpa [IsPurelyInseparable.exponent] using
    (IsPurelyInseparable.exponent_def' (K := FractionRing R) (L := L) p z)

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.161.16 (Tate): a common `p^e`-power condition on an overfield makes the
normalization map satisfy the Chapter `10.46.7` generator predicate. -/
lemma algebraMap_isGeneratedByPrimePowerAndScalarImage_of_common_qpow
    (p : ℕ) [Fact p.Prime] [CharP (FractionRing R) p]
    {M : Type u} [Field M] [Algebra R M] [Algebra (FractionRing R) M]
    [IsScalarTower R (FractionRing R) M]
    (e : ℕ)
    (hpow : ∀ z : M, z ^ (p ^ e) ∈ Set.range (algebraMap (FractionRing R) M)) :
    (algebraMap R (integralClosure R M)).IsGeneratedByPrimePowerAndScalarImage p := by
  -- Route correction: package the source's common-`p^e` power input into the exact Chapter
  -- `10.46.7` algebra-generator predicate before tackling the unique-prime-over-`(x)` step.
  let _ : Algebra R (integralClosure R M) := (algebraMap R (integralClosure R M)).toAlgebra
  letI : CharP M p :=
    charP_of_injective_algebraMap (algebraMap (FractionRing R) M).injective p
  let G : Set (integralClosure R M) :=
    {z : integralClosure R M |
      ∃ n : ℕ, 0 < n ∧
        z ^ (p ^ n) ∈ Set.range (algebraMap R (integralClosure R M)) ∧
        p ^ n • z ∈ Set.range (algebraMap R (integralClosure R M))}
  have hmem : ∀ z : integralClosure R M, z ∈ G := by
    intro z
    refine ⟨e + 1, Nat.succ_pos _, ?_, ?_⟩
    · rcases hpow (z : M) with ⟨a, ha⟩
      have ha_integral : IsIntegral R (a ^ p) := by
        have h_eq_image :
            algebraMap (FractionRing R) M (a ^ p) = (z : M) ^ (p ^ (e + 1)) := by
          -- Rewrite the `K`-element as a power of the integral element `z`.
          calc
            algebraMap (FractionRing R) M (a ^ p) = (algebraMap (FractionRing R) M a) ^ p := by
              simp
            _ = ((z : M) ^ (p ^ e)) ^ p := by simpa [ha]
            _ = (z : M) ^ (p ^ e * p) := by rw [pow_mul]
            _ = (z : M) ^ (p ^ (e + 1)) := by rw [Nat.pow_succ', Nat.mul_comm]
        have h_image_integral : IsIntegral R (algebraMap (FractionRing R) M (a ^ p)) := by
          rw [h_eq_image]
          exact z.2.pow _
        exact (isIntegral_algebraMap_iff (algebraMap (FractionRing R) M).injective).mp
          h_image_integral
      obtain ⟨r, hr⟩ :=
        IsIntegrallyClosed.algebraMap_eq_of_integral (K := FractionRing R) ha_integral
      refine ⟨r, ?_⟩
      apply Subtype.ext
      -- Transport the integrally closed fraction-field equality back into the normalization.
      change algebraMap R M r = (z : M) ^ (p ^ (e + 1))
      calc
        algebraMap R M r = algebraMap (FractionRing R) M (a ^ p) := by
          rw [← hr, IsScalarTower.algebraMap_apply R (FractionRing R) M]
        _ = (algebraMap (FractionRing R) M a) ^ p := by simp
        _ = ((z : M) ^ (p ^ e)) ^ p := by simpa [ha]
        _ = (z : M) ^ (p ^ e * p) := by rw [pow_mul]
        _ = (z : M) ^ (p ^ (e + 1)) := by rw [Nat.pow_succ', Nat.mul_comm]
    · refine ⟨0, ?_⟩
      apply Subtype.ext
      -- The scalar part is trivial because every `p`-power scalar vanishes in characteristic `p`.
      change algebraMap R M 0 = p ^ (e + 1) • (z : M)
      have hpzero : ((p ^ (e + 1) : ℕ) : M) = 0 := by simp
      rw [nsmul_eq_mul, hpzero, zero_mul]
      simp
  have htop : Algebra.adjoin R G = ⊤ := by
    apply top_unique
    intro z hz
    -- The generating set already contains every element of the normalization.
    exact Algebra.subset_adjoin (hmem z)
  simpa [RingHom.IsGeneratedByPrimePowerAndScalarImage, G] using htop

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.161.16 (Tate): in an algebraic closure of `L`, one can choose a
`p ^ e`-th root of the image of `x`. -/
lemma exists_root_in_algebraicClosure_of_prime_power
    (x : R) (p : ℕ) [Fact p.Prime]
    (L : Type u) [Field L] [Algebra R L]
    (e : ℕ) :
    ∃ y : AlgebraicClosure L, y ^ (p ^ e) = algebraMap R (AlgebraicClosure L) x := by
  let q := p ^ e
  have hq_pos : 0 < q := by
    dsimp [q]
    exact pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) _
  obtain ⟨y, hy⟩ :=
    IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure L)
      ((X : L[X]) ^ q - C (algebraMap R L x))
      (by
        rw [degree_X_pow_sub_C hq_pos (algebraMap R L x)]
        exact_mod_cast hq_pos.ne')
  refine ⟨y, ?_⟩
  -- Evaluating the defining polynomial records the chosen `p ^ e`-th root of `x`.
  simpa [q, IsScalarTower.algebraMap_apply R L (AlgebraicClosure L) x, sub_eq_zero] using hy

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.161.16 (Tate): each basis image in an overfield remains integral over the
fraction field. -/
lemma basis_image_isIntegral_over_fractionRing
    {L : Type*} {Ω : Type*} {ι : Type*}
    [Field L] [Field Ω] [Fintype ι]
    [Algebra (FractionRing R) L] [Algebra (FractionRing R) Ω]
    [FiniteDimensional (FractionRing R) L]
    (b : Module.Basis ι (FractionRing R) L) (iota : L →ₐ[FractionRing R] Ω) (j : ι) :
    IsIntegral (FractionRing R) (iota (b j)) := by
  -- Finite-dimensionality makes each basis vector algebraic, and algebraicity maps across `iota`.
  have h_integral : IsIntegral (FractionRing R) (b j) := by
    exact (Algebra.IsAlgebraic.isAlgebraic (b j)).isIntegral
  exact h_integral.map iota

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.161.16 (Tate): adjoining the images of a finite basis gives a finite
intermediate field over the fraction field. -/
lemma finite_basis_image_stage
    {L : Type*} {Ω : Type*} {ι : Type*}
    [Field L] [Field Ω] [Fintype ι]
    [Algebra (FractionRing R) L] [Algebra (FractionRing R) Ω]
    [FiniteDimensional (FractionRing R) L]
    (b : Module.Basis ι (FractionRing R) L) (iota : L →ₐ[FractionRing R] Ω) :
    FiniteDimensional (FractionRing R)
      (IntermediateField.adjoin (FractionRing R) (Set.range fun j : ι => iota (b j))) := by
  -- The finite basis image is integral term-by-term, so the adjoin is finite-dimensional.
  refine IntermediateField.finiteDimensional_adjoin ?_
  rintro z ⟨j, rfl⟩
  exact basis_image_isIntegral_over_fractionRing (R := R) b iota j

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.161.16 (Tate): the basis-image adjoin already contains the full image of
`L` in the ambient overfield. -/
lemma lift_mem_basis_image_stage
    {L : Type*} {Ω : Type*} {ι : Type*}
    [Field L] [Field Ω] [Fintype ι]
    [Algebra (FractionRing R) L] [Algebra (FractionRing R) Ω]
    (b : Module.Basis ι (FractionRing R) L) (iota : L →ₐ[FractionRing R] Ω) (x : L) :
    iota x ∈ IntermediateField.adjoin (FractionRing R) (Set.range fun j : ι => iota (b j)) := by
  let T : IntermediateField (FractionRing R) Ω :=
    IntermediateField.adjoin (FractionRing R) (Set.range fun j : ι => iota (b j))
  -- Expand `x` in the chosen basis and map the expansion into the ambient overfield.
  have hx :
      iota x = ∑ j, algebraMap (FractionRing R) Ω (b.repr x j) * iota (b j) := by
    calc
      iota x = iota (∑ j, b.repr x j • b j) := by rw [b.sum_repr]
      _ = ∑ j, algebraMap (FractionRing R) Ω (b.repr x j) * iota (b j) := by
        simp [map_sum, Algebra.smul_def]
  rw [hx]
  refine T.sum_mem ?_
  intro j _
  have hcoeff : algebraMap (FractionRing R) Ω (b.repr x j) ∈ T := by
    exact IntermediateField.algebraMap_mem _ _
  have hbasis : iota (b j) ∈ T := by
    exact IntermediateField.subset_adjoin (F := FractionRing R)
      (S := Set.range fun k : ι => iota (b k)) ⟨j, rfl⟩
  -- Each summand is the product of a scalar coefficient with a basis generator already in `T`.
  simpa [Algebra.smul_def] using T.mul_mem hcoeff hbasis

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.161.16 (Tate): an intermediate field whose elements have `p ^ e`-th powers
in the base-field image inherits the same condition on its own carrier. -/
lemma common_qpow_codrestrict_range
    {K : Type*} {Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (p e : ℕ)
    (M : IntermediateField K Ω)
    (hM : ∀ z : M, (z : Ω) ^ (p ^ e) ∈ (algebraMap K Ω).fieldRange) :
    ∀ z : M, z ^ (p ^ e) ∈ Set.range (algebraMap K M) := by
  intro z
  rcases RingHom.mem_fieldRange.mp (hM z) with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  -- Reuse the same base-field witness after viewing the equality on the carrier `M`.
  apply Subtype.ext
  simpa using ha

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.161.16 (Tate): after fixing the common exponent on `L`, adjoin a matching
`p ^ e`-th root of `x` in an algebraic closure and keep the same exponent on the resulting finite
overfield. -/
lemma exists_root_overfield_of_given_common_qpow
    (x : R) (p : ℕ) [Fact p.Prime] [CharP (FractionRing R) p]
    (L : Type u) [Field L] [Algebra R L] [Algebra (FractionRing R) L]
    [IsScalarTower R (FractionRing R) L] [FiniteDimensional (FractionRing R) L]
    (e : ℕ)
    (hpowL : ∀ z : L, z ^ (p ^ e) ∈ Set.range (algebraMap (FractionRing R) L)) :
    ∃ (M : Type u) (_ : Field M) (_ : Algebra R M) (_ : Algebra (FractionRing R) M)
      (_ : IsScalarTower R (FractionRing R) M) (_ : FiniteDimensional (FractionRing R) M)
      (iota : L →ₐ[FractionRing R] M),
      ∃ y : M,
        y ^ (p ^ e) = algebraMap R M x ∧
          (∀ z : M, z ^ (p ^ e) ∈ Set.range (algebraMap (FractionRing R) M)) := by
  let K := FractionRing R
  let Ω := AlgebraicClosure L
  letI : Algebra R Ω := inferInstance
  letI : Algebra K Ω := inferInstance
  letI : IsScalarTower R K Ω := inferInstance
  letI : CharP Ω p :=
    charP_of_injective_algebraMap (algebraMap K Ω).injective p
  let iotaΩ : L →ₐ[K] Ω := IsScalarTower.toAlgHom K L Ω
  obtain ⟨y0, hy0_root⟩ :=
    exists_root_in_algebraicClosure_of_prime_power (R := R) x p L e
  let Tsub : Subfield Ω :=
    (algebraMap K Ω).fieldRange.comap (iterateFrobenius Ω p e)
  let T : IntermediateField K Ω := Tsub.toIntermediateField fun z ↦ by
    -- Base-field elements stay inside the `q`-power-controlled ambient field.
    refine RingHom.mem_fieldRange.mpr ⟨z ^ (p ^ e), ?_⟩
    simp [iterateFrobenius_def]
  have hiotaΩ_mem_T : ∀ z : L, iotaΩ z ∈ T := by
    intro z
    change iterateFrobenius Ω p e (iotaΩ z) ∈ (algebraMap K Ω).fieldRange
    rcases hpowL z with ⟨a, ha⟩
    refine RingHom.mem_fieldRange.mpr ⟨a, ?_⟩
    -- The common `p^e`-power witness from `L` survives after mapping into `Ω`.
    simpa [iotaΩ, iterateFrobenius_def] using congrArg (algebraMap L Ω) ha
  have hy0_mem_T : y0 ∈ T := by
    change iterateFrobenius Ω p e y0 ∈ (algebraMap K Ω).fieldRange
    refine RingHom.mem_fieldRange.mpr ⟨algebraMap R K x, ?_⟩
    -- The chosen root has `p^e`-th power equal to the scalar image of `x`.
    calc
      algebraMap K Ω (algebraMap R K x) = algebraMap R Ω x := by
        rw [IsScalarTower.algebraMap_apply R K Ω x]
      _ = y0 ^ (p ^ e) := hy0_root.symm
  let b := Module.finBasis K L
  let E : IntermediateField K Ω :=
    IntermediateField.adjoin K (Set.range fun j => iotaΩ (b j))
  letI : FiniteDimensional K E :=
    finite_basis_image_stage (R := R) b iotaΩ
  have hiotaΩ_mem_E : ∀ z : L, iotaΩ z ∈ E := by
    intro z
    exact lift_mem_basis_image_stage (R := R) b iotaΩ z
  have hE_le_T : E ≤ T := by
    -- The finite stage lies in `T` because it is generated by elements already controlled by `hpowL`.
    refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro _ ⟨j, rfl⟩
    exact hiotaΩ_mem_T (b j)
  let M0 : IntermediateField K Ω := E ⊔ K⟮y0⟯
  have hy0_integral : IsIntegral K y0 := by
    have hx_integral : IsIntegral K (algebraMap R Ω x) := by
      simpa [IsScalarTower.algebraMap_apply R K Ω x] using
        (isIntegral_algebraMap (R := K) (A := Ω) (x := algebraMap R K x))
    -- A positive `p^e`-th power of `y0` lies in the base field, hence `y0` is integral.
    exact IsIntegral.of_pow (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) _)
      (hy0_root.symm ▸ hx_integral)
  letI : FiniteDimensional K K⟮y0⟯ :=
    IntermediateField.adjoin.finiteDimensional hy0_integral
  letI : FiniteDimensional K M0 := IntermediateField.finiteDimensional_sup E K⟮y0⟯
  have hM0_le_T : M0 ≤ T := by
    -- Both the finite image stage and the root field sit inside the common `q`-power field.
    refine sup_le hE_le_T ?_
    refine IntermediateField.adjoin_le_iff.mpr ?_
    simpa using hy0_mem_T
  have hiotaΩ_mem_M0 : ∀ z : L, iotaΩ z ∈ M0 := by
    intro z
    -- The full image stage `E` is the left summand of `M0 = E ⊔ K⟮y0⟯`.
    exact (show E ≤ M0 from le_sup_left) (hiotaΩ_mem_E z)
  let iotaM : L →ₐ[K] M0 := iotaΩ.codRestrict M0.toSubalgebra hiotaΩ_mem_M0
  let y : M0 :=
    ⟨y0, (show K⟮y0⟯ ≤ M0 from le_sup_right) (IntermediateField.mem_adjoin_simple_self K y0)⟩
  have hpowM0 : ∀ z : M0, z ^ (p ^ e) ∈ Set.range (algebraMap K M0) := by
    -- Route correction: use `M0` itself as the witness carrier and transport the common
    -- `p ^ e`-power witness directly from `M0 ≤ T`.
    refine common_qpow_codrestrict_range (p := p) (e := e) M0 ?_
    intro z
    change (z : Ω) ^ (p ^ e) ∈ (algebraMap K Ω).fieldRange
    exact hM0_le_T z.2
  refine
    ⟨M0, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, iotaM, y,
      ?_, hpowM0⟩
  -- The chosen root already satisfies the source equation inside `Ω`; now restate it on `M0`.
  apply Subtype.ext
  simpa [y] using hy0_root

end
