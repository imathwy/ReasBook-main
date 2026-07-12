import StacksProject_2024.Chap10.Example_10_55_5.ProjectiveClutching.VectorPresentation

noncomputable section

universe u v w

section

variable (k : Type u) [Field k]

local notation "R" => equal_endpoint_poly_subring k

/-- Helper for Chap10 Example 10 55 5: every conductor multiple belongs to any invertible
submodule unit of the polynomial normalization. -/
theorem equalEndpointConductorMul_mem_invertibleSubmoduleUnit
    (I : (Submodule R (equalEndpointPolynomialMulModule k))ˣ) (q : Polynomial k) :
    (((Polynomial.X ^ 2 - Polynomial.X : Polynomial k) * q : Polynomial k) :
      equalEndpointPolynomialMulModule k) ∈
      (I : Submodule R (equalEndpointPolynomialMulModule k)) := by
  classical
  let A := equalEndpointPolynomialMulModule k
  let E : A :=
    (((Polynomial.X ^ 2 - Polynomial.X : Polynomial k) * q : Polynomial k) : A)
  -- Use the finite product expression of `1 ∈ I * I⁻¹` and test it against the conductor
  -- multiplier.
  have hone : (1 : A) ∈ (I : Submodule R A) * ((I⁻¹ : (Submodule R A)ˣ) : Submodule R A) := by
    rw [I.mul_inv]
    exact (Submodule.mem_one).mpr ⟨1, by simp⟩
  rcases Submodule.mem_span_mul_finite_of_mem_mul hone with
    ⟨T, T', hT, hT', hone_span⟩
  let P : Submodule R A :=
    { carrier := {z : A | E * z ∈ (I : Submodule R A)}
      zero_mem' := by
        simp
      add_mem' := by
        intro z w hz hw
        change E * (z + w) ∈ (I : Submodule R A)
        rw [mul_add]
        exact (I : Submodule R A).add_mem hz hw
      smul_mem' := by
        intro r z hz
        change E * (r • z) ∈ (I : Submodule R A)
        have hsmul : E * (r • z) = r • (E * z) := by
          apply equalEndpointPolynomialMulModule_toPolynomial_injective (k := k)
          simp [A, E, equalEndpointPolynomialMulModule.toPolynomial, mul_comm]
        rw [hsmul]
        exact (I : Submodule R A).smul_mem r hz }
  have hspan_le :
      Submodule.span R (Set.image2 (fun x y : A => x * y) (T : Set A) (T' : Set A)) ≤ P := by
    apply Submodule.span_le.mpr
    intro z hz
    rcases hz with ⟨x, hx, y, hy, hxy⟩
    subst hxy
    -- For a product generator `x * y`, the factor `E * y` is in the equal-endpoint ring, so
    -- `E * (x * y)` is an `R`-multiple of the `I`-element `x`.
    have hxI : x ∈ (I : Submodule R A) := hT hx
    have hEy_mem : equalEndpointPolynomialMulModule.toPolynomial k (E * y) ∈ R := by
      let Ey : equalEndpointPolynomialMulModule k :=
        (((Polynomial.X ^ 2 - Polynomial.X : Polynomial k) *
          (q * equalEndpointPolynomialMulModule.toPolynomial k y) : Polynomial k) :
          equalEndpointPolynomialMulModule k)
      have hline : Ey ∈ equalEndpointLineSubmodule k 1 := by
        simpa [Ey] using
          equalEndpointLineSubmodule_conductor_mul_mem (k := k) (1 : kˣ)
            (q * equalEndpointPolynomialMulModule.toPolynomial k y)
      have hR : equalEndpointPolynomialMulModule.toPolynomial k Ey ∈ R :=
        (mem_equalEndpointLineSubmodule_one_iff (k := k) Ey).mp hline
      change ((Polynomial.X ^ 2 - Polynomial.X : Polynomial k) * q *
          equalEndpointPolynomialMulModule.toPolynomial k y) ∈ R
      rw [mul_assoc]
      exact hR
    let r : R := ⟨equalEndpointPolynomialMulModule.toPolynomial k (E * y), hEy_mem⟩
    have hrx : r • x ∈ (I : Submodule R A) :=
      (I : Submodule R A).smul_mem r hxI
    have hmul : E * (x * y) = r • x := by
      apply equalEndpointPolynomialMulModule_toPolynomial_injective (k := k)
      rw [equalEndpointPolynomialMulModule_smul_eq_mul]
      simp [A, E, r, equalEndpointPolynomialMulModule.toPolynomial,
        mul_assoc, mul_comm]
      rfl
    change E * (x * y) ∈ (I : Submodule R A)
    rw [hmul]
    exact hrx
  have hE_one : E * 1 ∈ (I : Submodule R A) := hspan_le hone_span
  -- Since `E * 1 = E`, the conductor multiple itself lies in `I`.
  simpa [A, E] using hE_one

/-- Helper for Chap10 Example 10 55 5: every constant polynomial belongs to the
equal-endpoint subring. -/
theorem equalEndpointConstant_mem_subring (a : k) :
    Polynomial.C a ∈ R := by
  -- Constants have the same value at both endpoints.
  rw [mem_equal_endpoint_poly_subring_iff]
  simp

/-- Helper for Chap10 Example 10 55 5: an invertible submodule unit has a product
with its inverse whose endpoint value at `0` is nonzero. -/
theorem equalEndpointInvertibleSubmoduleUnit_exists_mul_eval_zero_ne_zero
    (I : (Submodule R (equalEndpointPolynomialMulModule k))ˣ) :
    ∃ x : equalEndpointPolynomialMulModule k,
      x ∈ (I : Submodule R (equalEndpointPolynomialMulModule k)) ∧
      ∃ y : equalEndpointPolynomialMulModule k,
        y ∈ ((I⁻¹ : (Submodule R (equalEndpointPolynomialMulModule k))ˣ) :
          Submodule R (equalEndpointPolynomialMulModule k)) ∧
        Polynomial.eval 0
          (equalEndpointPolynomialMulModule.toPolynomial k (x * y)) ≠ 0 := by
  classical
  let A := equalEndpointPolynomialMulModule k
  by_contra hnone
  have hall :
      ∀ x : A, x ∈ (I : Submodule R A) →
        ∀ y : A, y ∈ ((I⁻¹ : (Submodule R A)ˣ) : Submodule R A) →
          Polynomial.eval 0 (equalEndpointPolynomialMulModule.toPolynomial k (x * y)) = 0 := by
    intro x hx y hy
    by_contra hxy
    exact hnone ⟨x, hx, y, hy, hxy⟩
  have hone_one : (1 : A) ∈ (1 : Submodule R A) := by
    -- The unit submodule contains the algebraic unit of the normalization owner.
    refine (Submodule.mem_one).mpr ?_
    refine ⟨1, ?_⟩
    simp
  have hone :
      (1 : A) ∈
        (I : Submodule R A) *
          (((I⁻¹ : (Submodule R A)ˣ) : Submodule R A)) := by
    simpa [I.mul_inv] using hone_one
  have hzero :
      Polynomial.eval 0 (equalEndpointPolynomialMulModule.toPolynomial k (1 : A)) = 0 := by
    -- If every product generator vanished at the endpoint, additivity over the product
    -- submodule would force the unit product to vanish there as well.
    exact Submodule.mul_induction_on hone
      (fun x hx y hy => hall x hx y hy)
      (fun z w hz hw => by
        have htoadd :
            equalEndpointPolynomialMulModule.toPolynomial k (z + w) =
              equalEndpointPolynomialMulModule.toPolynomial k z +
                equalEndpointPolynomialMulModule.toPolynomial k w := rfl
        rw [htoadd, Polynomial.eval_add, hz, hw, zero_add])
  have htoone :
      equalEndpointPolynomialMulModule.toPolynomial k (1 : A) = (1 : Polynomial k) := rfl
  have h10 : (1 : k) = 0 := by
    rw [htoone] at hzero
    simpa using hzero
  exact one_ne_zero h10

/-- Helper for Chap10 Example 10 55 5: a nonzero inverse-side product extracts the
endpoint ratio of every element of an invertible submodule unit. -/
theorem equalEndpointInvertibleSubmoduleUnit_endpointRatio_exists
    (I : (Submodule R (equalEndpointPolynomialMulModule k))ˣ) :
    ∃ unitRatio : kˣ,
      (I : Submodule R (equalEndpointPolynomialMulModule k)) ≤
        equalEndpointLineSubmodule k unitRatio ∧
      ∃ x : equalEndpointPolynomialMulModule k,
        x ∈ (I : Submodule R (equalEndpointPolynomialMulModule k)) ∧
        Polynomial.eval 0 (equalEndpointPolynomialMulModule.toPolynomial k x) ≠ 0 := by
  let A := equalEndpointPolynomialMulModule k
  rcases equalEndpointInvertibleSubmoduleUnit_exists_mul_eval_zero_ne_zero (k := k) I with
    ⟨x, hx, y, hy, hxy0_ne⟩
  have htomul_xy :
      equalEndpointPolynomialMulModule.toPolynomial k (x * y) =
        equalEndpointPolynomialMulModule.toPolynomial k x *
          equalEndpointPolynomialMulModule.toPolynomial k y := rfl
  have hxy0_prod :
      Polynomial.eval 0 (equalEndpointPolynomialMulModule.toPolynomial k x) *
        Polynomial.eval 0 (equalEndpointPolynomialMulModule.toPolynomial k y) ≠ 0 := by
    rw [htomul_xy, Polynomial.eval_mul] at hxy0_ne
    exact hxy0_ne
  have hx0_ne : Polynomial.eval 0 (equalEndpointPolynomialMulModule.toPolynomial k x) ≠ 0 :=
    left_ne_zero_of_mul hxy0_prod
  have hy0_ne : Polynomial.eval 0 (equalEndpointPolynomialMulModule.toPolynomial k y) ≠ 0 :=
    right_ne_zero_of_mul hxy0_prod
  have hxy_one : x * y ∈ (1 : Submodule R A) := by
    have hxy_prod :
        x * y ∈
          (I : Submodule R A) *
            (((I⁻¹ : (Submodule R A)ˣ) : Submodule R A)) :=
      Submodule.mul_mem_mul hx hy
    simpa [I.mul_inv] using hxy_prod
  have hxy_line : x * y ∈ equalEndpointLineSubmodule k 1 := by
    rw [equalEndpointLineSubmodule_one_eq_one]
    exact hxy_one
  have hxy_cond :=
    (mem_equalEndpointLineSubmodule (k := k) (1 : kˣ) (x * y)).mp hxy_line
  have hxy_eval_eq :
      Polynomial.eval 1 (equalEndpointPolynomialMulModule.toPolynomial k (x * y)) =
        Polynomial.eval 0 (equalEndpointPolynomialMulModule.toPolynomial k (x * y)) := by
    simpa [equalEndpointLineCondition] using hxy_cond
  have hxy1_ne :
      Polynomial.eval 1 (equalEndpointPolynomialMulModule.toPolynomial k (x * y)) ≠ 0 := by
    rw [hxy_eval_eq]
    exact hxy0_ne
  have hxy1_prod :
      Polynomial.eval 1 (equalEndpointPolynomialMulModule.toPolynomial k x) *
        Polynomial.eval 1 (equalEndpointPolynomialMulModule.toPolynomial k y) ≠ 0 := by
    rw [htomul_xy, Polynomial.eval_mul] at hxy1_ne
    exact hxy1_ne
  have hy1_ne : Polynomial.eval 1 (equalEndpointPolynomialMulModule.toPolynomial k y) ≠ 0 :=
    right_ne_zero_of_mul hxy1_prod
  have hu_ne :
      Polynomial.eval 0 (equalEndpointPolynomialMulModule.toPolynomial k y) *
        (Polynomial.eval 1 (equalEndpointPolynomialMulModule.toPolynomial k y))⁻¹ ≠ 0 := by
    exact mul_ne_zero hy0_ne (inv_ne_zero hy1_ne)
  let unitRatio : kˣ :=
    Units.mk0
      (Polynomial.eval 0 (equalEndpointPolynomialMulModule.toPolynomial k y) *
        (Polynomial.eval 1 (equalEndpointPolynomialMulModule.toPolynomial k y))⁻¹)
      hu_ne
  refine ⟨unitRatio, ?_, x, hx, hx0_ne⟩
  intro z hz
  have hzy_one : z * y ∈ (1 : Submodule R A) := by
    have hzy_prod :
        z * y ∈
          (I : Submodule R A) *
            (((I⁻¹ : (Submodule R A)ˣ) : Submodule R A)) :=
      Submodule.mul_mem_mul hz hy
    simpa [I.mul_inv] using hzy_prod
  have hzy_line : z * y ∈ equalEndpointLineSubmodule k 1 := by
    rw [equalEndpointLineSubmodule_one_eq_one]
    exact hzy_one
  have hzy_cond :=
    (mem_equalEndpointLineSubmodule (k := k) (1 : kˣ) (z * y)).mp hzy_line
  have hzy_eval_eq :
      Polynomial.eval 1 (equalEndpointPolynomialMulModule.toPolynomial k (z * y)) =
        Polynomial.eval 0 (equalEndpointPolynomialMulModule.toPolynomial k (z * y)) := by
    simpa [equalEndpointLineCondition] using hzy_cond
  have htomul_zy :
      equalEndpointPolynomialMulModule.toPolynomial k (z * y) =
        equalEndpointPolynomialMulModule.toPolynomial k z *
          equalEndpointPolynomialMulModule.toPolynomial k y := rfl
  have hzy_mul_eq :
      Polynomial.eval 1 (equalEndpointPolynomialMulModule.toPolynomial k z) *
        Polynomial.eval 1 (equalEndpointPolynomialMulModule.toPolynomial k y) =
      Polynomial.eval 0 (equalEndpointPolynomialMulModule.toPolynomial k z) *
        Polynomial.eval 0 (equalEndpointPolynomialMulModule.toPolynomial k y) := by
    rw [htomul_zy, Polynomial.eval_mul] at hzy_eval_eq
    rw [Polynomial.eval_mul] at hzy_eval_eq
    exact hzy_eval_eq
  rw [mem_equalEndpointLineSubmodule]
  unfold equalEndpointLineCondition
  calc
    Polynomial.eval 1 (equalEndpointPolynomialMulModule.toPolynomial k z) =
        (Polynomial.eval 1 (equalEndpointPolynomialMulModule.toPolynomial k z) *
          Polynomial.eval 1 (equalEndpointPolynomialMulModule.toPolynomial k y)) *
          (Polynomial.eval 1 (equalEndpointPolynomialMulModule.toPolynomial k y))⁻¹ := by
      rw [mul_assoc, mul_inv_cancel₀ hy1_ne, mul_one]
    _ = (Polynomial.eval 0 (equalEndpointPolynomialMulModule.toPolynomial k z) *
          Polynomial.eval 0 (equalEndpointPolynomialMulModule.toPolynomial k y)) *
          (Polynomial.eval 1 (equalEndpointPolynomialMulModule.toPolynomial k y))⁻¹ := by
      rw [hzy_mul_eq]
    _ = (unitRatio : k) *
          Polynomial.eval 0 (equalEndpointPolynomialMulModule.toPolynomial k z) := by
      simp [unitRatio]
      ring

/-- Helper for Chap10 Example 10 55 5: once an invertible submodule unit has a fixed
endpoint ratio and contains an element nonzero at `0`, it contains the affine Milnor
generator for that ratio. -/
theorem equalEndpointInvertibleSubmoduleUnit_affine_mem_of_endpointRatio
    (I : (Submodule R (equalEndpointPolynomialMulModule k))ˣ) (unitRatio : kˣ)
    (hle :
      (I : Submodule R (equalEndpointPolynomialMulModule k)) ≤
        equalEndpointLineSubmodule k unitRatio)
    (x : equalEndpointPolynomialMulModule k)
    (hx : x ∈ (I : Submodule R (equalEndpointPolynomialMulModule k)))
    (hx0_ne : Polynomial.eval 0 (equalEndpointPolynomialMulModule.toPolynomial k x) ≠ 0) :
    equalEndpointLinePolynomial k unitRatio ∈
      (I : Submodule R (equalEndpointPolynomialMulModule k)) := by
  let A := equalEndpointPolynomialMulModule k
  let c : k := Polynomial.eval 0 (equalEndpointPolynomialMulModule.toPolynomial k x)
  let line : Polynomial k :=
    equalEndpointPolynomialMulModule.toPolynomial k (equalEndpointLinePolynomial k unitRatio)
  have hxcond :
      equalEndpointLineCondition k unitRatio (equalEndpointPolynomialMulModule.toPolynomial k x) :=
    (mem_equalEndpointLineSubmodule (k := k) unitRatio x).mp (hle hx)
  rcases equalEndpointLineCondition_exists_conductor_decomposition (k := k) unitRatio hxcond with
    ⟨q, hq⟩
  let E : Polynomial k := Polynomial.X ^ 2 - Polynomial.X
  have hcond : ((E * q : Polynomial k) : A) ∈ (I : Submodule R A) := by
    simpa [E] using equalEndpointConductorMul_mem_invertibleSubmoduleUnit (k := k) I q
  have hscaled : ((Polynomial.C c * line : Polynomial k) : A) ∈ (I : Submodule R A) := by
    have hsum :
        (((Polynomial.C c * line + E * q : Polynomial k) : Polynomial k) : A) ∈
          (I : Submodule R A) := by
      have hx_eq :
          x = (((Polynomial.C c * line + E * q : Polynomial k) : Polynomial k) : A) := by
        apply equalEndpointPolynomialMulModule_toPolynomial_injective (k := k)
        simpa [c, line, E, equalEndpointLinePolynomial,
          equalEndpointPolynomialMulModule.toPolynomial] using hq
      simpa [hx_eq] using hx
    have hdiff := (I : Submodule R A).sub_mem hsum hcond
    convert hdiff using 1
    apply equalEndpointPolynomialMulModule_toPolynomial_injective (k := k)
    change Polynomial.C c * line = Polynomial.C c * line + E * q - E * q
    rw [add_sub_cancel_right]
  let rInv : R := ⟨Polynomial.C (c⁻¹), equalEndpointConstant_mem_subring (k := k) (c⁻¹)⟩
  have hc_ne : c ≠ 0 := by
    simpa [c] using hx0_ne
  have hscale_eq :
      rInv • ((Polynomial.C c * line : Polynomial k) : A) =
        equalEndpointLinePolynomial k unitRatio := by
    apply equalEndpointPolynomialMulModule_toPolynomial_injective (k := k)
    change ((rInv : R) : Polynomial k) * (Polynomial.C c * line) =
      equalEndpointPolynomialMulModule.toPolynomial k (equalEndpointLinePolynomial k unitRatio)
    simp only [rInv, line, equalEndpointLinePolynomial,
      equalEndpointPolynomialMulModule.toPolynomial]
    rw [← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hc_ne, Polynomial.C_1, one_mul]
  have hline_scaled :
      rInv • ((Polynomial.C c * line : Polynomial k) : A) ∈ (I : Submodule R A) :=
    (I : Submodule R A).smul_mem rInv hscaled
  simpa [hscale_eq] using hline_scaled

/-- Helper for Chap10 Example 10 55 5: a unit submodule contained in a Milnor line and
containing the affine generator and all conductor multiples is exactly that Milnor line unit. -/
theorem equalEndpointSubmoduleUnit_eq_lineSubmoduleUnit_of_generators
    (I : (Submodule R (equalEndpointPolynomialMulModule k))ˣ) (unitRatio : kˣ)
    (hle :
      (I : Submodule R (equalEndpointPolynomialMulModule k)) ≤
        equalEndpointLineSubmodule k unitRatio)
    (haffine :
      equalEndpointLinePolynomial k unitRatio ∈
        (I : Submodule R (equalEndpointPolynomialMulModule k)))
    (hconductor : ∀ q : Polynomial k,
      (((Polynomial.X ^ 2 - Polynomial.X : Polynomial k) * q : Polynomial k) :
        equalEndpointPolynomialMulModule k) ∈
        (I : Submodule R (equalEndpointPolynomialMulModule k))) :
    I = equalEndpointLineSubmoduleUnit k unitRatio := by
  -- Equality of units is equality of underlying submodules; the reverse inclusion follows from
  -- the three-generator presentation of a Milnor line.
  apply Units.ext
  apply le_antisymm
  · exact hle
  · rw [equalEndpointLineSubmoduleUnit_coe, equalEndpointLineSubmodule_eq_span_three]
    apply Submodule.span_le.mpr
    intro x hx
    rcases hx with hx | hx
    · subst hx
      exact haffine
    · rcases hx with hx | hx
      · subst hx
        simpa using hconductor 1
      · rcases hx with hx
        subst hx
        simpa [mul_assoc] using hconductor Polynomial.X

/-- Helper for Chap10 Example 10 55 5: endpoint-ratio inclusion plus the affine generator
membership identifies an invertible submodule unit with the corresponding Milnor line unit. -/
theorem equalEndpointInvertibleSubmoduleUnit_eq_lineSubmoduleUnit_of_endpointRatio
    (I : (Submodule R (equalEndpointPolynomialMulModule k))ˣ) (unitRatio : kˣ)
    (hle :
      (I : Submodule R (equalEndpointPolynomialMulModule k)) ≤
        equalEndpointLineSubmodule k unitRatio)
    (haffine :
      equalEndpointLinePolynomial k unitRatio ∈
        (I : Submodule R (equalEndpointPolynomialMulModule k))) :
    I = equalEndpointLineSubmoduleUnit k unitRatio := by
  -- The conductor containment for invertible submodules supplies the two conductor generators in
  -- the three-generator presentation of `I_u`.
  exact equalEndpointSubmoduleUnit_eq_lineSubmoduleUnit_of_generators (k := k)
    I unitRatio hle haffine
    (equalEndpointConductorMul_mem_invertibleSubmoduleUnit (k := k) I)

/-- Helper for Chap10 Example 10 55 5: every invertible submodule unit of the
polynomial normalization is one of the endpoint-ratio Milnor line units. -/
theorem equalEndpointInvertibleSubmoduleUnit_lineCover
    (I : (Submodule R (equalEndpointPolynomialMulModule k))ˣ) :
    ∃ unitRatio : kˣ, I = equalEndpointLineSubmoduleUnit k unitRatio := by
  -- Extract the common endpoint ratio from a nonzero product with the inverse unit, then use
  -- the affine generator and conductor generators to identify the whole submodule.
  rcases equalEndpointInvertibleSubmoduleUnit_endpointRatio_exists (k := k) I with
    ⟨unitRatio, hle, x, hx, hx0_ne⟩
  have haffine :
      equalEndpointLinePolynomial k unitRatio ∈
        (I : Submodule R (equalEndpointPolynomialMulModule k)) :=
    equalEndpointInvertibleSubmoduleUnit_affine_mem_of_endpointRatio (k := k)
      I unitRatio hle x hx hx0_ne
  exact ⟨unitRatio,
    equalEndpointInvertibleSubmoduleUnit_eq_lineSubmoduleUnit_of_endpointRatio (k := k)
      I unitRatio hle haffine⟩

/-- Helper for Chap10 Example 10 55 5: two surjective additive homomorphisms from the same
source with the same kernel have an additive equivalence of targets that preserves representatives. -/
theorem addEquivOfSurjectiveWithSameKernel_apply_exists
    {A : Type u} {B : Type v} {C : Type w}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (q : B →+ A) (boundary : B →+ C)
    (hq : Function.Surjective q) (hboundary : Function.Surjective boundary)
    (hker : boundary.ker = q.ker) :
    ∃ e : A ≃+ C, ∀ b : B, e (q b) = boundary b := by
  -- Compare both targets with the same quotient of the source, keeping the quotient
  -- representative computation available for the endpoint-boundary adapters.
  let eqLeft : B ⧸ q.ker ≃+ A :=
    QuotientAddGroup.liftEquiv q.ker hq rfl
  let eqKernel : B ⧸ q.ker ≃+ B ⧸ boundary.ker :=
    QuotientAddGroup.quotientAddEquivOfEq hker.symm
  let eqRight : B ⧸ boundary.ker ≃+ C :=
    QuotientAddGroup.liftEquiv boundary.ker hboundary rfl
  let e : A ≃+ C := eqLeft.symm.trans (eqKernel.trans eqRight)
  refine ⟨e, ?_⟩
  intro b
  have hleft : eqLeft.symm (q b) = (b : B ⧸ q.ker) := by
    -- The first quotient isomorphism sends the class of `b` to `q b`, so its inverse sends
    -- `q b` back to that class.
    apply eqLeft.injective
    simp [eqLeft]
  calc
    e (q b) = eqRight (eqKernel (eqLeft.symm (q b))) := rfl
    _ = eqRight (eqKernel (b : B ⧸ q.ker)) := by rw [hleft]
    _ = boundary b := by simp [eqKernel, eqRight]

/-- Helper for Chap10 Example 10 55 5: once Milnor-line Picard classes are known to be
surjective, the endpoint-pair Picard boundary is the line Picard homomorphism composed with the
endpoint-unit ratio map. -/
theorem equalEndpointEndpointPicBoundaryExact_of_linePicHom_surjective
    (hlineSurj : Function.Surjective (equalEndpointLinePicHom k)) :
    ∃ boundary : Additive (kˣ × kˣ) →+ Additive (CommRing.Pic R),
      Function.Surjective boundary ∧
        boundary.ker = (equalEndpointEndpointUnitRatioHom k).ker ∧
        ∀ p : kˣ × kˣ,
          boundary (Additive.ofMul p) =
            Additive.ofMul (equalEndpointLinePicClass k (p.2 * p.1⁻¹)) := by
  let linePicAddHom : Additive kˣ →+ Additive (CommRing.Pic R) :=
    MonoidHom.toAdditive (equalEndpointLinePicHom k)
  let boundary : Additive (kˣ × kˣ) →+ Additive (CommRing.Pic R) :=
    linePicAddHom.comp (equalEndpointEndpointUnitRatioHom k)
  have hlineAddInj : Function.Injective linePicAddHom := by
    intro x y hxy
    -- Removing the `Additive` tags turns injectivity into the already-proved Picard-line
    -- injectivity statement.
    have hmul :
        equalEndpointLinePicHom k x.toMul =
          equalEndpointLinePicHom k y.toMul := by
      simpa [linePicAddHom] using congrArg Additive.toMul hxy
    have hxyMul : x.toMul = y.toMul :=
      equalEndpointLinePicHom_injective (k := k) hmul
    cases x
    cases y
    simpa using hxyMul
  refine ⟨boundary, ?_, ?_, ?_⟩
  · intro pic
    -- Lift the Picard class to a Milnor-line ratio, then lift that ratio to an endpoint pair.
    rcases hlineSurj pic.toMul with ⟨unitRatio, hunitRatio⟩
    rcases equalEndpointEndpointUnitRatioHom_surjective k
        (Additive.ofMul unitRatio) with ⟨p, hp⟩
    refine ⟨p, ?_⟩
    have hpicTag :
        Additive.ofMul (equalEndpointLinePicHom k unitRatio) = pic := by
      simpa using congrArg Additive.ofMul hunitRatio
    simpa [boundary, linePicAddHom, AddMonoidHom.comp_apply, hp] using hpicTag
  · ext p
    -- The only endpoint pairs killed by the Picard boundary are those with trivial ratio.
    constructor
    · intro hp
      rw [AddMonoidHom.mem_ker] at hp ⊢
      have hp' : linePicAddHom ((equalEndpointEndpointUnitRatioHom k) p) =
          linePicAddHom 0 := by
        simpa [boundary, AddMonoidHom.comp_apply] using hp
      exact hlineAddInj hp'
    · intro hp
      rw [AddMonoidHom.mem_ker] at hp ⊢
      simpa [boundary, AddMonoidHom.comp_apply, hp]
  · intro p
    -- On representatives, the composed boundary first takes the endpoint ratio and then the
    -- Milnor-line Picard class.
    simp [boundary, linePicAddHom, AddMonoidHom.comp_apply,
      equalEndpointLinePicHom_apply]

/-- Helper for Chap10 Example 10 55 5: endpoint-pair Picard boundary exactness identifies
Picard classes with endpoint-unit ratios and computes the Milnor-line representative. -/
theorem equalEndpointEndpointPicBoundaryExact :
    ∃ boundary : Additive (kˣ × kˣ) →+ Additive (CommRing.Pic R),
      Function.Surjective boundary ∧
        boundary.ker = (equalEndpointEndpointUnitRatioHom k).ker ∧
        ∀ p : kˣ × kˣ,
          boundary (Additive.ofMul p) =
            Additive.ofMul (equalEndpointLinePicClass k (p.2 * p.1⁻¹)) := by
  -- Route correction: isolate the formal endpoint-pair quotient step.  The remaining source
  -- blocker is now the explicit statement that all invertible submodule units are Milnor lines;
  -- principal ambient-unit factors have already been proved trivial above.
  have hlineSurj : Function.Surjective (equalEndpointLinePicHom k) := by
    have hcover :
        ∀ I : (Submodule R (equalEndpointPolynomialMulModule k))ˣ,
          ∃ unitRatio : kˣ, I = equalEndpointLineSubmoduleUnit k unitRatio := by
      -- The source line-cover argument is now the conductor-plus-endpoint-ratio theorem above.
      intro I
      exact equalEndpointInvertibleSubmoduleUnit_lineCover (k := k) I
    exact equalEndpointLinePicHom_surjective_of_unit_line_cover k hcover
  exact equalEndpointEndpointPicBoundaryExact_of_linePicHom_surjective k hlineSurj

/-- Helper for Chap10 Example 10 55 5: endpoint-pair Picard boundary exactness gives a
computed additive equivalence from endpoint-unit ratios to Picard classes. -/
theorem equalEndpointLinePicEquiv_exists_of_endpointBoundary :
    ∃ e : Additive kˣ ≃+ Additive (CommRing.Pic R),
      ∀ unitRatio : kˣ,
        e (Additive.ofMul unitRatio) =
          Additive.ofMul (equalEndpointLinePicClass k unitRatio) := by
  -- The endpoint boundary and the ratio map are two surjective maps with the same kernel, so the
  -- representative-preserving first isomorphism theorem gives the desired Picard equivalence.
  rcases equalEndpointEndpointPicBoundaryExact k with ⟨boundary, hsurj, hker, happly⟩
  rcases addEquivOfSurjectiveWithSameKernel_apply_exists
      (q := equalEndpointEndpointUnitRatioHom k)
      (boundary := boundary)
      (equalEndpointEndpointUnitRatioHom_surjective k) hsurj hker with
    ⟨e, he⟩
  refine ⟨e, ?_⟩
  intro unitRatio
  let p : kˣ × kˣ := (1, unitRatio)
  have hratio :
      equalEndpointEndpointUnitRatioHom k (Additive.ofMul p) =
        Additive.ofMul unitRatio :=
    equalEndpointEndpointUnitRatioHom_one_pair (k := k) unitRatio
  calc
    e (Additive.ofMul unitRatio) =
        e (equalEndpointEndpointUnitRatioHom k (Additive.ofMul p)) := by
          rw [hratio]
    _ = boundary (Additive.ofMul p) := he (Additive.ofMul p)
    _ = Additive.ofMul (equalEndpointLinePicClass k unitRatio) := by
          simpa [p] using happly p

/-- Helper for Chap10 Example 10 55 5: every Picard class of the equal-endpoint ring is the
Picard class of a Milnor line. -/
theorem equalEndpointLinePicHom_surjective :
    Function.Surjective (equalEndpointLinePicHom k) := by
  intro pic
  -- Route correction: instead of classifying arbitrary invertible submodules of `k[X]`, use the
  -- computed endpoint-pair Picard boundary and lift a Picard class through that equivalence.
  rcases equalEndpointLinePicEquiv_exists_of_endpointBoundary k with ⟨e, he⟩
  let unitRatio : Additive kˣ := e.symm (Additive.ofMul pic)
  refine ⟨unitRatio.toMul, ?_⟩
  have hpicTag :
      Additive.ofMul (equalEndpointLinePicClass k unitRatio.toMul) =
        Additive.ofMul pic := by
    calc
      Additive.ofMul (equalEndpointLinePicClass k unitRatio.toMul) =
          e (Additive.ofMul unitRatio.toMul) := by
            exact (he unitRatio.toMul).symm
      _ = e unitRatio := by
            cases unitRatio
            rfl
      _ = Additive.ofMul pic := e.apply_symm_apply (Additive.ofMul pic)
  have hpic : equalEndpointLinePicClass k unitRatio.toMul = pic := by
    simpa using congrArg Additive.toMul hpicTag
  calc
    equalEndpointLinePicHom k unitRatio.toMul =
        equalEndpointLinePicClass k unitRatio.toMul := by
          exact equalEndpointLinePicHom_apply (k := k) unitRatio.toMul
    _ = pic := hpic

/-- Helper for Chap10 Example 10 55 5: Picard-homomorphism surjectivity packages the explicit
Milnor-line Picard classes as a multiplicative equivalence. -/
theorem equalEndpointLinePicEquiv_exists :
    ∃ e : kˣ ≃* CommRing.Pic R,
      ∀ unitRatio : kˣ, e unitRatio = equalEndpointLinePicClass k unitRatio := by
  -- The structural Picard-surjectivity theorem supplies the missing half of bijectivity; the
  -- existing adapter turns bijectivity into the requested equivalence and computation rule.
  exact equalEndpointLinePicEquiv_exists_of_surjective k
    (equalEndpointLinePicHom_surjective k)

/-- Helper for Chap10 Example 10 55 5: bijectivity of the residual Milnor-line homomorphism
makes the endpoint-pair residual boundary exact and keeps its representative formula. -/
theorem equalEndpointEndpointResidualBoundaryExact_of_residualHom_bijective
    (hbijective :
      Function.Bijective
        (equalEndpointLineResidualHom (k := k) (hmul := equalEndpointLineResidualClass_mul k))) :
    ∃ boundary :
        Additive (kˣ × kˣ) →+ (equalEndpointProjectiveRankMap.{u, u} k).ker,
      Function.Surjective boundary ∧
        boundary.ker = (equalEndpointEndpointUnitRatioHom k).ker ∧
        ∀ p : kˣ × kˣ,
          boundary (Additive.ofMul p) =
            equalEndpointLineResidualClass k (p.2 * p.1⁻¹) := by
  let residualHom :=
    equalEndpointLineResidualHom (k := k) (hmul := equalEndpointLineResidualClass_mul k)
  let boundary :
      Additive (kˣ × kˣ) →+ (equalEndpointProjectiveRankMap.{u, u} k).ker :=
    residualHom.comp (equalEndpointEndpointUnitRatioHom k)
  refine ⟨boundary, ?_, ?_, ?_⟩
  · intro z
    -- Lift a rank-kernel class through the residual homomorphism, then through the endpoint
    -- ratio map.
    rcases hbijective.2 z with ⟨unitRatio, hunitRatio⟩
    rcases equalEndpointEndpointUnitRatioHom_surjective k unitRatio with ⟨p, hp⟩
    refine ⟨p, ?_⟩
    simpa [boundary, residualHom, AddMonoidHom.comp_apply, hp] using hunitRatio
  · ext p
    -- Injectivity of the residual-line homomorphism identifies the kernel with ratio-zero pairs.
    constructor
    · intro hp
      rw [AddMonoidHom.mem_ker] at hp ⊢
      have hp' : residualHom ((equalEndpointEndpointUnitRatioHom k) p) =
          residualHom 0 := by
        simpa [boundary, AddMonoidHom.comp_apply] using hp
      exact hbijective.1 hp'
    · intro hp
      rw [AddMonoidHom.mem_ker] at hp ⊢
      simpa [boundary, AddMonoidHom.comp_apply, hp]
  · intro p
    -- The representative formula follows from the ratio-map computation and the residual
    -- homomorphism computation.
    simp [boundary, residualHom, AddMonoidHom.comp_apply,
      equalEndpointLineResidualHom_apply]

/-- Helper for Chap10 Example 10 55 5: the class-level Picard/Cartan exactness clauses imply
endpoint-pair residual boundary exactness. -/
theorem equalEndpointEndpointResidualBoundaryExact_of_picardCartanExact
    (hexact :
      (∀ unitRatio : kˣ,
        equalEndpointLineResidualClass k unitRatio = 0 →
          equalEndpointLinePicClass k unitRatio = 1) ∧
        ∀ z : (equalEndpointProjectiveRankMap.{u, u} k).ker,
          ∃ unitRatio : kˣ, equalEndpointLineResidualClass k unitRatio = z) :
    ∃ boundary :
        Additive (kˣ × kˣ) →+ (equalEndpointProjectiveRankMap.{u, u} k).ker,
      Function.Surjective boundary ∧
        boundary.ker = (equalEndpointEndpointUnitRatioHom k).ker ∧
        ∀ p : kˣ × kˣ,
          boundary (Additive.ofMul p) =
            equalEndpointLineResidualClass k (p.2 * p.1⁻¹) := by
  -- The exactness clauses give bijectivity of the residual-line homomorphism, which the endpoint
  -- boundary adapter turns into exactness over endpoint-unit pairs.
  have hbijective :
      Function.Bijective
        (equalEndpointLineResidualHom (k := k) (hmul := equalEndpointLineResidualClass_mul k)) :=
    equalEndpointLineResidualHom_bijective_of_zeroPicClass_surjective k hexact.1 hexact.2
  exact equalEndpointEndpointResidualBoundaryExact_of_residualHom_bijective k hbijective

end
