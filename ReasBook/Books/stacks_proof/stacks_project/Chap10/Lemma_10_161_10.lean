import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial

universe u v

section

variable {R : Type u} {K : Type v}
variable [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable {p : ℕ} [Fact p.Prime] [CharP K p]

omit [IsNoetherianRing R] [IsIntegrallyClosed R] [CharP K p] in
/-- Helper for Chap10 Lemma 10 161 10: after writing an element of the fraction field as a quotient
`x / y`, multiplying by `y ^ p` clears denominators and keeps the derivation value nonzero. -/
lemma exists_rescaled_mem_range
    (a : K) (D : Derivation ℤ K K) (hDa : D a ≠ 0) :
    ∃ f b : R,
      algebraMap R K f ≠ 0 ∧
      algebraMap R K b = (algebraMap R K f) ^ p * a ∧
      ((algebraMap R K f) ^ p) * D a ≠ 0 := by
  let hp : Nat.Prime p := Fact.out
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective R a
  refine ⟨y, x * y ^ (p - 1), ?_, ?_, ?_⟩
  · -- The chosen denominator stays nonzero in the fraction field.
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
  · -- Multiplying the quotient `x / y` by `y ^ p` leaves an element coming from `R`.
    have hyK : algebraMap R K y ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
    have hp1 : 1 ≤ p := Nat.succ_le_of_lt hp.pos
    calc
      algebraMap R K (x * y ^ (p - 1))
          = algebraMap R K x * (algebraMap R K y) ^ (p - 1) := by
              simp [map_mul, map_pow]
      _ = algebraMap R K x * ((algebraMap R K y) ^ p * (algebraMap R K y)⁻¹) := by
            simpa using congrArg (fun z => algebraMap R K x * z) (pow_sub₀ (algebraMap R K y) hyK hp1)
      _ = (algebraMap R K y) ^ p * (algebraMap R K x / algebraMap R K y) := by
            rw [div_eq_mul_inv]
            ac_rfl
  · -- A nonzero scalar multiple of the nonzero derivation value is still nonzero.
    exact mul_ne_zero (pow_ne_zero _ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy)) hDa

omit [Fact (Nat.Prime p)] in
/-- Helper for Chap10 Lemma 10 161 10: a derivation that does not kill `a` rules out `a` being a
`p`th power. -/
lemma pth_power_ne_of_derivation_nonzero
    (D : Derivation ℤ K K) {a : K} (hDa : D a ≠ 0) :
    ∀ b : K, b ^ p ≠ a := by
  intro b hb
  apply hDa
  rw [← hb, Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul K]
  simp

omit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsFractionRing R K] in
/-- Helper for Chap10 Lemma 10 161 10: the derivation hypothesis makes `X ^ p - C a` irreducible over
the fraction field. -/
lemma irreducible_X_pow_sub_C_of_exists_derivation
    (a : K)
    (hD : ∃ D : Derivation ℤ K K,
      Set.MapsTo D (Set.range (algebraMap R K)) (Set.range (algebraMap R K)) ∧
        D a ≠ 0) :
    Irreducible (X ^ p - C a) := by
  rcases hD with ⟨D, -, hDa⟩
  apply X_pow_sub_C_irreducible_of_prime (Fact.out : Nat.Prime p)
  exact pth_power_ne_of_derivation_nonzero (p := p) D hDa

omit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsFractionRing R K]
  [Fact (Nat.Prime p)] in
/-- Helper for Chap10 Lemma 10 161 10: after the denominator-clearing step, differentiating the relation
`b = f ^ p * a` shows that the new coefficient still has nonzero derivative. -/
lemma rescaled_derivation_nonzero
    (D : Derivation ℤ K K)
    {f b : R}
    (hf : algebraMap R K f ≠ 0)
    (hb : algebraMap R K b = (algebraMap R K f) ^ p * a)
    (hDa : D a ≠ 0) :
    D (algebraMap R K b) ≠ 0 := by
  -- Differentiate the rescaling identity; the `p`th power factor contributes no derivative in
  -- characteristic `p`, so the new derivative is the same nonzero scalar multiple of `D a`.
  have hpow :
      D ((algebraMap R K f) ^ p) = 0 := by
    rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul K]
    simp
  have hderiv :
      D (algebraMap R K b) = ((algebraMap R K f) ^ p) * D a := by
    calc
      D (algebraMap R K b) = D ((algebraMap R K f) ^ p * a) := by rw [hb]
      _ = ((algebraMap R K f) ^ p) * D a + a * D ((algebraMap R K f) ^ p) := by
            rw [Derivation.leibniz]
            simp [Algebra.smul_def, add_comm]
      _ = ((algebraMap R K f) ^ p) * D a := by simp [hpow]
  rw [hderiv]
  exact mul_ne_zero (pow_ne_zero _ hf) hDa

omit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsFractionRing R K]
  [Fact (Nat.Prime p)] [CharP K p] in
/-- Helper for Chap10 Lemma 10 161 10: if `b = f ^ p * a` with `f ≠ 0`, then adjoining a `p`th root of
`b` is `K`-algebra equivalent to adjoining a `p`th root of `a`, by rescaling the distinguished
root by `f`. -/
theorem adjoinRoot_pth_root_rescale_equiv_of_mem_range
    (a : K) {f b : R}
    (hf : algebraMap R K f ≠ 0)
    (hb : algebraMap R K b = (algebraMap R K f) ^ p * a) :
    Nonempty (AdjoinRoot (X ^ p - C (algebraMap R K b)) ≃ₐ[K] AdjoinRoot (X ^ p - C a)) := by
  let Pₐ : K[X] := X ^ p - C a
  let P_b : K[X] := X ^ p - C (algebraMap R K b)
  let Lₐ := AdjoinRoot Pₐ
  let L_b := AdjoinRoot P_b
  let u : K := algebraMap R K f
  have hu : u ≠ 0 := hf
  let α : Lₐ := algebraMap K Lₐ u * AdjoinRoot.root Pₐ
  have hα :
      P_b.eval₂ (Algebra.ofId K Lₐ) α = 0 := by
    -- The scaled root satisfies the polynomial with coefficient `b`.
    have hαpow : α ^ p = algebraMap K Lₐ (algebraMap R K b) := by
      calc
        α ^ p = (algebraMap K Lₐ u * AdjoinRoot.root Pₐ) ^ p := by rfl
        _ = (algebraMap K Lₐ u) ^ p * (AdjoinRoot.root Pₐ) ^ p := by
              rw [mul_pow]
        _ = algebraMap K Lₐ (u ^ p) * AdjoinRoot.of Pₐ a := by
              rw [map_pow, root_X_pow_sub_C_pow]
        _ = algebraMap K Lₐ (u ^ p * a) := by
              rw [AdjoinRoot.algebraMap_eq]
              simp [map_mul]
        _ = algebraMap K Lₐ (algebraMap R K b) := by rw [hb]
    calc
      P_b.eval₂ (Algebra.ofId K Lₐ) α = α ^ p - algebraMap K Lₐ (algebraMap R K b) := by
        simp [P_b, α]
      _ = 0 := by rw [hαpow, sub_self]
  let φ : L_b →ₐ[K] Lₐ := AdjoinRoot.liftAlgHom P_b (Algebra.ofId K Lₐ) α hα
  let β : L_b := algebraMap K L_b u⁻¹ * AdjoinRoot.root P_b
  have hβ :
      Pₐ.eval₂ (Algebra.ofId K L_b) β = 0 := by
    -- Rescaling by the inverse scalar sends a root of `X ^ p - b` back to a root of `X ^ p - a`.
    have hu_pow : u ^ p ≠ 0 := pow_ne_zero _ hu
    have hβpow : β ^ p = algebraMap K L_b a := by
      calc
        β ^ p = (algebraMap K L_b u⁻¹ * AdjoinRoot.root P_b) ^ p := by rfl
        _ = (algebraMap K L_b u⁻¹) ^ p * (AdjoinRoot.root P_b) ^ p := by
              rw [mul_pow]
        _ = algebraMap K L_b ((u⁻¹) ^ p) * AdjoinRoot.of P_b (algebraMap R K b) := by
              rw [map_pow, root_X_pow_sub_C_pow]
        _ = algebraMap K L_b (((u⁻¹) ^ p) * algebraMap R K b) := by
              rw [AdjoinRoot.algebraMap_eq]
              simp [map_mul]
        _ = algebraMap K L_b (((u⁻¹) ^ p) * (u ^ p * a)) := by rw [hb]
        _ = algebraMap K L_b a := by
              rw [← mul_assoc, inv_pow, inv_mul_cancel₀ hu_pow, one_mul]
    calc
      Pₐ.eval₂ (Algebra.ofId K L_b) β = β ^ p - algebraMap K L_b a := by
        simp [Pₐ, β]
      _ = 0 := by rw [hβpow, sub_self]
  let ψ : Lₐ →ₐ[K] L_b := AdjoinRoot.liftAlgHom Pₐ (Algebra.ofId K L_b) β hβ
  have hψφ : ψ.comp φ = AlgHom.id K L_b := by
    -- The composite fixes the distinguished root, hence is the identity.
    apply AdjoinRoot.algHom_ext
    calc
      ψ (φ (AdjoinRoot.root P_b))
          = ψ (algebraMap K Lₐ u * AdjoinRoot.root Pₐ) := by
              rw [AdjoinRoot.liftAlgHom_root]
      _ = ψ (algebraMap K Lₐ u) * ψ (AdjoinRoot.root Pₐ) := by rw [map_mul]
      _ = algebraMap K L_b u * (algebraMap K L_b u⁻¹ * AdjoinRoot.root P_b) := by
            rw [AlgHom.commutes, AdjoinRoot.liftAlgHom_root]
      _ = AdjoinRoot.root P_b := by
            rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hu, map_one, one_mul]
      _ = AlgHom.id K L_b (AdjoinRoot.root P_b) := rfl
  have hφψ : φ.comp ψ = AlgHom.id K Lₐ := by
    -- The symmetric computation shows the reverse composite is also the identity.
    apply AdjoinRoot.algHom_ext
    calc
      φ (ψ (AdjoinRoot.root Pₐ))
          = φ (algebraMap K L_b u⁻¹ * AdjoinRoot.root P_b) := by
              rw [AdjoinRoot.liftAlgHom_root]
      _ = φ (algebraMap K L_b u⁻¹) * φ (AdjoinRoot.root P_b) := by rw [map_mul]
      _ = algebraMap K Lₐ u⁻¹ * (algebraMap K Lₐ u * AdjoinRoot.root Pₐ) := by
            rw [AlgHom.commutes, AdjoinRoot.liftAlgHom_root]
      _ = AdjoinRoot.root Pₐ := by
            rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hu, map_one, one_mul]
      _ = AlgHom.id K Lₐ (AdjoinRoot.root Pₐ) := rfl
  exact ⟨AlgEquiv.ofAlgHom φ ψ hφψ hψφ⟩

omit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsFractionRing R K] in
/-- Helper for Chap10 Lemma 10 161 10: the derivation value on an element of `R` again comes from
`R` when the derivation preserves the image of `R`. -/
lemma exists_derivation_image_eq
    (b : R)
    (D : Derivation ℤ K K)
    (hMaps : Set.MapsTo D (Set.range (algebraMap R K)) (Set.range (algebraMap R K))) :
    ∃ delta0 : R, algebraMap R K delta0 = D (algebraMap R K b) := by
  -- Apply the range-preserving hypothesis to the coefficient coming from `b`.
  simpa using hMaps ⟨b, rfl⟩

omit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsFractionRing R K] in
/-- Helper for Chap10 Lemma 10 161 10: the coefficient `δ₀ ∈ R` mapping to `D(b)` is nonzero whenever
`D(b)` is nonzero. -/
lemma derivation_image_ne_zero
    (b : R)
    (D : Derivation ℤ K K)
    {delta0 : R}
    (hdelta : algebraMap R K delta0 = D (algebraMap R K b))
    (hDb : D (algebraMap R K b) ≠ 0) :
    delta0 ≠ 0 := by
  -- Injectivity of the fraction-field map lets us pull the nonvanishing back to `R`.
  intro hzero
  apply hDb
  simpa [hzero] using hdelta.symm

/-- Helper for Chap10 Lemma 10 161 10: fix the `Fin p`-indexed power basis for the reduced polynomial
`X ^ p - b`. -/
noncomputable def adjoinRoot_pth_root_basis (b : R) :
    Module.Basis (Fin p) K (AdjoinRoot (X ^ p - C (algebraMap R K b))) :=
  (AdjoinRoot.powerBasis' (monic_X_pow_sub_C (algebraMap R K b) (Fact.out : Nat.Prime p).ne_zero)).basis.reindex <|
    finCongr (natDegree_X_pow_sub_C (R := K) (n := p) (r := algebraMap R K b))

omit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsFractionRing R K]
  [CharP K p] in
/-- Helper for Chap10 Lemma 10 161 10: the fixed `Fin p` basis vectors are the powers of the adjoined
root. -/
lemma adjoinRoot_pth_root_basis_apply
    (b : R) (j : Fin p) :
    adjoinRoot_pth_root_basis (R := R) (K := K) (p := p) b j =
      AdjoinRoot.root (X ^ p - C (algebraMap R K b)) ^ (j : ℕ) := by
  -- Reindexing the canonical power basis only changes the index type, not the basis vectors.
  rw [adjoinRoot_pth_root_basis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow,
    finCongr_symm_apply, Fin.val_cast]
  simp [AdjoinRoot.powerBasis']

/-- Helper for Chap10 Lemma 10 161 10: coordinates in the fixed `Fin p` power basis. -/
noncomputable def adjoinRoot_pth_root_coord (b : R) :
    AdjoinRoot (X ^ p - C (algebraMap R K b)) → Fin p → K :=
  fun y j ↦ (adjoinRoot_pth_root_basis (R := R) (K := K) (p := p) b).repr y j

omit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsFractionRing R K]
  [CharP K p] in
/-- Helper for Chap10 Lemma 10 161 10: every element of the reduced `AdjoinRoot` algebra reconstructs
from its fixed `Fin p` power-basis coordinates. -/
lemma adjoinRoot_pth_root_sum_repr
    (b : R)
    (y : AdjoinRoot (X ^ p - C (algebraMap R K b))) :
    ∑ j : Fin p, adjoinRoot_pth_root_coord (R := R) (K := K) (p := p) b y j •
        AdjoinRoot.root (X ^ p - C (algebraMap R K b)) ^ (j : ℕ) = y := by
  -- Reconstruct from the basis coordinates, then rewrite the basis vectors as powers of the root.
  simpa [adjoinRoot_pth_root_coord, Algebra.smul_def, adjoinRoot_pth_root_basis_apply] using
    (adjoinRoot_pth_root_basis (R := R) (K := K) (p := p) b).sum_repr y

omit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsFractionRing R K]
  [CharP K p] in
/-- Helper for Chap10 Lemma 10 161 10: the fixed power-basis coordinates recover the coefficients
of an explicit root-power expansion. -/
lemma adjoinRoot_pth_root_coord_sum
    (b : R)
    (c : Fin p → K)
    (j : Fin p) :
    adjoinRoot_pth_root_coord (R := R) (K := K) (p := p) b
      (∑ k : Fin p,
        c k • AdjoinRoot.root (X ^ p - C (algebraMap R K b)) ^ (k : ℕ)) j = c j := by
  let basis := adjoinRoot_pth_root_basis (R := R) (K := K) (p := p) b
  -- Evaluate the chosen coordinate functional on the explicit basis expansion.
  have hrepr :
      basis.repr (∑ k : Fin p, c k • basis k) j = c j := by
    simpa using congrArg (fun f : Fin p → K => f j) (basis.repr_sum_self c)
  simpa [basis, adjoinRoot_pth_root_coord, adjoinRoot_pth_root_basis_apply] using hrepr

omit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsFractionRing R K] in
/-- Helper for Chap10 Lemma 10 161 10: the `p`th power of an element in the fixed power basis
descends to a scalar in the fraction field. -/
lemma adjoinRoot_pth_root_pow_eq_scalarImage
    (b : R)
    (z : AdjoinRoot (X ^ p - C (algebraMap R K b))) :
    z ^ p =
      algebraMap K (AdjoinRoot (X ^ p - C (algebraMap R K b)))
        (∑ j : Fin p,
          adjoinRoot_pth_root_coord (R := R) (K := K) (p := p) b z j ^ p *
            (algebraMap R K b) ^ (j : ℕ)) := by
  letI : Nontrivial (AdjoinRoot (X ^ p - C (algebraMap R K b))) :=
    AdjoinRoot.nontrivial
      (f := X ^ p - C (algebraMap R K b))
      (by
        rw [Polynomial.degree_eq_natDegree
          (X_pow_sub_C_ne_zero ((Fact.out : Nat.Prime p).pos) (algebraMap R K b)),
          natDegree_X_pow_sub_C]
        exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)
  letI : CharP (AdjoinRoot (X ^ p - C (algebraMap R K b))) p :=
    charP_of_injective_ringHom
      (algebraMap K (AdjoinRoot (X ^ p - C (algebraMap R K b)))).injective p
  let x : AdjoinRoot (X ^ p - C (algebraMap R K b)) :=
    AdjoinRoot.root (X ^ p - C (algebraMap R K b))
  let coord :
      AdjoinRoot (X ^ p - C (algebraMap R K b)) → Fin p → K :=
    adjoinRoot_pth_root_coord (R := R) (K := K) (p := p) b
  -- Expand in the fixed basis, apply Frobenius termwise, and collapse `x ^ p` to the scalar `b`.
  calc
    z ^ p = (∑ j : Fin p, coord z j • x ^ (j : ℕ)) ^ p := by
      rw [adjoinRoot_pth_root_sum_repr (R := R) (K := K) (p := p) b z]
    _ = ∑ j : Fin p, (coord z j • x ^ (j : ℕ)) ^ p := by
      simpa using
        (sum_pow_char
          (R := AdjoinRoot (X ^ p - C (algebraMap R K b)))
          (p := p)
          (s := Finset.univ)
          (f := fun j : Fin p ↦ coord z j • x ^ (j : ℕ)))
    _ = ∑ j : Fin p,
          algebraMap K (AdjoinRoot (X ^ p - C (algebraMap R K b)))
            (coord z j ^ p * (algebraMap R K b) ^ (j : ℕ)) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hxpow : (x ^ (j : ℕ)) ^ p = (x ^ p) ^ (j : ℕ) := by
            rw [← pow_mul, Nat.mul_comm, pow_mul]
          calc
            (coord z j • x ^ (j : ℕ)) ^ p =
                (algebraMap K (AdjoinRoot (X ^ p - C (algebraMap R K b))) (coord z j) *
                  x ^ (j : ℕ)) ^ p := by
                    rw [Algebra.smul_def]
            _ = (algebraMap K (AdjoinRoot (X ^ p - C (algebraMap R K b))) (coord z j)) ^ p *
                  (x ^ (j : ℕ)) ^ p := by
                    rw [mul_pow]
            _ = algebraMap K (AdjoinRoot (X ^ p - C (algebraMap R K b))) (coord z j ^ p) *
                  (x ^ p) ^ (j : ℕ) := by
                    rw [map_pow, hxpow]
            _ = algebraMap K (AdjoinRoot (X ^ p - C (algebraMap R K b))) (coord z j ^ p) *
                  algebraMap K (AdjoinRoot (X ^ p - C (algebraMap R K b)))
                    ((algebraMap R K b) ^ (j : ℕ)) := by
                      rw [root_X_pow_sub_C_pow, AdjoinRoot.algebraMap_eq, ← map_pow]
            _ = algebraMap K (AdjoinRoot (X ^ p - C (algebraMap R K b)))
                  (coord z j ^ p * (algebraMap R K b) ^ (j : ℕ)) := by
                    rw [map_mul]
    _ = algebraMap K (AdjoinRoot (X ^ p - C (algebraMap R K b)))
          (∑ j : Fin p, coord z j ^ p * (algebraMap R K b) ^ (j : ℕ)) := by
            rw [map_sum]

omit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsFractionRing R K]
  [CharP K p] in
/-- Helper for Chap10 Lemma 10 161 10: when the coefficient already lies in `R`, the distinguished root
is integral over `R`. -/
lemma adjoinRoot_root_isIntegral_of_mem_range
    (b : R) :
    IsIntegral R
      (AdjoinRoot.root (X ^ p - C (algebraMap R K b)) :
        AdjoinRoot (X ^ p - C (algebraMap R K b))) := by
  refine ⟨X ^ p - C b, monic_X_pow_sub_C b (Fact.out : Nat.Prime p).ne_zero, ?_⟩
  -- The distinguished root satisfies the monic polynomial `X ^ p - b` over `R`.
  calc
    aeval
        (AdjoinRoot.root (X ^ p - C (algebraMap R K b)) :
          AdjoinRoot (X ^ p - C (algebraMap R K b)))
        (X ^ p - C b)
      = (AdjoinRoot.root (X ^ p - C (algebraMap R K b))) ^ p -
          algebraMap R (AdjoinRoot (X ^ p - C (algebraMap R K b))) b := by
            simp
    _ = 0 := by
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
            IsScalarTower.algebraMap_eq R K
              (AdjoinRoot (X ^ p - C (algebraMap R K b)))] using
            sub_eq_zero.mpr (root_X_pow_sub_C_pow p (algebraMap R K b))

omit [IsDomain R] [IsIntegrallyClosed R] in
/-- Helper for Chap10 Lemma 10 161 10: once the integral closure is trapped in the span of a finite
family, Noetherianity turns that containment into module finiteness. -/
lemma integralClosure_finite_of_le_span
    {L : Type*} [Field L] [Algebra R L]
    {s : Set L} (hs : s.Finite)
    (hle : Subalgebra.toSubmodule (integralClosure R L) ≤ Submodule.span R s) :
    Module.Finite R (integralClosure R L) := by
  -- The finite family gives a finitely generated ambient span.
  have hfg_span : (Submodule.span R s).FG := by
    rw [← Module.Finite.iff_fg]
    exact Module.Finite.span_of_finite R hs
  -- The integral closure submodule is finitely generated inside that Noetherian ambient module.
  have hfg_ic : (Subalgebra.toSubmodule (integralClosure R L)).FG :=
    Submodule.FG.of_le hfg_span hle
  exact ⟨(Subalgebra.toSubmodule (integralClosure R L)).fg_top.mpr hfg_ic⟩

omit [IsNoetherianRing R] [IsIntegrallyClosed R] [CharP K p] in
/-- Helper for Chap10 Lemma 10 161 10: once every fixed power-basis coefficient is cleared by the same
power of `D(b)`, the element lies in the span of the corresponding rescaled root powers. -/
lemma mem_span_scaled_root_powers_of_cleared_coordinates
    (b delta0 : R)
    (hdelta0 : delta0 ≠ 0)
    (y : AdjoinRoot (X ^ p - C (algebraMap R K b)))
    (hcoeff : ∀ j : Fin p, ∃ r : R,
      algebraMap R K r =
        (algebraMap R K delta0 : K) ^ (p - 1) *
          adjoinRoot_pth_root_coord (R := R) (K := K) (p := p) b y j) :
    y ∈ Submodule.span R
      (Set.range fun j : Fin p ↦
        algebraMap K (AdjoinRoot (X ^ p - C (algebraMap R K b)))
          (((algebraMap R K delta0 : K) ^ (p - 1))⁻¹) *
            AdjoinRoot.root (X ^ p - C (algebraMap R K b)) ^ (j : ℕ)) := by
  let delta : K := algebraMap R K delta0
  let deltaPow : K := delta ^ (p - 1)
  have hdelta : delta ≠ 0 := by
    -- The derivative value stays nonzero after mapping into the fraction field.
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr hdelta0)
  have hdeltaPow : deltaPow ≠ 0 := by
    -- The common clearing scalar is a nonzero power of `delta`.
    simp [deltaPow, delta, hdelta]
  -- Reconstruct `y` from its fixed power-basis coordinates and place each summand in the span.
  rw [← adjoinRoot_pth_root_sum_repr (R := R) (K := K) (p := p) b y]
  refine Submodule.sum_mem _ ?_
  intro j hj
  rcases hcoeff j with ⟨r, hr⟩
  have hcoord :
      (algebraMap R K r : K) * deltaPow⁻¹ =
        adjoinRoot_pth_root_coord (R := R) (K := K) (p := p) b y j := by
    -- Solving for the coefficient is the endgame algebra from the source proof.
    calc
      (algebraMap R K r : K) * deltaPow⁻¹ =
          (deltaPow *
              adjoinRoot_pth_root_coord (R := R) (K := K) (p := p) b y j) * deltaPow⁻¹ := by
            simpa [deltaPow, delta] using congrArg (fun z : K ↦ z * deltaPow⁻¹) hr
      _ = adjoinRoot_pth_root_coord (R := R) (K := K) (p := p) b y j *
            (deltaPow * deltaPow⁻¹) := by
            ac_rfl
      _ = adjoinRoot_pth_root_coord (R := R) (K := K) (p := p) b y j := by
            rw [mul_inv_cancel₀ hdeltaPow, mul_one]
  have hterm :
      adjoinRoot_pth_root_coord (R := R) (K := K) (p := p) b y j •
          AdjoinRoot.root (X ^ p - C (algebraMap R K b)) ^ (j : ℕ) =
        r •
          (algebraMap K (AdjoinRoot (X ^ p - C (algebraMap R K b))) (deltaPow⁻¹) *
            AdjoinRoot.root (X ^ p - C (algebraMap R K b)) ^ (j : ℕ)) := by
    -- Rewrite the `K`-coefficient as an `R`-scalar times the rescaled basis vector.
    rw [Algebra.smul_def, Algebra.smul_def, ← hcoord]
    calc
      algebraMap K (AdjoinRoot (X ^ p - C (algebraMap R K b)))
          ((algebraMap R K r : K) * deltaPow⁻¹) *
          AdjoinRoot.root (X ^ p - C (algebraMap R K b)) ^ (j : ℕ) =
        (algebraMap R (AdjoinRoot (X ^ p - C (algebraMap R K b))) r *
            algebraMap K (AdjoinRoot (X ^ p - C (algebraMap R K b))) (deltaPow⁻¹)) *
          AdjoinRoot.root (X ^ p - C (algebraMap R K b)) ^ (j : ℕ) := by
            simp [map_mul, IsScalarTower.algebraMap_eq R K
              (AdjoinRoot (X ^ p - C (algebraMap R K b)))]
      _ = algebraMap R (AdjoinRoot (X ^ p - C (algebraMap R K b))) r *
            (algebraMap K (AdjoinRoot (X ^ p - C (algebraMap R K b))) (deltaPow⁻¹) *
              AdjoinRoot.root (X ^ p - C (algebraMap R K b)) ^ (j : ℕ)) := by
            rw [mul_assoc]
  rw [hterm]
  -- Each rescaled power is one of the chosen generators, so scalar closure finishes.
  have hgen :
      algebraMap K (AdjoinRoot (X ^ p - C (algebraMap R K b))) (deltaPow⁻¹) *
          AdjoinRoot.root (X ^ p - C (algebraMap R K b)) ^ (j : ℕ) ∈
        Set.range fun j : Fin p ↦
          algebraMap K (AdjoinRoot (X ^ p - C (algebraMap R K b))) (deltaPow⁻¹) *
            AdjoinRoot.root (X ^ p - C (algebraMap R K b)) ^ (j : ℕ) := by
    exact ⟨j, rfl⟩
  exact Submodule.smul_mem _ r (Submodule.subset_span hgen)

omit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsFractionRing R K] in
/-- Helper for Chap10 Lemma 10 161 10: if a unit multiple of a fraction-field element comes from
`R`, then the element itself already comes from `R`. -/
lemma exists_mem_range_of_unit_mul
    {u : R} (hu : IsUnit u) {x : K}
    (hx : ∃ r : R, algebraMap R K r = algebraMap R K u * x) :
    ∃ r : R, algebraMap R K r = x := by
  rcases hx with ⟨r, hr⟩
  let uUnit : Rˣ := hu.unit
  refine ⟨↑uUnit⁻¹ * r, ?_⟩
  -- Multiply by the inverse unit inside `R` before mapping to the fraction field.
  calc
    algebraMap R K (↑uUnit⁻¹ * r)
        = algebraMap R K (↑uUnit⁻¹) * algebraMap R K r := by
            simp [map_mul]
    _ = algebraMap R K (↑uUnit⁻¹) * (algebraMap R K u * x) := by rw [hr]
    _ = (algebraMap R K (↑uUnit⁻¹) * algebraMap R K u) * x := by rw [mul_assoc]
    _ = x := by
          have hinv : (↑uUnit⁻¹ : R) * u = 1 := by
            simpa [uUnit, hu.unit_spec] using uUnit.inv_val
          rw [← map_mul, hinv, map_one, one_mul]

omit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsFractionRing R K] in
/-- Helper for Chap10 Lemma 10 161 10: once the differentiated scalar sum is already descended to
`R`, the explicit lowered basis sum is integral over `R`. -/
lemma loweredIsIntegral_of_scalarWitness
    (b : R)
    (coeff : Fin p → K)
    (hcoeff : ∃ r : R,
      algebraMap R K r =
        ∑ j : Fin p, coeff j ^ p * (algebraMap R K b) ^ (j : ℕ)) :
    IsIntegral R
      ((∑ j : Fin p,
          coeff j • AdjoinRoot.root (X ^ p - C (algebraMap R K b)) ^ (j : ℕ)) :
        AdjoinRoot (X ^ p - C (algebraMap R K b))) := by
  rcases hcoeff with ⟨r, hr⟩
  let lowered : AdjoinRoot (X ^ p - C (algebraMap R K b)) :=
    ∑ j : Fin p, coeff j • AdjoinRoot.root (X ^ p - C (algebraMap R K b)) ^ (j : ℕ)
  have hcoord :
      ∀ j : Fin p,
        adjoinRoot_pth_root_coord (R := R) (K := K) (p := p) b lowered j = coeff j := by
    -- The explicit basis expansion was chosen so that the fixed coordinates are exactly `coeff`.
    intro j
    simpa [lowered] using
      adjoinRoot_pth_root_coord_sum
        (R := R) (K := K) (p := p) b coeff j
  have hpow :
      lowered ^ p =
        algebraMap R (AdjoinRoot (X ^ p - C (algebraMap R K b))) r := by
    -- Compare the explicit basis sum with the Frobenius power formula, then rewrite the descended
    -- scalar through the chosen witness from `R`.
    have hpow' :
        lowered ^ p =
          ∑ j : Fin p,
            (AdjoinRoot.of (X ^ p - C (algebraMap R K b))) (coeff j) ^ p *
              (AdjoinRoot.of (X ^ p - C (algebraMap R K b))) (algebraMap R K b) ^ (j : ℕ) := by
      simpa [hcoord, AdjoinRoot.algebraMap_eq] using
        adjoinRoot_pth_root_pow_eq_scalarImage
          (R := R) (K := K) (p := p) b lowered
    have hr' :
        (∑ j : Fin p,
          (AdjoinRoot.of (X ^ p - C (algebraMap R K b))) (coeff j) ^ p *
            (AdjoinRoot.of (X ^ p - C (algebraMap R K b))) (algebraMap R K b) ^ (j : ℕ)) =
          algebraMap R (AdjoinRoot (X ^ p - C (algebraMap R K b))) r := by
      have hmap :
          algebraMap K (AdjoinRoot (X ^ p - C (algebraMap R K b)))
              (∑ j : Fin p, coeff j ^ p * (algebraMap R K b) ^ (j : ℕ)) =
            algebraMap K (AdjoinRoot (X ^ p - C (algebraMap R K b))) ((algebraMap R K) r) := by
        exact congrArg
          (algebraMap K (AdjoinRoot (X ^ p - C (algebraMap R K b))))
          hr.symm
      calc
        (∑ j : Fin p,
          (AdjoinRoot.of (X ^ p - C (algebraMap R K b))) (coeff j) ^ p *
            (AdjoinRoot.of (X ^ p - C (algebraMap R K b))) (algebraMap R K b) ^ (j : ℕ)) =
            algebraMap K (AdjoinRoot (X ^ p - C (algebraMap R K b)))
              (∑ j : Fin p, coeff j ^ p * (algebraMap R K b) ^ (j : ℕ)) := by
              rw [map_sum]
              apply Finset.sum_congr rfl
              intro j hj
              simp [AdjoinRoot.algebraMap_eq, map_mul, map_pow]
        _ = algebraMap K (AdjoinRoot (X ^ p - C (algebraMap R K b))) ((algebraMap R K) r) := hmap
        _ = algebraMap R (AdjoinRoot (X ^ p - C (algebraMap R K b))) r := by
              simp [IsScalarTower.algebraMap_eq R K
                (AdjoinRoot (X ^ p - C (algebraMap R K b)))]
    calc
      lowered ^ p =
          ∑ j : Fin p,
            (AdjoinRoot.of (X ^ p - C (algebraMap R K b))) (coeff j) ^ p *
              (AdjoinRoot.of (X ^ p - C (algebraMap R K b))) (algebraMap R K b) ^ (j : ℕ) := hpow'
      _ = algebraMap R (AdjoinRoot (X ^ p - C (algebraMap R K b))) r := hr'
  -- The lowered element is integral because its `p`th power is the image of an `R`-scalar.
  refine IsIntegral.of_pow (show 0 < p by exact (Fact.out : Nat.Prime p).pos) ?_
  rw [hpow]
  exact isIntegral_algebraMap

omit [IsDomain R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 161 10: the scalar coming from the `p`th power of an integral
power-basis expansion already descends to `R`. -/
lemma scalarWitness_of_integralPowerBasisExpansion
    (b : R)
    (z : integralClosure R (AdjoinRoot (X ^ p - C (algebraMap R K b)))) :
    ∃ r : R,
      algebraMap R K r =
        ∑ j : Fin p,
          adjoinRoot_pth_root_coord (R := R) (K := K) (p := p) b (z : _) j ^ p *
            (algebraMap R K b) ^ (j : ℕ) := by
  let scalar : K :=
    ∑ j : Fin p,
      adjoinRoot_pth_root_coord (R := R) (K := K) (p := p) b (z : _) j ^ p *
        (algebraMap R K b) ^ (j : ℕ)
  letI : Nontrivial (AdjoinRoot (X ^ p - C (algebraMap R K b))) :=
    AdjoinRoot.nontrivial
      (f := X ^ p - C (algebraMap R K b))
      (by
        rw [Polynomial.degree_eq_natDegree
          (X_pow_sub_C_ne_zero ((Fact.out : Nat.Prime p).pos) (algebraMap R K b)),
          natDegree_X_pow_sub_C]
        exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)
  have hscalar_integral :
      IsIntegral R (algebraMap K (AdjoinRoot (X ^ p - C (algebraMap R K b))) scalar) := by
    -- The scalar image is the `p`th power of the integral element `z`.
    rw [← adjoinRoot_pth_root_pow_eq_scalarImage (R := R) (K := K) (p := p) b (z : _)]
    exact z.2.pow p
  have hscalarK : IsIntegral R scalar := by
    -- Injectivity of the scalar map from `K` lets us descend integrality back to the fraction field.
    exact (isIntegral_algebraMap_iff
      (algebraMap K (AdjoinRoot (X ^ p - C (algebraMap R K b)))).injective).mp hscalar_integral
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hscalarK
  exact ⟨r, by simpa [scalar] using hr⟩

/-- Helper for Chap10 Lemma 10 161 10: Frobenius fixes the natural-number scalars in
characteristic `p`. -/
lemma natCast_pow_char (n : ℕ) : ((n : K) ^ p) = (n : K) := by
  induction n with
  | zero =>
      simpa [(Fact.out : Nat.Prime p).ne_zero]
  | succ n ih =>
      -- Freshman's dream reduces the successor step to the induction hypothesis.
      calc
        ((n.succ : K) ^ p) = ((n : K) + 1) ^ p := by simp [Nat.cast_succ]
        _ = (n : K) ^ p + 1 ^ p := by rw [add_pow_char]
        _ = (n : K) + 1 := by rw [ih, one_pow]
        _ = (n.succ : K) := by simp [Nat.cast_succ]

omit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] in
/-- Helper for Chap10 Lemma 10 161 10: a positive natural number below the characteristic prime
remains a unit after mapping into `R`. -/
lemma natCastIsUnit_of_pos_lt_prime
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K] [CharP K p]
    {n : ℕ} (hn : 0 < n) (hnp : n < p) :
    IsUnit ((n : ℕ) : R) := by
  letI : CharP R p := (algebraMap R K).charP (IsFractionRing.injective R K) p
  exact
    (CharP.isUnit_natCast_iff (R := R) (p := p) (Fact.out : Nat.Prime p)).2
      (Nat.not_dvd_of_pos_of_lt hn hnp)

omit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsFractionRing R K] in
/-- Helper for Chap10 Lemma 10 161 10: differentiating one summand of the scalar witness only
hits the `b`-power, because the coefficient is already a `p`th power in characteristic `p`. -/
lemma derivative_powerBasisScalarTerm
    (b : R)
    (D : Derivation ℤ K K)
    {delta0 : R}
    (hdelta : algebraMap R K delta0 = D (algebraMap R K b))
    (z : integralClosure R (AdjoinRoot (X ^ p - C (algebraMap R K b))))
    (j : Fin p) :
    D (adjoinRoot_pth_root_coord (R := R) (K := K) (p := p) b (z : _) j ^ p *
        (algebraMap R K b) ^ (j : ℕ)) =
      adjoinRoot_pth_root_coord (R := R) (K := K) (p := p) b (z : _) j ^ p *
        ((j : K) * (algebraMap R K b) ^ ((j : ℕ) - 1) * algebraMap R K delta0) := by
  -- The `p`th power coefficient contributes zero to the derivative, so only the power of `b`
  -- survives.
  rw [Derivation.leibniz, Derivation.leibniz_pow, Derivation.leibniz_pow, hdelta]
  simp [Algebra.smul_def, mul_assoc, mul_comm]

/-- Helper for Chap10 Lemma 10 161 10: the shifted coefficient family obtained by
differentiating the scalar witness and dividing the root powers by one degree. -/
noncomputable def derivativeShiftCoeff
    (b delta0 : R)
    (z : integralClosure R (AdjoinRoot (X ^ p - C (algebraMap R K b))))
    (k : Fin p) : K :=
  if h : (k : ℕ) + 1 < p then
    ((k : ℕ) + 1 : K) * algebraMap R K delta0 *
      adjoinRoot_pth_root_coord (R := R) (K := K) (p := p) b (z : _) ⟨(k : ℕ) + 1, h⟩
  else 0

omit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsFractionRing R K]
  [CharP K p] in
/-- Helper for Chap10 Lemma 10 161 10: below the final index, the shifted coefficient is the
successor-index derivative coefficient. -/
lemma derivativeShiftCoeff_of_lt
    (b delta0 : R)
    (z : integralClosure R (AdjoinRoot (X ^ p - C (algebraMap R K b))))
    (k : Fin p)
    (h : (k : ℕ) + 1 < p) :
    derivativeShiftCoeff (R := R) (K := K) (p := p) b delta0 z k =
      ((k : ℕ) + 1 : K) * algebraMap R K delta0 *
        adjoinRoot_pth_root_coord (R := R) (K := K) (p := p) b (z : _) ⟨(k : ℕ) + 1, h⟩ := by
  -- Unfold only the named coefficient family and select the successor branch.
  simp [derivativeShiftCoeff, h]

omit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsFractionRing R K]
  [CharP K p] in
/-- Helper for Chap10 Lemma 10 161 10: at the final index, or beyond the successor range, the
shifted derivative coefficient is zero. -/
lemma derivativeShiftCoeff_of_not_lt
    (b delta0 : R)
    (z : integralClosure R (AdjoinRoot (X ^ p - C (algebraMap R K b))))
    (k : Fin p)
    (h : ¬ (k : ℕ) + 1 < p) :
    derivativeShiftCoeff (R := R) (K := K) (p := p) b delta0 z k = 0 := by
  -- The definition was chosen with an `if` branch precisely to avoid exposing Fin transports.
  simp [derivativeShiftCoeff, h]

omit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsFractionRing R K] in
/-- Helper for Chap10 Lemma 10 161 10: finite sums of fraction-field scalars that each come
from `R` again come from `R`. -/
lemma exists_mem_range_finset_sum
    {ι : Type*} (s : Finset ι) (f : ι → K)
    (h : ∀ j ∈ s, ∃ r : R, algebraMap R K r = f j) :
    ∃ r : R, algebraMap R K r = ∑ j ∈ s, f j := by
  classical
  -- Induct over the finite set, adding the chosen `R`-witnesses term by term.
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨0, by simp⟩
  | insert a s ha ih =>
      have hamem : a ∈ insert a s := Finset.mem_insert_self a s
      obtain ⟨ra, hra⟩ := h a hamem
      have htail : ∀ j ∈ s, ∃ r : R, algebraMap R K r = f j := by
        intro j hj
        have hmem : j ∈ insert a s := Finset.mem_insert_of_mem hj
        exact h j hmem
      obtain ⟨rs, hrs⟩ := ih htail
      refine ⟨ra + rs, ?_⟩
      -- Mapping the sum of witnesses gives the inserted finite sum.
      rw [map_add, hra, hrs, Finset.sum_insert ha]

omit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsFractionRing R K] in
/-- Helper for Chap10 Lemma 10 161 10: the image of `R` in its fraction field is closed under
subtraction. -/
lemma exists_mem_range_sub
    {x y : K}
    (hx : ∃ r : R, algebraMap R K r = x)
    (hy : ∃ r : R, algebraMap R K r = y) :
    ∃ r : R, algebraMap R K r = x - y := by
  rcases hx with ⟨rx, hrx⟩
  rcases hy with ⟨ry, hry⟩
  refine ⟨rx - ry, ?_⟩
  -- Subtract the two `R`-witnesses before applying the algebra map.
  simp [map_sub, hrx, hry]

omit [IsDomain R] [IsNoetherianRing R] [CharP K p] in
/-- Helper for Chap10 Lemma 10 161 10: if a `p`th power lies in the image of `R`, then the
element itself lies in the image of `R`. -/
lemma exists_mem_range_of_pow
    (x : K)
    (hx : ∃ r : R, algebraMap R K r = x ^ p) :
    ∃ r : R, algebraMap R K r = x := by
  rcases hx with ⟨r, hr⟩
  have hxIntegral : IsIntegral R x := by
    -- A monic equation for `x` is obtained from the descended `p`th power.
    refine IsIntegral.of_pow (show 0 < p by exact (Fact.out : Nat.Prime p).pos) ?_
    rw [← hr]
    exact isIntegral_algebraMap
  obtain ⟨s, hs⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hxIntegral
  exact ⟨s, by simpa using hs⟩

/-- Chap10 Lemma 10 161 10: once the coefficient lies in `R`, the source-proof induction clears the
power-basis coefficients using the nonzero derivative. -/
lemma integralClosure_finite_adjoinRoot_pth_root_of_mem_range_of_exists_derivation
    (b : R)
    (D : Derivation ℤ K K)
    (hMaps : Set.MapsTo D (Set.range (algebraMap R K)) (Set.range (algebraMap R K)))
    (hDb : D (algebraMap R K b) ≠ 0) :
    Module.Finite R (integralClosure R (AdjoinRoot (X ^ p - C (algebraMap R K b)))) := by
  let hIrred : Irreducible (X ^ p - C (algebraMap R K b)) :=
    irreducible_X_pow_sub_C_of_exists_derivation (R := R) (p := p) (algebraMap R K b)
      ⟨D, hMaps, hDb⟩
  letI : Fact (Irreducible (X ^ p - C (algebraMap R K b))) := Fact.mk hIrred
  letI : Field (AdjoinRoot (X ^ p - C (algebraMap R K b))) := AdjoinRoot.instField
  obtain ⟨delta0, hdelta⟩ :=
    exists_derivation_image_eq (R := R) (K := K) b D hMaps
  have hdelta0 : delta0 ≠ 0 :=
    derivation_image_ne_zero (R := R) (K := K) b D hdelta hDb
  let x : AdjoinRoot (X ^ p - C (algebraMap R K b)) :=
    AdjoinRoot.root (X ^ p - C (algebraMap R K b))
  let coord :
      AdjoinRoot (X ^ p - C (algebraMap R K b)) → Fin p → K :=
    adjoinRoot_pth_root_coord (R := R) (K := K) (p := p) b
  have hxIntegral : IsIntegral R x := by
    -- The source proof uses that the adjoined root is integral once the coefficient lies in `R`.
    simpa [x] using adjoinRoot_root_isIntegral_of_mem_range (R := R) (K := K) (p := p) b
  have hsum_repr :
      ∀ y : AdjoinRoot (X ^ p - C (algebraMap R K b)),
        ∑ j : Fin p, coord y j • x ^ (j : ℕ) = y := by
    -- Fix the `Fin p` coordinates once so the remaining induction can work with explicit sums.
    intro y
    simpa [coord, x] using
      adjoinRoot_pth_root_sum_repr (R := R) (K := K) (p := p) b y
  let scaledRootPowers :
      Set (AdjoinRoot (X ^ p - C (algebraMap R K b))) :=
    Set.range fun j : Fin p ↦
      algebraMap K (AdjoinRoot (X ^ p - C (algebraMap R K b)))
          (((algebraMap R K delta0 : K) ^ (p - 1))⁻¹) * x ^ (j : ℕ)
  have hcontain :
      Subalgebra.toSubmodule
          (integralClosure R (AdjoinRoot (X ^ p - C (algebraMap R K b)))) ≤
        Submodule.span R scaledRootPowers := by
    intro y hy
    have clear_trunc :
        ∀ i : ℕ, i ≤ p - 1 →
          ∀ z : integralClosure R (AdjoinRoot (X ^ p - C (algebraMap R K b))),
            (∀ j : Fin p, i < j.1 → coord (z : _) j = 0) →
            ∀ j : Fin p, j.1 ≤ i →
              ∃ r : R,
                algebraMap R K r =
                  (algebraMap R K delta0 : K) ^ i * coord (z : _) j := by
      intro i hi
      induction i with
      | zero =>
          intro z hz j hj
          have hj0 : j = 0 := Fin.ext (Nat.eq_zero_of_le_zero hj)
          subst hj0
          have hscalar :
              (z : AdjoinRoot (X ^ p - C (algebraMap R K b))) =
                algebraMap K (AdjoinRoot (X ^ p - C (algebraMap R K b)))
                  (coord (z : AdjoinRoot (X ^ p - C (algebraMap R K b))) 0) := by
            -- The truncation hypothesis kills every positive root-power coefficient, so only the
            -- constant scalar term remains in the fixed basis expansion.
            calc
              (z : AdjoinRoot (X ^ p - C (algebraMap R K b))) =
                  ∑ j : Fin p,
                    coord (z : AdjoinRoot (X ^ p - C (algebraMap R K b))) j •
                      x ^ (j : ℕ) := by
                        symm
                        exact hsum_repr (z : AdjoinRoot (X ^ p - C (algebraMap R K b)))
              _ =
                  coord (z : AdjoinRoot (X ^ p - C (algebraMap R K b))) 0 • x ^ (0 : ℕ) := by
                    refine Finset.sum_eq_single 0 ?_ ?_
                    · intro j _ hj0
                      have hjpos : 0 < j.1 := Nat.pos_of_ne_zero fun hzero ↦
                        hj0 (Fin.ext hzero)
                      simp [hz j hjpos]
                    · intro hzero
                      simp at hzero
              _ =
                  algebraMap K (AdjoinRoot (X ^ p - C (algebraMap R K b)))
                    (coord (z : AdjoinRoot (X ^ p - C (algebraMap R K b))) 0) := by
                      simp [Algebra.smul_def]
          have hcoord_integral :
              IsIntegral R
                (coord (z : AdjoinRoot (X ^ p - C (algebraMap R K b))) 0) := by
            -- Rewriting the integral element as a scalar in the fraction field lets us descend
            -- that scalar back to `R` because `R` is integrally closed in `K`.
            rw [← isIntegral_algebraMap_iff (algebraMap K
              (AdjoinRoot (X ^ p - C (algebraMap R K b)))).injective, ← hscalar]
            exact z.2
          obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hcoord_integral
          exact ⟨r, by simpa using hr⟩
      | succ i ih =>
          intro z hz j hj
          let delta : K := algebraMap R K delta0
          have hp_eq : (p - 1) + 1 = p := Nat.succ_pred_eq_of_pos (Fact.out : Nat.Prime p).pos
          have hp_pred_lt : p - 1 < p := Nat.pred_lt (Fact.out : Nat.Prime p).ne_zero
          have hp_succ : p = Nat.succ (p - 1) := by
            simpa [Nat.succ_eq_add_one] using hp_eq.symm
          have hi_prev : i ≤ p - 1 := Nat.le_trans (Nat.le_succ i) hi
          let derivTerm : ℕ → K := fun k ↦
            if hk : k < p then
              coord (z : AdjoinRoot (X ^ p - C (algebraMap R K b))) ⟨k, hk⟩ ^ p *
                ((k : K) * (algebraMap R K b) ^ (k - 1) * delta)
            else 0
          obtain ⟨r0, hr0⟩ :=
            scalarWitness_of_integralPowerBasisExpansion (R := R) (K := K) (p := p) b z
          obtain ⟨r1, hr1⟩ := hMaps ⟨r0, rfl⟩
          have hderivFin :
              algebraMap R K r1 = ∑ j : Fin p,
                coord (z : AdjoinRoot (X ^ p - C (algebraMap R K b))) j ^ p *
                  ((j : K) * (algebraMap R K b) ^ ((j : ℕ) - 1) * delta) := by
            -- Differentiate the descended scalar witness termwise before changing normal form.
            calc
              algebraMap R K r1 = D (algebraMap R K r0) := hr1
              _ = D (∑ j : Fin p,
                  coord (z : AdjoinRoot (X ^ p - C (algebraMap R K b))) j ^ p *
                    (algebraMap R K b) ^ (j : ℕ)) := by
                    rw [hr0]
              _ = ∑ j : Fin p,
                  D (coord (z : AdjoinRoot (X ^ p - C (algebraMap R K b))) j ^ p *
                    (algebraMap R K b) ^ (j : ℕ)) := by
                    rw [map_sum]
              _ = ∑ j : Fin p,
                  coord (z : AdjoinRoot (X ^ p - C (algebraMap R K b))) j ^ p *
                    ((j : K) * (algebraMap R K b) ^ ((j : ℕ) - 1) * delta) := by
                      refine Finset.sum_congr rfl ?_
                      intro j hj
                      simpa using
                        derivative_powerBasisScalarTerm
                          (R := R) (K := K) (p := p) b D hdelta z j
          have hderivRange :
              algebraMap R K r1 = Finset.sum (Finset.range p) derivTerm := by
            -- Keep the differentiated witness explicit; the only later reindexing is the
            -- one-step successor shift that produces the lowered coefficients.
            calc
              algebraMap R K r1 = ∑ j : Fin p,
                  coord (z : AdjoinRoot (X ^ p - C (algebraMap R K b))) j ^ p *
                    ((j : K) * (algebraMap R K b) ^ ((j : ℕ) - 1) * delta) := hderivFin
              _ = Finset.sum (Finset.range p) derivTerm := by
                    simpa [derivTerm] using (Fin.sum_univ_eq_sum_range derivTerm p)
          let shifted : Fin p → K :=
            derivativeShiftCoeff (R := R) (K := K) (p := p) b delta0 z
          have hshiftWitness :
              ∃ r : R,
                algebraMap R K r =
                  ∑ k : Fin p, shifted k ^ p * (algebraMap R K b) ^ (k : ℕ) := by
            refine ⟨delta0 ^ (p - 1) * r1, ?_⟩
            let shiftRangeTerm : ℕ → K := fun k ↦
              if hk : k < p then
                shifted ⟨k, hk⟩ ^ p * (algebraMap R K b) ^ k
              else 0
            have hderiv_zero : derivTerm 0 = 0 := by
              -- The zeroth differentiated term contains the scalar factor `0`.
              simp [derivTerm]
            have hfinal_shift :
                shifted ⟨p - 1, hp_pred_lt⟩ = 0 := by
              have hnot : ¬ (p - 1) + 1 < p := by
                omega
              simpa [shifted] using
                derivativeShiftCoeff_of_not_lt (R := R) (K := K) (p := p)
                  b delta0 z ⟨p - 1, hp_pred_lt⟩ hnot
            have hfinal_term : shiftRangeTerm (p - 1) = 0 := by
              -- The final shifted coefficient is the explicit zero branch.
              have hp_ne : p ≠ 0 := (Fact.out : Nat.Prime p).ne_zero
              simp [shiftRangeTerm, hp_pred_lt, hfinal_shift, hp_ne]
            have hleft :
                (∑ k : Fin p, shifted k ^ p * (algebraMap R K b) ^ (k : ℕ)) =
                  Finset.sum (Finset.range (p - 1)) shiftRangeTerm := by
              -- Rewrite the `Fin p` sum as a natural range and drop the final zero term.
              calc
                (∑ k : Fin p, shifted k ^ p * (algebraMap R K b) ^ (k : ℕ)) =
                    Finset.sum (Finset.range p) shiftRangeTerm := by
                      simpa [shiftRangeTerm] using
                        (Fin.sum_univ_eq_sum_range shiftRangeTerm p)
                _ = Finset.sum (Finset.range ((p - 1) + 1)) shiftRangeTerm := by
                      rw [hp_eq]
                _ = Finset.sum (Finset.range (p - 1)) shiftRangeTerm +
                    shiftRangeTerm (p - 1) := by
                      rw [Finset.sum_range_succ]
                _ = Finset.sum (Finset.range (p - 1)) shiftRangeTerm := by
                      rw [hfinal_term, add_zero]
            have hpoint :
                ∀ k ∈ Finset.range (p - 1),
                  shiftRangeTerm k = (algebraMap R K delta0 : K) ^ (p - 1) *
                    derivTerm (k + 1) := by
              intro k hk
              have hk_pred : k < p - 1 := Finset.mem_range.mp hk
              have hk_lt : k < p := by
                omega
              have hsucc : k + 1 < p := by
                omega
              have hnatpow : ((k : K) + 1) ^ p = (k : K) + 1 := by
                simpa [Nat.cast_add, Nat.cast_one] using
                  natCast_pow_char (K := K) (p := p) (k + 1)
              have hdelta_pow :
                  (algebraMap R K delta0 : K) ^ p =
                    (algebraMap R K delta0 : K) ^ (p - 1) *
                      algebraMap R K delta0 := by
                calc
                  (algebraMap R K delta0 : K) ^ p =
                      (algebraMap R K delta0 : K) ^ ((p - 1) + 1) := by
                        rw [hp_eq]
                  _ = (algebraMap R K delta0 : K) ^ (p - 1) *
                      algebraMap R K delta0 := by
                        rw [pow_succ]
              -- On each non-final index, Frobenius turns the successor scalar into itself and
              -- leaves exactly the differentiated successor term times `delta^(p-1)`.
              have hnormalized :
                  ((k : K) + 1) ^ p * (algebraMap R K delta0 : K) ^ p *
                      coord (z : AdjoinRoot (X ^ p - C (algebraMap R K b)))
                        ⟨k + 1, hsucc⟩ ^ p *
                        (algebraMap R K b) ^ k =
                    (algebraMap R K delta0 : K) ^ (p - 1) *
                      (coord (z : AdjoinRoot (X ^ p - C (algebraMap R K b)))
                          ⟨k + 1, hsucc⟩ ^ p *
                        (((k + 1 : ℕ) : K) * (algebraMap R K b) ^ (k + 1 - 1) *
                          algebraMap R K delta0)) := by
                rw [hnatpow, hdelta_pow]
                have hk_sub : k + 1 - 1 = k := by
                  omega
                rw [hk_sub]
                rw [Nat.cast_add, Nat.cast_one]
                ring_nf
              simpa [shiftRangeTerm, derivTerm, hk_lt, hsucc, shifted,
                derivativeShiftCoeff_of_lt, mul_pow, delta, coord, Nat.cast_add, Nat.cast_one]
                using hnormalized
            have hright :
                (algebraMap R K delta0 : K) ^ (p - 1) *
                    Finset.sum (Finset.range p) derivTerm =
                  Finset.sum (Finset.range (p - 1))
                    (fun k ↦ (algebraMap R K delta0 : K) ^ (p - 1) *
                      derivTerm (k + 1)) := by
              -- The derivative range sum has zero constant term, so it is the shifted successor
              -- range after pulling out the fixed scalar.
              calc
                (algebraMap R K delta0 : K) ^ (p - 1) *
                    Finset.sum (Finset.range p) derivTerm =
                    (algebraMap R K delta0 : K) ^ (p - 1) *
                      Finset.sum (Finset.range ((p - 1) + 1)) derivTerm := by
                        rw [hp_eq]
                _ = (algebraMap R K delta0 : K) ^ (p - 1) *
                    (Finset.sum (Finset.range (p - 1)) (fun k ↦ derivTerm (k + 1)) +
                      derivTerm 0) := by
                      rw [Finset.sum_range_succ']
                _ = (algebraMap R K delta0 : K) ^ (p - 1) *
                    Finset.sum (Finset.range (p - 1)) (fun k ↦ derivTerm (k + 1)) := by
                      rw [hderiv_zero, add_zero]
                _ = Finset.sum (Finset.range (p - 1))
                    (fun k ↦ (algebraMap R K delta0 : K) ^ (p - 1) *
                      derivTerm (k + 1)) := by
                      rw [Finset.mul_sum]
            have hshift_sum :
                (∑ k : Fin p, shifted k ^ p * (algebraMap R K b) ^ (k : ℕ)) =
                  (algebraMap R K delta0 : K) ^ (p - 1) *
                    Finset.sum (Finset.range p) derivTerm := by
              -- Combine the two range normal forms.
              calc
                (∑ k : Fin p, shifted k ^ p * (algebraMap R K b) ^ (k : ℕ)) =
                    Finset.sum (Finset.range (p - 1)) shiftRangeTerm := hleft
                _ = Finset.sum (Finset.range (p - 1))
                    (fun k ↦ (algebraMap R K delta0 : K) ^ (p - 1) *
                      derivTerm (k + 1)) := by
                      exact Finset.sum_congr rfl hpoint
                _ = (algebraMap R K delta0 : K) ^ (p - 1) *
                    Finset.sum (Finset.range p) derivTerm := hright.symm
            -- Map the explicit witness `delta0^(p-1) * r1` and use the descended derivative sum.
            calc
              algebraMap R K (delta0 ^ (p - 1) * r1) =
                  (algebraMap R K delta0 : K) ^ (p - 1) * algebraMap R K r1 := by
                    simp [map_mul, map_pow]
              _ = (algebraMap R K delta0 : K) ^ (p - 1) *
                    Finset.sum (Finset.range p) derivTerm := by
                    rw [hderivRange]
              _ = ∑ k : Fin p, shifted k ^ p * (algebraMap R K b) ^ (k : ℕ) :=
                    hshift_sum.symm
          let lowered : AdjoinRoot (X ^ p - C (algebraMap R K b)) :=
            ∑ k : Fin p, shifted k • x ^ (k : ℕ)
          have hloweredIntegral : IsIntegral R lowered := by
            -- The shifted scalar witness makes the explicit shifted root-power sum integral.
            simpa [lowered, shifted, x] using
              loweredIsIntegral_of_scalarWitness (R := R) (K := K) (p := p) b shifted
                hshiftWitness
          let w : integralClosure R (AdjoinRoot (X ^ p - C (algebraMap R K b))) :=
            ⟨lowered, hloweredIntegral⟩
          have hcoordLowered :
              ∀ k : Fin p, coord (w : AdjoinRoot (X ^ p - C (algebraMap R K b))) k =
                shifted k := by
            -- The shifted element was defined as an explicit fixed-basis expansion.
            intro k
            simpa [w, lowered, shifted, coord, x] using
              adjoinRoot_pth_root_coord_sum (R := R) (K := K) (p := p) b shifted k
          have htailLowered :
              ∀ k : Fin p, i < k.1 →
                coord (w : AdjoinRoot (X ^ p - C (algebraMap R K b))) k = 0 := by
            -- Above degree `i`, the shifted coefficient either points to a killed original
            -- coefficient or is the explicit zero final branch.
            intro k hk
            rw [hcoordLowered k]
            by_cases hsucc : (k : ℕ) + 1 < p
            · have hkill :
                  i + 1 < (⟨(k : ℕ) + 1, hsucc⟩ : Fin p).1 := by
                simpa using Nat.succ_lt_succ hk
              calc
                shifted k =
                    ((k : ℕ) + 1 : K) * algebraMap R K delta0 *
                      coord (z : AdjoinRoot (X ^ p - C (algebraMap R K b)))
                        ⟨(k : ℕ) + 1, hsucc⟩ := by
                      simpa [shifted, coord] using
                        derivativeShiftCoeff_of_lt (R := R) (K := K) (p := p) b delta0 z k hsucc
                _ = 0 := by
                      simp [hz ⟨(k : ℕ) + 1, hsucc⟩ hkill]
            · simpa [shifted] using
                derivativeShiftCoeff_of_not_lt (R := R) (K := K) (p := p) b delta0 z k hsucc
          have hpositive :
              ∀ j : Fin p, 0 < j.1 → j.1 ≤ i + 1 →
                ∃ r : R,
                  algebraMap R K r =
                    (algebraMap R K delta0 : K) ^ (i + 1) *
                      coord (z : AdjoinRoot (X ^ p - C (algebraMap R K b))) j := by
            intro j hjpos hjle
            have hk_lt : j.1 - 1 < p := Nat.lt_of_le_of_lt (Nat.sub_le _ _) j.2
            let k : Fin p := ⟨j.1 - 1, hk_lt⟩
            have hk_le : k.1 ≤ i := by
              dsimp [k]
              omega
            obtain ⟨s, hs⟩ := ih hi_prev w htailLowered k hk_le
            have hsucc : (k : ℕ) + 1 < p := by
              dsimp [k]
              omega
            have hnat : (j.1 - 1) + 1 = j.1 :=
              Nat.sub_add_cancel (Nat.succ_le_of_lt hjpos)
            have hk_nat : (k : ℕ) + 1 = j.1 := by
              simpa [k] using hnat
            have hk_cast : ((k : K) + 1) = (j.1 : K) := by
              rw [← Nat.cast_one, ← Nat.cast_add, hk_nat]
            have hfin : (⟨(k : ℕ) + 1, hsucc⟩ : Fin p) = j := by
              apply Fin.ext
              exact hk_nat
            have hshift_eval :
                shifted k =
                  (j.1 : K) * (algebraMap R K delta0 : K) *
                    coord (z : AdjoinRoot (X ^ p - C (algebraMap R K b))) j := by
              calc
                shifted k =
                    ((k : ℕ) + 1 : K) * algebraMap R K delta0 *
                      coord (z : AdjoinRoot (X ^ p - C (algebraMap R K b)))
                        ⟨(k : ℕ) + 1, hsucc⟩ := by
                      simpa [shifted, coord] using
                        derivativeShiftCoeff_of_lt (R := R) (K := K) (p := p) b delta0 z k hsucc
                _ =
                    (j.1 : K) * (algebraMap R K delta0 : K) *
                      coord (z : AdjoinRoot (X ^ p - C (algebraMap R K b))) j := by
                      rw [hfin]
                      rw [hk_cast]
            have hunit : IsUnit ((j.1 : ℕ) : R) :=
              natCastIsUnit_of_pos_lt_prime (R := R) (K := K) (p := p) hjpos j.2
            have hunitMul :
                ∃ r : R,
                  algebraMap R K r =
                    algebraMap R K ((j.1 : ℕ) : R) *
                      ((algebraMap R K delta0 : K) ^ (i + 1) *
                        coord (z : AdjoinRoot (X ^ p - C (algebraMap R K b))) j) := by
              refine ⟨s, ?_⟩
              calc
                algebraMap R K s =
                    (algebraMap R K delta0 : K) ^ i * coord (w : _) k := hs
                _ = (algebraMap R K delta0 : K) ^ i * shifted k := by
                      rw [hcoordLowered k]
                _ =
                    algebraMap R K ((j.1 : ℕ) : R) *
                      ((algebraMap R K delta0 : K) ^ (i + 1) *
                        coord (z : AdjoinRoot (X ^ p - C (algebraMap R K b))) j) := by
                      rw [hshift_eval]
                      simp [pow_succ, mul_assoc, mul_comm, mul_left_comm]
            exact exists_mem_range_of_unit_mul (R := R) (K := K)
              (u := ((j.1 : ℕ) : R)) hunit hunitMul
          have hconstant :
              ∃ r : R,
                algebraMap R K r =
                  (algebraMap R K delta0 : K) ^ (i + 1) *
                    coord (z : AdjoinRoot (X ^ p - C (algebraMap R K b))) 0 := by
            let scaledTerm : Fin p → K := fun j ↦
              ((algebraMap R K delta0 : K) ^ (i + 1) *
                  coord (z : AdjoinRoot (X ^ p - C (algebraMap R K b))) j) ^ p *
                (algebraMap R K b) ^ (j : ℕ)
            have hr0coord :
                algebraMap R K r0 =
                  ∑ j : Fin p,
                    coord (z : AdjoinRoot (X ^ p - C (algebraMap R K b))) j ^ p *
                      (algebraMap R K b) ^ (j : ℕ) := by
              simpa [coord] using hr0
            have hscaledScalar :
                ∃ r : R, algebraMap R K r = ∑ j : Fin p, scaledTerm j := by
              refine ⟨delta0 ^ (p * (i + 1)) * r0, ?_⟩
              -- Scale the original scalar witness by `delta0^(p*(i+1))`.
              calc
                algebraMap R K (delta0 ^ (p * (i + 1)) * r0) =
                    (algebraMap R K delta0 : K) ^ (p * (i + 1)) *
                      algebraMap R K r0 := by
                      simp [map_mul, map_pow]
                _ = (algebraMap R K delta0 : K) ^ (p * (i + 1)) *
                    ∑ j : Fin p,
                      coord (z : AdjoinRoot (X ^ p - C (algebraMap R K b))) j ^ p *
                        (algebraMap R K b) ^ (j : ℕ) := by
                      rw [hr0coord]
                _ = ∑ j : Fin p, scaledTerm j := by
                      rw [Finset.mul_sum]
                      refine Finset.sum_congr rfl ?_
                      intro j hj
                      have hpow_exp :
                          (algebraMap R K delta0 : K) ^ (p * (i + 1)) =
                            ((algebraMap R K delta0 : K) ^ (i + 1)) ^ p := by
                        calc
                          (algebraMap R K delta0 : K) ^ (p * (i + 1)) =
                              (algebraMap R K delta0 : K) ^ ((i + 1) * p) := by
                                rw [Nat.mul_comm]
                          _ = ((algebraMap R K delta0 : K) ^ (i + 1)) ^ p := by
                                rw [pow_mul]
                      calc
                        (algebraMap R K delta0 : K) ^ (p * (i + 1)) *
                            (coord (z : AdjoinRoot (X ^ p - C (algebraMap R K b))) j ^ p *
                              (algebraMap R K b) ^ (j : ℕ)) =
                            ((algebraMap R K delta0 : K) ^ (i + 1)) ^ p *
                              (coord (z : AdjoinRoot (X ^ p - C (algebraMap R K b))) j ^ p *
                                (algebraMap R K b) ^ (j : ℕ)) := by
                              rw [hpow_exp]
                        _ = scaledTerm j := by
                              simp [scaledTerm, mul_pow, mul_assoc, mul_comm, mul_left_comm]
            have hpositiveTerm :
                ∀ j ∈ Finset.univ.erase (0 : Fin p),
                  ∃ r : R, algebraMap R K r = scaledTerm j := by
              intro j hjmem
              have hjne : j ≠ 0 := (Finset.mem_erase.mp hjmem).1
              by_cases hjle : j.1 ≤ i + 1
              · have hjpos : 0 < j.1 := Nat.pos_of_ne_zero fun hzero ↦
                  hjne (Fin.ext hzero)
                obtain ⟨rj, hrj⟩ := hpositive j hjpos hjle
                refine ⟨rj ^ p * b ^ (j : ℕ), ?_⟩
                -- Positive coefficients up to degree `i+1` already have descended witnesses.
                calc
                  algebraMap R K (rj ^ p * b ^ (j : ℕ)) =
                      (algebraMap R K rj : K) ^ p *
                        (algebraMap R K b) ^ (j : ℕ) := by
                        simp [map_mul, map_pow]
                  _ = scaledTerm j := by
                        rw [hrj]
              · have hjgt : i + 1 < j.1 := by
                  omega
                have hzero : coord (z : AdjoinRoot (X ^ p - C (algebraMap R K b))) j = 0 :=
                  hz j hjgt
                refine ⟨0, ?_⟩
                -- Coefficients above the current truncation degree vanish, so their terms are zero.
                have hp_ne : p ≠ 0 := (Fact.out : Nat.Prime p).ne_zero
                simp [scaledTerm, hzero, hp_ne]
            obtain ⟨rpos, hrpos⟩ :=
              exists_mem_range_finset_sum (R := R) (K := K)
                (s := Finset.univ.erase (0 : Fin p)) scaledTerm hpositiveTerm
            have hpositiveSum :
                ∃ r : R,
                  algebraMap R K r =
                    ∑ j ∈ Finset.univ.erase (0 : Fin p), scaledTerm j := ⟨rpos, hrpos⟩
            have hconstantPow :
                ∃ r : R,
                  algebraMap R K r =
                    ((algebraMap R K delta0 : K) ^ (i + 1) *
                      coord (z : AdjoinRoot (X ^ p - C (algebraMap R K b))) 0) ^ p := by
              obtain ⟨rpow, hrpow⟩ :=
                exists_mem_range_sub (R := R) (K := K) hscaledScalar hpositiveSum
              refine ⟨rpow, ?_⟩
              have hdiff :
                  (∑ j : Fin p, scaledTerm j) -
                      (∑ j ∈ Finset.univ.erase (0 : Fin p), scaledTerm j) =
                    ((algebraMap R K delta0 : K) ^ (i + 1) *
                      coord (z : AdjoinRoot (X ^ p - C (algebraMap R K b))) 0) ^ p := by
                -- Splitting the full sum into the zero term and the erased positive-index sum
                -- leaves only the constant coefficient's `p`th power.
                have hsplit :
                    (∑ j : Fin p, scaledTerm j) =
                      scaledTerm 0 +
                        ∑ j ∈ Finset.univ.erase (0 : Fin p), scaledTerm j :=
                  (Finset.add_sum_erase Finset.univ scaledTerm (Finset.mem_univ 0)).symm
                rw [hsplit]
                simp [scaledTerm]
              calc
                algebraMap R K rpow =
                    (∑ j : Fin p, scaledTerm j) -
                      (∑ j ∈ Finset.univ.erase (0 : Fin p), scaledTerm j) := hrpow
                _ = ((algebraMap R K delta0 : K) ^ (i + 1) *
                      coord (z : AdjoinRoot (X ^ p - C (algebraMap R K b))) 0) ^ p := hdiff
            -- A descended `p`th power descends the constant coefficient itself.
            exact exists_mem_range_of_pow (R := R) (K := K) (p := p)
              ((algebraMap R K delta0 : K) ^ (i + 1) *
                coord (z : AdjoinRoot (X ^ p - C (algebraMap R K b))) 0)
              hconstantPow
          by_cases hjzero : (j : ℕ) = 0
          · have hjFin : j = 0 := Fin.ext hjzero
            simpa [hjFin] using hconstant
          · exact hpositive j (Nat.pos_of_ne_zero hjzero) hj
    -- Route correction: the remaining open step is now isolated to the source-proof induction
    -- that clears the fixed `Fin p` coordinates of the integral element `y`.
    have hcoeff :
        ∀ j : Fin p, ∃ r : R,
          algebraMap R K r =
            (algebraMap R K delta0 : K) ^ (p - 1) * coord (y : _) j := by
      -- Apply the source invariant at the full truncation degree `p - 1`; the upper-tail
      -- vanishing hypothesis is vacuous because `Fin p` has no indices above `p - 1`.
      intro j
      exact clear_trunc (p - 1) le_rfl ⟨y, hy⟩
        (fun j hj ↦ False.elim <| Nat.not_lt_of_ge (Nat.le_pred_of_lt j.2) hj)
        j (Nat.le_pred_of_lt j.2)
    -- Once the coefficients are cleared, the source proof ends by rewriting `y` in the fixed
    -- power basis and observing that each summand is an `R`-multiple of a rescaled root power.
    simpa [scaledRootPowers, coord, x] using
      mem_span_scaled_root_powers_of_cleared_coordinates
        (R := R) (K := K) (p := p) b delta0 hdelta0 (y : _)
        hcoeff
  -- Route correction: the remaining work is the reduced-case coefficient-clearing induction from
  -- the source proof, after extracting `δ = D(b)` in the image of `R`. The endgame is now
  -- isolated in `hcontain`, which is the finite-span trap from the textbook proof.
  exact integralClosure_finite_of_le_span (R := R) (hs := Set.finite_range _) hcontain

/-
Domain-style sampling:
* primary domain: commutative algebra of finite normalization in purely inseparable degree-`p`
  extensions of a fraction field, with the auxiliary input of an absolute derivation detecting that
  the adjoined element is not a `p`th power;
* sampled owner-style declarations:
  - `IsN2Ring.integralClosure_finite`, the chapter owner field for finite normalization in finite
    fraction-field extensions;
  - `Derivation ℤ K K`, the canonical absolute-derivation owner from Chapter `10.131`;
  - `integralClosure`, the normalization owner from Chapter `10.36`;
  - `Polynomial.Monic.finite_adjoinRoot`, the canonical finite `K`-algebra API for
    `AdjoinRoot (X ^ p - C a)`;
  - `X_pow_sub_C_irreducible_of_prime`, the standard bridge for the degree-`p` purely inseparable
    step when `a` is not a `p`th power.
* layer triage:
  - `source-facing`: the finiteness theorem for the normalization in the single-root extension
    `AdjoinRoot (X ^ p - C a)`;
  - `core/canonical`: `Derivation ℤ K K` for the absolute derivation,
    `AdjoinRoot (X ^ p - C a)` for the degree-`p` purely inseparable step,
    `integralClosure` for the normalization owner, and `Module.Finite` for the finiteness
    conclusion;
  - `bridge/view`: the canonical irreducibility theorem `X_pow_sub_C_irreducible_of_prime`,
    together with the derived `AdjoinRoot` field and finite `K`-algebra API
    `AdjoinRoot.instField` and `Polynomial.Monic.finite_adjoinRoot`.
* owner decision: this file stays `source-facing`. The textbook item is not introducing a new owner
  abstraction beyond the canonical normalization/finiteness owners; it is a criterion for one
  specific purely inseparable step, so no wrapper around `integralClosure` or `AdjoinRoot` should
  be added here.
* primitive data: `R`, its fraction field `K`, the prime characteristic `p`, the element `a : K`,
  and the chosen derivation witness.
* derived API: the `AdjoinRoot` algebra structure and its finiteness over `K` are canonical
  consequences of the sampled owner API and should not be promoted to separate public data in this
  file. They are auxiliary to the source-facing normalization statement, not a replacement for it.
-/

/-- Helper for Chap10 Lemma 10 161 10: if `R` is a Noetherian normal domain, `K` is a fraction field
of `R` of characteristic `p > 0`, `a : K`, and there exists an absolute derivation of `K`
preserving the image of `R` and not killing `a`, then the integral closure of `R` in the canonical
quotient `AdjoinRoot (X ^ p - C a) ≅ K[x] / (x^p - a)` is finite over `R`. -/
-- Proof sketch: clear denominators so that `a ∈ R`, then extend the derivation to the fraction
-- field and argue by induction on the degree in the adjoined root. For an integral element
-- `y = a₀ + a₁x + ... + aᵢxᵢ`, differentiating `y ^ p ∈ R` shows that suitable powers of `D a`
-- clear the coefficients `aⱼ`. Hence every integral element lies in a fixed finite `R`-submodule
-- generated by finitely many rescaled powers of `x`, so the integral closure is module-finite.
@[stacks 0AE0]
theorem integralClosure_finite_adjoinRoot_pth_root_of_exists_derivation
    (a : K)
    (hD : ∃ D : Derivation ℤ K K,
      Set.MapsTo D (Set.range (algebraMap R K)) (Set.range (algebraMap R K)) ∧
        D a ≠ 0) :
    Module.Finite R (integralClosure R (AdjoinRoot (X ^ p - C a))) := by
  let hp : Nat.Prime p := Fact.out
  -- The derivation witness first shows that `x ^ p - a` is irreducible, so the adjoined-root
  -- algebra is the degree-`p` field extension used in the source proof.
  have hIrred : Irreducible (X ^ p - C a) :=
    irreducible_X_pow_sub_C_of_exists_derivation (R := R) (p := p) a hD
  letI : Fact (Irreducible (X ^ p - C a)) := Fact.mk hIrred
  letI : Field (AdjoinRoot (X ^ p - C a)) := AdjoinRoot.instField
  have hfiniteK : Module.Finite K (AdjoinRoot (X ^ p - C a)) := by
    exact (monic_X_pow_sub_C a hp.ne_zero).finite_adjoinRoot
  letI : Module.Finite K (AdjoinRoot (X ^ p - C a)) := hfiniteK
  letI : FiniteDimensional K (AdjoinRoot (X ^ p - C a)) := by infer_instance
  -- The source-proof reduction starts by clearing denominators and replacing `a` by `f ^ p * a`,
  -- which lies in the image of `R` while preserving the nonzero derivation value.
  obtain ⟨D, hMaps, hDa⟩ := hD
  obtain ⟨f, b, hf, hb, hDb⟩ := exists_rescaled_mem_range (R := R) (p := p) a D hDa
  have hDb' : D (algebraMap R K b) ≠ 0 :=
    rescaled_derivation_nonzero (R := R) (a := a) (p := p) D hf hb hDa
  have hfiniteReduced :
      Module.Finite R (integralClosure R (AdjoinRoot (X ^ p - C (algebraMap R K b)))) :=
    integralClosure_finite_adjoinRoot_pth_root_of_mem_range_of_exists_derivation
      (R := R) (K := K) (p := p) b D hMaps hDb'
  obtain ⟨e⟩ :=
    adjoinRoot_pth_root_rescale_equiv_of_mem_range (R := R) (K := K) (p := p) a hf hb
  let eR :
      AdjoinRoot (X ^ p - C (algebraMap R K b)) ≃ₐ[R] AdjoinRoot (X ^ p - C a) :=
    e.restrictScalars R
  letI :
      Module.Finite R (integralClosure R (AdjoinRoot (X ^ p - C (algebraMap R K b)))) :=
    hfiniteReduced
  exact Module.Finite.equiv eR.mapIntegralClosure.toLinearEquiv

end
