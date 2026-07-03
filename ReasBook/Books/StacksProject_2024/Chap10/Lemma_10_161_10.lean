import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial

universe u v

section

variable {R : Type u} {K : Type v}
variable [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable {p : ℕ} [Fact p.Prime] [CharP K p]

/-- Helper for Lemma 10.161.10: after writing an element of the fraction field as a quotient
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

/-- Helper for Lemma 10.161.10: a derivation that does not kill `a` rules out `a` being a
`p`th power. -/
lemma pth_power_ne_of_derivation_nonzero
    (D : Derivation ℤ K K) {a : K} (hDa : D a ≠ 0) :
    ∀ b : K, b ^ p ≠ a := by
  intro b hb
  apply hDa
  rw [← hb, Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul K]
  simp

/-- Helper for Lemma 10.161.10: the derivation hypothesis makes `X ^ p - C a` irreducible over
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

/-- Helper for Lemma 10.161.10: after the denominator-clearing step, differentiating the relation
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
            simp [Algebra.smul_def, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
              mul_assoc]
      _ = ((algebraMap R K f) ^ p) * D a := by simp [hpow]
  rw [hderiv]
  exact mul_ne_zero (pow_ne_zero _ hf) hDa

/-- Helper for Lemma 10.161.10: if `b = f ^ p * a` with `f ≠ 0`, then adjoining a `p`th root of
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

/-- Helper for Lemma 10.161.10: the derivation value on an element of `R` again comes from
`R` when the derivation preserves the image of `R`. -/
lemma exists_derivation_image_eq
    (b : R)
    (D : Derivation ℤ K K)
    (hMaps : Set.MapsTo D (Set.range (algebraMap R K)) (Set.range (algebraMap R K))) :
    ∃ delta0 : R, algebraMap R K delta0 = D (algebraMap R K b) := by
  -- Apply the range-preserving hypothesis to the coefficient coming from `b`.
  simpa using hMaps ⟨b, rfl⟩

/-- Helper for Lemma 10.161.10: the coefficient `δ₀ ∈ R` mapping to `D(b)` is nonzero whenever
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

/-- Helper for Lemma 10.161.10: fix the `Fin p`-indexed power basis for the reduced polynomial
`X ^ p - b`. -/
noncomputable def adjoinRoot_pth_root_basis (b : R) :
    Module.Basis (Fin p) K (AdjoinRoot (X ^ p - C (algebraMap R K b))) :=
  (AdjoinRoot.powerBasis' (monic_X_pow_sub_C (algebraMap R K b) (Fact.out : Nat.Prime p).ne_zero)).basis.reindex <|
    finCongr (natDegree_X_pow_sub_C (R := K) (n := p) (r := algebraMap R K b))

/-- Helper for Lemma 10.161.10: the fixed `Fin p` basis vectors are the powers of the adjoined
root. -/
lemma adjoinRoot_pth_root_basis_apply
    (b : R) (j : Fin p) :
    adjoinRoot_pth_root_basis (R := R) (K := K) (p := p) b j =
      AdjoinRoot.root (X ^ p - C (algebraMap R K b)) ^ (j : ℕ) := by
  -- Reindexing the canonical power basis only changes the index type, not the basis vectors.
  rw [adjoinRoot_pth_root_basis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow,
    finCongr_symm_apply, Fin.val_cast]
  simp [AdjoinRoot.powerBasis']

/-- Helper for Lemma 10.161.10: coordinates in the fixed `Fin p` power basis. -/
noncomputable def adjoinRoot_pth_root_coord (b : R) :
    AdjoinRoot (X ^ p - C (algebraMap R K b)) → Fin p → K :=
  fun y j ↦ (adjoinRoot_pth_root_basis (R := R) (K := K) (p := p) b).repr y j

/-- Helper for Lemma 10.161.10: every element of the reduced `AdjoinRoot` algebra reconstructs
from its fixed `Fin p` power-basis coordinates. -/
lemma adjoinRoot_pth_root_sum_repr
    (b : R)
    (y : AdjoinRoot (X ^ p - C (algebraMap R K b))) :
    ∑ j : Fin p, adjoinRoot_pth_root_coord (R := R) (K := K) (p := p) b y j •
        AdjoinRoot.root (X ^ p - C (algebraMap R K b)) ^ (j : ℕ) = y := by
  -- Reconstruct from the basis coordinates, then rewrite the basis vectors as powers of the root.
  simpa [adjoinRoot_pth_root_coord, Algebra.smul_def, adjoinRoot_pth_root_basis_apply] using
    (adjoinRoot_pth_root_basis (R := R) (K := K) (p := p) b).sum_repr y

/-- Helper for Lemma 10.161.10: when the coefficient already lies in `R`, the distinguished root
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

/-- Helper for Lemma 10.161.10: once the integral closure is trapped in the span of a finite
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

/-- Helper for Lemma 10.161.10: once every fixed power-basis coefficient is cleared by the same
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

/-- Helper for Lemma 10.161.10: once the coefficient lies in `R`, the remaining argument is the
source-proof induction that clears the power-basis coefficients using the nonzero derivative. -/
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
          -- TODO: Source-faithful successor step. Build the lowered derivative element
          -- `z' = Σ_j ((j+1) * D(b) * coeff_{j+1}(z)) x^j`, prove `(z')^p` comes from `R` by
          -- differentiating the scalar witness for `z^p ∈ R`, apply `ih` to clear the shifted
          -- coefficients, and then recover the constant term by subtracting the controlled tail.
          sorry
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

/-- Lemma 10.161.10: if `R` is a Noetherian normal domain, `K` is a fraction field of `R` of
characteristic `p > 0`, `a : K`, and there exists an absolute derivation of `K` preserving the
image of `R` and not killing `a`, then the integral closure of `R` in the canonical quotient
`AdjoinRoot (X ^ p - C a) ≅ K[x] / (x^p - a)` is finite over `R`. -/
-- Proof sketch: clear denominators so that `a ∈ R`, then extend the derivation to the fraction
-- field and argue by induction on the degree in the adjoined root. For an integral element
-- `y = a₀ + a₁x + ... + aᵢxᵢ`, differentiating `y ^ p ∈ R` shows that suitable powers of `D a`
-- clear the coefficients `aⱼ`. Hence every integral element lies in a fixed finite `R`-submodule
-- generated by finitely many rescaled powers of `x`, so the integral closure is module-finite.
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
