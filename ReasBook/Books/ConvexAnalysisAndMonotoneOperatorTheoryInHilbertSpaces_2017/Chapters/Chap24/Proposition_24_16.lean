import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap24.Proposition_24_12
import BauschkeLean.Chap24.Proposition_24_14

open scoped InnerProductSpace

noncomputable section

universe u

namespace ERealFunction

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

local notation "ell2" => ℓ²(ℕ, ℝ)

-- Source/core/bridge triage:
-- - `source-facing`: the Hilbert-basis penalty on `H` and its basiswise proximal map
-- - `core/canonical`: `hilbertSum` and `hilbertSumCoordinatewiseProx` on `ell2`
-- - `bridge/view`: transport along the Hilbert-basis coordinate isometry `b.repr`

/-- The separable Hilbert-basis penalty attached to `b` and `φ`, i.e. the
textbook function `x ↦ ∑' k, φₖ (⟪x, bₖ⟫)`, expressed by transporting the
Chapter 24 Hilbert-sum owner along `b.repr`. -/
def hilbertBasisSeparablePenalty
    (b : HilbertBasis ℕ ℝ H) (φ : ℕ → ℝ → Set.Ioi (⊥ : EReal)) :
    H → Set.Ioi (⊥ : EReal) :=
  fun x ↦ hilbertSum φ (b.repr x)

/-- Evaluating `hilbertBasisSeparablePenalty b φ` is the same as evaluating `hilbertSum φ` on the
Hilbert-basis coordinates of `x`. -/
@[simp] theorem hilbertBasisSeparablePenalty_apply
    (b : HilbertBasis ℕ ℝ H) (φ : ℕ → ℝ → Set.Ioi (⊥ : EReal)) (x : H) :
    hilbertBasisSeparablePenalty b φ x = hilbertSum φ (b.repr x) :=
  rfl

/-- The source-facing coordinatewise proximal map on `H`, obtained by transporting the Chapter 24
`ell2` coordinatewise proximal map back along `b.repr.symm`. -/
def hilbertBasisSeparablePenaltyCoordinatewiseProx
    (b : HilbertBasis ℕ ℝ H) (φ : ℕ → ℝ → Set.Ioi (⊥ : EReal))
    (hφ : ∀ k, φ k ∈ Γ₀(ℝ)) :
    H → H :=
  fun x ↦ b.repr.symm (hilbertSumCoordinatewiseProx φ hφ (b.repr x))

/-- In Hilbert-basis coordinates, the transported coordinatewise proximal map is exactly the
Chapter 24 `ell2` coordinatewise proximal vector. -/
@[simp] theorem repr_hilbertBasisSeparablePenaltyCoordinatewiseProx
    (b : HilbertBasis ℕ ℝ H) (φ : ℕ → ℝ → Set.Ioi (⊥ : EReal))
    (hφ : ∀ k, φ k ∈ Γ₀(ℝ)) (x : H) :
    b.repr (hilbertBasisSeparablePenaltyCoordinatewiseProx b φ hφ x) =
      hilbertSumCoordinatewiseProx φ hφ (b.repr x) := by
  simp [hilbertBasisSeparablePenaltyCoordinatewiseProx]

/-- The transported coordinatewise proximal map has the textbook Hilbert-basis expansion
`∑' k, (Prox_{φₖ} (⟪x, bₖ⟫_ℝ)) • bₖ`. -/
theorem hilbertBasisSeparablePenaltyCoordinatewiseProx_eq_tsum
    (b : HilbertBasis ℕ ℝ H) (φ : ℕ → ℝ → Set.Ioi (⊥ : EReal))
    (hφ : ∀ k, φ k ∈ Γ₀(ℝ)) (x : H) :
    hilbertBasisSeparablePenaltyCoordinatewiseProx b φ hφ x =
      ∑' k : ℕ, (Prox[φ k, hφ k] (⟪x, b k⟫_ℝ)) • b k := by
  -- Expand the transported `ell2` vector back into the Hilbert basis via `repr.symm`.
  have hsum :
      HasSum
        (fun k : ℕ ↦ (Prox[φ k, hφ k] (⟪x, b k⟫_ℝ)) • b k)
        (hilbertBasisSeparablePenaltyCoordinatewiseProx b φ hφ x) := by
    simpa [hilbertBasisSeparablePenaltyCoordinatewiseProx,
      HilbertBasis.repr_apply_apply, real_inner_comm] using
      b.hasSum_repr_symm (hilbertSumCoordinatewiseProx φ hφ (b.repr x))
  exact hsum.tsum_eq.symm

/-- Helper for Proposition 24.16: the Hilbert-basis coordinate map composed with its adjoint is
the identity on `ell2`, written in the scalar form needed by Proposition 24.14. -/
theorem reprContinuousLinearMap_comp_adjoint_eq_oneSmulId
    [CompleteSpace H]
    (b : HilbertBasis ℕ ℝ H) :
    let e : H ≃L[ℝ] ell2 := b.repr.toContinuousLinearEquiv
    let L : H →L[ℝ] ell2 := e.toContinuousLinearMap
    L.comp L.adjoint = (1 : ℝ) • (1 : ell2 →L[ℝ] ell2) := by
  -- Identify the adjoint with the inverse coordinate isometry and then use the inverse law.
  dsimp
  rw [LinearIsometryEquiv.adjoint_eq_symm]
  ext y n
  simp

/-- Membership half of Proposition 24.16: if each `φₖ ∈ Γ₀(ℝ)` satisfies `φₖ ≥ φₖ(0) = 0`,
then the Hilbert-basis penalty `x ↦ ∑' k, φₖ (⟪x, bₖ⟫)` belongs to `Γ₀(H)`. -/
theorem hilbertBasisSeparablePenalty_mem_gammaZero
    (b : HilbertBasis ℕ ℝ H) (φ : ℕ → ℝ → Set.Ioi (⊥ : EReal))
    (hφ : ∀ k, φ k ∈ Γ₀(ℝ))
    (hmin : ∀ k x, (φ k 0 : EReal) ≤ (φ k x : EReal))
    (hzero : ∀ k, (φ k 0 : EReal) = 0) :
    hilbertBasisSeparablePenalty b φ ∈ Γ₀(H) := by
  letI : CompleteSpace H := b.repr.toIsometryEquiv.completeSpace
  let e : H ≃L[ℝ] ell2 := b.repr.toContinuousLinearEquiv
  let L : H →L[ℝ] ell2 := e.toContinuousLinearMap
  have hHilbertSum : hilbertSum φ ∈ Γ₀(ell2) :=
    hilbertSum_mem_gammaZero_of_forall_mem_gammaZero_of_min_zero φ hφ hmin hzero
  -- Transport the `Γ₀` owner from `ell2` back to `H` through Hilbert-basis coordinates.
  simpa [hilbertBasisSeparablePenalty, e, L, Function.comp_apply] using
    comp_continuousLinearMap_mem_gammaZero_of_comp_adjoint_eq_smul_id
      (f := hilbertSum φ) (L := L) (μ := (1 : PosReal)) hHilbertSum
      (reprContinuousLinearMap_comp_adjoint_eq_oneSmulId (b := b))

/-- Bridge form for Proposition 24.16 (2): under the same hypotheses, the proximal map of the
Hilbert-basis penalty is the transported coordinatewise proximal map. -/
theorem prox_hilbertBasisSeparablePenalty_eq_coordinatewiseProx
    [CompleteSpace H]
    (b : HilbertBasis ℕ ℝ H) (φ : ℕ → ℝ → Set.Ioi (⊥ : EReal))
    (hφ : ∀ k, φ k ∈ Γ₀(ℝ))
    (hmin : ∀ k x, (φ k 0 : EReal) ≤ (φ k x : EReal))
    (hzero : ∀ k, (φ k 0 : EReal) = 0)
    (x : H) :
    Prox[hilbertBasisSeparablePenalty b φ,
      hilbertBasisSeparablePenalty_mem_gammaZero b φ hφ hmin hzero] x =
      hilbertBasisSeparablePenaltyCoordinatewiseProx b φ hφ x := by
  let e : H ≃L[ℝ] ell2 := b.repr.toContinuousLinearEquiv
  let L : H →L[ℝ] ell2 := e.toContinuousLinearMap
  have hHilbertSum : hilbertSum φ ∈ Γ₀(ell2) :=
    hilbertSum_mem_gammaZero_of_forall_mem_gammaZero_of_min_zero φ hφ hmin hzero
  have hscalar :
      L.comp L.adjoint = (1 : ℝ) • (1 : ell2 →L[ℝ] ell2) :=
    reprContinuousLinearMap_comp_adjoint_eq_oneSmulId (b := b)
  have hproxTransport :
      Prox[hilbertBasisSeparablePenalty b φ,
        hilbertBasisSeparablePenalty_mem_gammaZero b φ hφ hmin hzero] x =
        x + (1 : ℝ)⁻¹ • L.adjoint (Prox[hilbertSum φ, hHilbertSum] (L x) - L x) := by
    -- Proposition 24.14 transports the prox computation from `ell2` back to `H`.
    simpa [hilbertBasisSeparablePenalty, e, L, Function.comp_apply,
      hilbertBasisSeparablePenalty_mem_gammaZero, hHilbertSum, scaledProximityOperator, one_smul]
      using
        prox_comp_continuousLinearMap_eq_add_inv_smul_adjoint_sub_of_comp_adjoint_eq_smul_id
          (f := hilbertSum φ) (L := L) (μ := (1 : PosReal)) hHilbertSum hscalar x
  rw [hproxTransport]
  rw [prox_hilbertSum_eq_coordinatewise φ hφ hmin hzero]
  -- Collapse the transported affine formula to `repr.symm` of the coordinatewise prox vector.
  have hcollapse :
      x + (1 : ℝ)⁻¹ •
          L.adjoint (hilbertSumCoordinatewiseProx φ hφ (L x) - L x) =
        hilbertBasisSeparablePenaltyCoordinatewiseProx b φ hφ x := by
    have hadd :
        L x + (hilbertSumCoordinatewiseProx φ hφ (L x) - L x) =
          hilbertSumCoordinatewiseProx φ hφ (L x) := by
      ext n
      abel_nf
    rw [show L.adjoint = e.symm.toContinuousLinearMap by
      simp [L, e, LinearIsometryEquiv.adjoint_eq_symm]]
    calc
      x + (1 : ℝ)⁻¹ •
          e.symm.toContinuousLinearMap
            (hilbertSumCoordinatewiseProx φ hφ (L x) - L x)
          =
          e.symm (L x) +
            e.symm.toContinuousLinearMap
              (hilbertSumCoordinatewiseProx φ hφ (L x) - L x) := by
            simp [e, L]
      _ =
          e.symm.toContinuousLinearMap
            (L x + (hilbertSumCoordinatewiseProx φ hφ (L x) - L x)) := by
            simp
      _ = e.symm.toContinuousLinearMap (hilbertSumCoordinatewiseProx φ hφ (L x)) := by
            rw [hadd]
      _ = e.symm (hilbertSumCoordinatewiseProx φ hφ (L x)) := by
            rfl
      _ = hilbertBasisSeparablePenaltyCoordinatewiseProx b φ hφ x := by
            simp [hilbertBasisSeparablePenaltyCoordinatewiseProx, e, L]
  exact hcollapse

/-- Proposition 24.16. Under the same hypotheses, the proximal map of the Hilbert-basis
penalty acts coordinatewise:
`Prox_f x = ∑' k, (Prox_{φₖ} (⟪x, bₖ⟫_ℝ)) • bₖ`. -/
theorem prox_hilbertBasisSeparablePenalty_eq_tsum
    [CompleteSpace H]
    (b : HilbertBasis ℕ ℝ H) (φ : ℕ → ℝ → Set.Ioi (⊥ : EReal))
    (hφ : ∀ k, φ k ∈ Γ₀(ℝ))
    (hmin : ∀ k x, (φ k 0 : EReal) ≤ (φ k x : EReal))
    (hzero : ∀ k, (φ k 0 : EReal) = 0)
    (x : H) :
    Prox[hilbertBasisSeparablePenalty b φ,
      hilbertBasisSeparablePenalty_mem_gammaZero b φ hφ hmin hzero] x =
      ∑' k : ℕ, (Prox[φ k, hφ k] (⟪x, b k⟫_ℝ)) • b k := by
  rw [prox_hilbertBasisSeparablePenalty_eq_coordinatewiseProx b φ hφ hmin hzero x]
  exact hilbertBasisSeparablePenaltyCoordinatewiseProx_eq_tsum b φ hφ x

end

end ERealFunction
