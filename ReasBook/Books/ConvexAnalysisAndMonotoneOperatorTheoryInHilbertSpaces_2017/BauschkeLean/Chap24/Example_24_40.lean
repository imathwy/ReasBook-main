import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap09.Example_9_36
import BauschkeLean.Chap12.ScaledProximityOperator
import BauschkeLean.Chap13.Example_13_2
import BauschkeLean.Chap24.Proposition_24_1

-- Declarations for this item will be appended below by the statement pipeline.

namespace ERealFunction

open InnerProductSpace
open Set
open Filter
open scoped Topology

noncomputable section

private theorem negativeBurgEntropy_isProper : IsProper negativeBurgEntropy := by
  refine ⟨?_, ?_⟩
  · intro ξ
    by_cases hξ : 0 < ξ
    · simp [negativeBurgEntropy, hξ]
    · simp [negativeBurgEntropy, hξ]
  · refine ⟨1, ?_⟩
    simp [dom, negativeBurgEntropy]

/-- The Chapter 24 `]-∞,+∞]`-valued owner induced by the Chapter 13 negative Burg entropy. -/
def negativeBurgEntropyIoi : ℝ → Set.Ioi (⊥ : EReal) :=
  properIoi negativeBurgEntropy negativeBurgEntropy_isProper

/-- Coercing `negativeBurgEntropyIoi` back to `EReal` recovers `negativeBurgEntropy`. -/
@[simp] theorem negativeBurgEntropyIoi_apply (ξ : ℝ) :
    (negativeBurgEntropyIoi ξ : EReal) = negativeBurgEntropy ξ :=
  rfl

/-- Helper for Example 24.40: the Chapter 24 proper packaging of the negative Burg entropy agrees
with the canonical Chapter 9 negative-log barrier on `(0,+∞)` and its `+∞` extension elsewhere. -/
private theorem properIoi_negativeBurgEntropy_eq_negLogIoiExtension :
    properIoi negativeBurgEntropy negativeBurgEntropy_isProper = negLogIoiExtension := by
  ext ξ
  -- Compare the two owners by splitting into the positive branch, zero, and the negative branch.
  by_cases hξ : 0 < ξ
  · simpa [negativeBurgEntropy, hξ] using negLogIoiExtension_apply_of_pos hξ
  · have hξ_le : ξ ≤ 0 := le_of_not_gt hξ
    rcases hξ_le.eq_or_lt with rfl | hξ_neg
    · simp [negativeBurgEntropy, negLogIoiExtension_apply_zero]
    · simp [negativeBurgEntropy, hξ, negLogIoiExtension_apply_of_neg hξ_neg]

/-- Helper for Example 24.40: the Chapter 24 owner belongs to `Γ₀(ℝ)` because it is exactly the
canonical negative-log barrier from Chapter 9. -/
private theorem properIoi_negativeBurgEntropy_mem_gammaZero :
    properIoi negativeBurgEntropy negativeBurgEntropy_isProper ∈ Γ₀(ℝ) := by
  -- Rewrite the owner to the Chapter 9 model and reuse its `Γ₀` theorem.
  simpa [properIoi_negativeBurgEntropy_eq_negLogIoiExtension] using
    negLogIoiExtension_mem_gammaZero

/-- The Chapter 24 `]-∞,+∞]`-valued negative Burg entropy belongs to `Γ₀(ℝ)`. -/
theorem negativeBurgEntropyIoi_mem_gammaZero :
    negativeBurgEntropyIoi ∈ Γ₀(ℝ) := by
  simpa [negativeBurgEntropyIoi] using properIoi_negativeBurgEntropy_mem_gammaZero

/-- Helper for Example 24.40: positive scaling does not change the effective domain of the
negative Burg entropy, so the scaled owner is finite exactly on `(0,+∞)`. -/
private theorem scaled_negativeBurgEntropyIoi_effectiveDomain (γ : PosReal) :
    effectiveDomain (γ • negativeBurgEntropyIoi) = Set.Ioi (0 : ℝ) := by
  have hbase : effectiveDomain negativeBurgEntropyIoi = Set.Ioi (0 : ℝ) := by
    -- First identify the unscaled owner with the canonical Chapter 9 barrier.
    simpa [negativeBurgEntropyIoi, properIoi_negativeBurgEntropy_eq_negLogIoiExtension] using
      effectiveDomain_negLogIoiExtension
  ext x
  constructor
  · intro hx
    -- A finite scaled value forces the original value to be finite as well.
    have hx_top : ((γ • negativeBurgEntropyIoi) x : EReal) ≠ ⊤ := by
      exact ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hbase_top : (negativeBurgEntropyIoi x : EReal) ≠ ⊤ := by
      intro htop
      have hscaled_top : ((γ • negativeBurgEntropyIoi) x : EReal) = ⊤ := by
        rw [posReal_smul_apply, htop]
        simpa using EReal.coe_mul_top_of_pos γ.2
      exact hx_top hscaled_top
    rw [← hbase]
    exact mem_effectiveDomain_iff.mpr (lt_top_iff_ne_top.mpr hbase_top)
  · intro hx
    -- Conversely, positive scaling preserves finiteness of an already finite value.
    rw [mem_effectiveDomain_iff, lt_top_iff_ne_top]
    have hbase_mem : x ∈ effectiveDomain negativeBurgEntropyIoi := by
      simpa [hbase] using hx
    have hbase_top : (negativeBurgEntropyIoi x : EReal) ≠ ⊤ := by
      exact lt_top_iff_ne_top.mp (mem_effectiveDomain_iff.mp hbase_mem)
    rw [posReal_smul_apply, EReal.mul_ne_top]
    refine ⟨Or.inl (EReal.coe_ne_bot (γ : ℝ)), Or.inl (EReal.coe_nonneg.mpr γ.2.le),
      Or.inl (EReal.coe_ne_top (γ : ℝ)), Or.inr hbase_top⟩

/-- Helper for Example 24.40: the positive quadratic root solves the first-order equation
`p - γ / p = ξ`. -/
private theorem negative_burg_prox_candidate_pos_and_residual (γ : PosReal) (ξ : ℝ) :
    let p : ℝ := (ξ + Real.sqrt (ξ ^ (2 : ℕ) + 4 * (γ : ℝ))) / 2
    0 < p ∧ -(γ : ℝ) / p = ξ - p := by
  dsimp
  let d : ℝ := ξ ^ (2 : ℕ) + 4 * (γ : ℝ)
  have hd_nonneg : 0 ≤ d := by
    have hsq : 0 ≤ ξ ^ (2 : ℕ) := sq_nonneg ξ
    have hγ : 0 ≤ 4 * (γ : ℝ) := by nlinarith [γ.2.le]
    dsimp [d]
    nlinarith
  have hd_gt : ξ ^ (2 : ℕ) < d := by
    -- The discriminant is strictly larger than `ξ²` because `γ > 0`.
    have hγ : 0 < 4 * (γ : ℝ) := by nlinarith [γ.2]
    dsimp [d]
    nlinarith
  have habs_lt : |ξ| < Real.sqrt d := by
    -- Comparing squares shows that the square root dominates `|ξ|`.
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg ξ) hd_gt
  have hnum_pos : 0 < ξ + Real.sqrt d := by
    nlinarith [neg_abs_le ξ, habs_lt]
  have hp : 0 < (ξ + Real.sqrt d) / 2 := by
    exact div_pos hnum_pos (by norm_num)
  have hsub :
      ξ - (ξ + Real.sqrt d) / 2 = (ξ - Real.sqrt d) / 2 := by
    ring
  have hprod :
      ((ξ + Real.sqrt d) / 2) * (ξ - (ξ + Real.sqrt d) / 2) = -(γ : ℝ) := by
    -- Expanding the product reduces the stationarity equation to the discriminant identity.
    rw [hsub]
    calc
      ((ξ + Real.sqrt d) / 2) * ((ξ - Real.sqrt d) / 2) =
          (ξ ^ (2 : ℕ) - (Real.sqrt d) ^ (2 : ℕ)) / 4 := by
        ring
      _ = (ξ ^ (2 : ℕ) - d) / 4 := by
        rw [Real.sq_sqrt hd_nonneg]
      _ = -(γ : ℝ) := by
        dsimp [d]
        ring
  have hp_ne : (ξ + Real.sqrt d) / 2 ≠ 0 := ne_of_gt hp
  have hresidual : -(γ : ℝ) / ((ξ + Real.sqrt d) / 2) = ξ - (ξ + Real.sqrt d) / 2 := by
    -- Divide the quadratic identity by the positive root.
    rw [div_eq_iff hp_ne]
    simpa [mul_comm] using hprod.symm
  exact ⟨hp, hresidual⟩

/-- Helper for Example 24.40: near the positive quadratic root, the scaled negative Burg entropy
has Gâteaux gradient `ξ - p`. -/
private theorem scaled_negativeBurgEntropyIoi_hasGateauxDerivativeAt_candidate
    (γ : PosReal) (ξ : ℝ) :
    let p : ℝ := (ξ + Real.sqrt (ξ ^ (2 : ℕ) + 4 * (γ : ℝ))) / 2
    HasGateauxDerivativeAt
      (fun y ↦ (((γ • negativeBurgEntropyIoi) y : EReal).toReal))
      (toDualMap ℝ ℝ (ξ - p))
      p := by
  dsimp
  let p : ℝ := (ξ + Real.sqrt (ξ ^ (2 : ℕ) + 4 * (γ : ℝ))) / 2
  have hp : 0 < p := by
    simpa [p] using (negative_burg_prox_candidate_pos_and_residual γ ξ).1
  have hresidual : -(γ : ℝ) / p = ξ - p := by
    simpa [p] using (negative_burg_prox_candidate_pos_and_residual γ ξ).2
  have hseed_eventually :
      (fun y ↦ (((γ • negativeBurgEntropyIoi) y : EReal).toReal)) =ᶠ[𝓝 p]
        (fun y : ℝ ↦ -(γ : ℝ) * Real.log y) := by
    -- Around the positive candidate, the indicator branch is inactive and the owner is the real
    -- seed `y ↦ -γ log y`.
    have hnhds : Set.Ioi (0 : ℝ) ∈ 𝓝 p := isOpen_Ioi.mem_nhds hp
    filter_upwards [hnhds] with y hy
    have hneglog :
        (negativeBurgEntropyIoi y : EReal) = (((-Real.log y : ℝ)) : EReal) := by
      calc
        (negativeBurgEntropyIoi y : EReal) = (negLogIoiExtension y : EReal) := by
          rw [negativeBurgEntropyIoi, properIoi_negativeBurgEntropy_eq_negLogIoiExtension]
        _ = (((-Real.log y : ℝ)) : EReal) := negLogIoiExtension_apply_of_pos hy
    have hvalue :
        ((γ • negativeBurgEntropyIoi) y : EReal) = (((-(γ : ℝ) * Real.log y : ℝ)) : EReal) := by
      rw [posReal_smul_apply, hneglog, ← EReal.coe_mul]
      congr 1
      ring
    rw [hvalue]
    rw [EReal.toReal_coe]
  have hseed_deriv :
      HasDerivAt (fun y : ℝ ↦ -(γ : ℝ) * Real.log y) (-(γ : ℝ) / p) p := by
    -- Differentiate the real seed on the positive branch.
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (Real.hasDerivAt_log hp.ne').const_mul (-(γ : ℝ))
  have htarget_deriv :
      HasDerivAt (fun y ↦ (((γ • negativeBurgEntropyIoi) y : EReal).toReal)) (-(γ : ℝ) / p) p := by
    exact hseed_deriv.congr_of_eventuallyEq hseed_eventually
  have hgrad :
      HasGradientAt
        (fun y ↦ (((γ • negativeBurgEntropyIoi) y : EReal).toReal))
        (ξ - p) p := by
    -- Rewrite the scalar derivative using the quadratic-root identity before switching to the
    -- one-dimensional gradient API.
    exact (htarget_deriv.congr_deriv hresidual).hasGradientAt'
  have hGateaux :
      HasGateauxDerivativeAt
        (fun y ↦ (((γ • negativeBurgEntropyIoi) y : EReal).toReal))
        (InnerProductSpace.toDual ℝ ℝ (ξ - p)) p := by
    exact hgrad.hasFDerivAt.hasGateauxDerivativeAt
  exact by
    simpa [InnerProductSpace.toDual_apply_eq_toDualMap_apply] using hGateaux

/-- Example 24.40: let `γ ∈ ℝ_{++}` and let `φ(ξ) = -log ξ` for `ξ > 0`, with `φ(ξ) = +∞` for
`ξ ≤ 0`. Then `Prox_{γ φ} ξ = (ξ + sqrt (ξ^2 + 4γ)) / 2` for every `ξ ∈ ℝ`. -/
theorem prox_negativeBurgEntropy_eq (γ : PosReal) :
    Prox[γ, negativeBurgEntropyIoi, negativeBurgEntropyIoi_mem_gammaZero] =
      fun ξ : ℝ ↦ (ξ + Real.sqrt (ξ ^ (2 : ℕ) + 4 * (γ : ℝ))) / 2 := by
  funext ξ
  let p : ℝ := (ξ + Real.sqrt (ξ ^ (2 : ℕ) + 4 * (γ : ℝ))) / 2
  have hp_pos : 0 < p := by
    -- The selected quadratic root is positive, so it lies in the interior domain.
    simpa [p] using (negative_burg_prox_candidate_pos_and_residual γ ξ).1
  have hp :
      p ∈ interior (effectiveDomain (γ • negativeBurgEntropyIoi)) := by
    simpa [scaled_negativeBurgEntropyIoi_effectiveDomain, p, isOpen_Ioi.interior_eq] using hp_pos
  have hgrad :
      HasGateauxDerivativeAt
        (fun y ↦ (((γ • negativeBurgEntropyIoi) y : EReal).toReal))
        (toDualMap ℝ ℝ (ξ - p))
        p := by
    simpa [p] using scaled_negativeBurgEntropyIoi_hasGateauxDerivativeAt_candidate γ ξ
  have hprox :
      p = Prox[γ • negativeBurgEntropyIoi,
        smul_mem_gammaZero negativeBurgEntropyIoi negativeBurgEntropyIoi_mem_gammaZero γ] ξ := by
    -- Proposition 24.1 reduces the proximal identity to the scalar equation `(ξ - p) + p = ξ`.
    exact
      (eq_proximityOperator_iff_gateauxGradient_add_eq
        (γ • negativeBurgEntropyIoi)
        (smul_mem_gammaZero negativeBurgEntropyIoi negativeBurgEntropyIoi_mem_gammaZero γ)
        hp hgrad).2
        (by
          dsimp [p]
          abel_nf)
  simpa [scaledProximityOperator, p] using hprox.symm

end

end ERealFunction
