import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap12.Definition_12_23
import BauschkeLean.Chap12.Proposition_12_26
import BauschkeLean.Chap12.ProximityOperator
import BauschkeLean.Chap16.Proposition_16_4
import BauschkeLean.Chap20.Definition_20_20

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace
open SetValuedOperator

universe u

namespace ERealFunction

section SubdifferentialCalculus

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: Theorem 20.25 is Moreau's maximal-monotonicity theorem for the subdifferential.
- `core/canonical`: the owner conclusion is maximal monotonicity `Maximal IsMonotone (∂ f)`.
- `bridge/view`: the proof uses the Chapter 12 proximal-point variational inequality and rewrites
  it as subdifferential membership, while monotonicity comes from the Chapter 16 half-space
  description of `∂ f`. -/

omit [CompleteSpace H] in
/-- Helper for Theorem 20.25: if the effective domain of `f` is nonempty, then `∂ f` is monotone.
-/
private theorem subdifferential_isMonotone_of_nonemptyEffectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (hdom : (effectiveDomain f).Nonempty) :
    SetValuedOperator.IsMonotone (∂ f) := by
  rw [SetValuedOperator.isMonotone_iff]
  intro x u y v hux hvy
  have hx : x ∈ effectiveDomain f :=
    SubdifferentiableAt.mem_effectiveDomain hdom ⟨u, hux⟩
  have hy : y ∈ effectiveDomain f :=
    SubdifferentiableAt.mem_effectiveDomain hdom ⟨v, hvy⟩
  -- Rewrite both graph points through the affine half-space description of `∂ f`.
  have hux' :
      ∀ z ∈ effectiveDomain f,
        ⟪z - x, u⟫_ℝ ≤ (f z : EReal).toReal - (f x : EReal).toReal := by
    simpa [subdifferential_eq_iInter_affine_halfspaces f x hx] using hux
  have hvy' :
      ∀ z ∈ effectiveDomain f,
        ⟪z - y, v⟫_ℝ ≤ (f z : EReal).toReal - (f y : EReal).toReal := by
    simpa [subdifferential_eq_iInter_affine_halfspaces f y hy] using hvy
  have hxu : ⟪y - x, u⟫_ℝ ≤ (f y : EReal).toReal - (f x : EReal).toReal := by
    exact hux' y hy
  have hyv : ⟪x - y, v⟫_ℝ ≤ (f x : EReal).toReal - (f y : EReal).toReal := by
    exact hvy' x hx
  have hyx : y - x = -(x - y) := by
    abel_nf
  rw [hyx, inner_neg_left] at hxu
  have hmono : 0 ≤ ⟪x - y, u⟫_ℝ - ⟪x - y, v⟫_ℝ := by
    linarith
  simpa [inner_sub_right] using hmono

-- Proof sketch: prove monotonicity first. For maximality, let `B` be a monotone extension of
-- `∂ f`, and let `u ∈ B x`. The extension monotonicity gives the Minty inequalities
-- against every graph point of `∂ f`; Moreau's proximal construction then produces the
-- specific graph point that forces `x = Prox[f, hf] (x + u)`, hence `u ∈ (∂ f) x`.
/-- Theorem 20.25. (Moreau) If `f ∈ Γ₀(H)`, then the subdifferential `∂ f` is maximally
monotone. -/
theorem subdifferential_isMaximallyMonotone_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    Maximal IsMonotone (∂ f) := by
  rw [SetValuedOperator.maximal_iff_mem_iff]
  have hmono :
      ∀ ⦃x u y v : H⦄, u ∈ (∂ f) x → v ∈ (∂ f) y → 0 ≤ ⟪x - y, u - v⟫_ℝ :=
    (SetValuedOperator.isMonotone_iff (∂ f)).1
      (subdifferential_isMonotone_of_nonemptyEffectiveDomain f hf.2.nonempty)
  intro x u
  constructor
  · intro hu y v hv
    exact hmono hu hv
  · intro hMinty
    let p : H := Prox[f, hf] (x + u)
    let q : H := x + u - p
    have hconv : ConvexOn f (effectiveDomain f) := (mem_gammaZero_iff.mp hf).2
    -- Rewrite the proximal point as a subgradient relation through the Chapter 12 variational
    -- inequality, avoiding the duplicate-owner import from Proposition 16.44.
    have hq : q ∈ (∂ f) p := by
      have hp : p = Prox[f, hf] (x + u) := by
        simp [p]
      have hp_prox : IsProxPoint f (x + u) p := by
        rw [hp]
        simpa using
          proximityOperator_isProxPoint f
            (hasUniqueProxPoint_of_mem_gammaZero (f := f) hf) (x + u)
      rw [mem_subdifferential_iff]
      simpa [q] using
        (isProxPoint_iff_forall_inner_add_le f hconv (x + u) p).mp hp_prox
    -- Feed the source-style graph point `(p, q)` into the Minty inequality.
    have htest : 0 ≤ ⟪x - p, u - q⟫_ℝ := hMinty hq
    -- Normalize the Minty inequality to `0 ≤ -‖x - p‖²`, forcing `x = p`.
    have hsq_nonpos : ‖x - p‖ ^ (2 : ℕ) ≤ 0 := by
      have hresidual : u - q = -(x - p) := by
        dsimp [q]
        abel_nf
      have hnonneg : 0 ≤ -‖x - p‖ ^ (2 : ℕ) := by
        calc
          0 ≤ ⟪x - p, u - q⟫_ℝ := htest
          _ = ⟪x - p, -(x - p)⟫_ℝ := by
            rw [hresidual]
          _ = -⟪x - p, x - p⟫_ℝ := by
            rw [inner_neg_right]
          _ = -‖x - p‖ ^ (2 : ℕ) := by
            rw [real_inner_self_eq_norm_sq]
      linarith
    have hsq_zero : ‖x - p‖ ^ (2 : ℕ) = 0 := by
      exact le_antisymm hsq_nonpos (sq_nonneg ‖x - p‖)
    have hxp : x = p := by
      exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hsq_zero))
    -- Transport the residual graph point back to `(x, u)` using the forced identities.
    have huq : q = u := by
      calc
        q = x + u - p := by rfl
        _ = x + u - x := by rw [← hxp]
        _ = u := by abel_nf
    rw [← hxp, huq] at hq
    exact hq

end SubdifferentialCalculus

end ERealFunction
