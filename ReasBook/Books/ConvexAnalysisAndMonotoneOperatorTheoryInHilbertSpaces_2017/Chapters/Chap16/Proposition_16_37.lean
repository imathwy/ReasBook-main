import Mathlib
import BauschkeLean.Chap01.Text_1_0_9
import BauschkeLean.Chap13.Corollary_13_38
import BauschkeLean.Chap13.Proposition_13_15
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap16.Proposition_16_4
import BauschkeLean.Chap16.Proposition_16_10
import BauschkeLean.Chap16.Proposition_16_27
import BauschkeLean.Chap16.Corollary_16_30

open Set
open scoped InnerProductSpace

universe u

namespace ERealFunction

section SubdifferentialConjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))

local notation "f⋆" => gammaZeroConjugate f hf

/-- Helper for Proposition 16 37: a subgradient point for `f` lies in the effective domain of the
Fenchel conjugate `f*`, represented by `gammaZeroConjugate f hf`. -/
lemma gammaZeroConjugate_mem_effectiveDomain_of_mem_subdifferential
    {x u : H} (hu : u ∈ (∂ f) x) :
    u ∈ effectiveDomain f⋆ := by
  -- A subgradient point makes `x` an effective-domain point of `f`, so Fenchel--Young equality
  -- cannot have `f⋆ u = ⊤`.
  have hx_dom : x ∈ effectiveDomain f := by
    have hx_subdom : x ∈ SetValuedOperator.dom (∂ f) := by
      rw [SetValuedOperator.mem_dom_iff]
      exact ⟨u, hu⟩
    exact subdifferential_domain_subset_effectiveDomain f hf.2.nonempty hx_subdom
  have hfx_bot : (f x : EReal) ≠ ⊥ := ne_of_gt (f x).2
  have hfy :
      (f x : EReal) + (f⋆ u : EReal) =
        ((⟪x, u⟫_ℝ : ℝ) : EReal) := by
    simpa [gammaZeroConjugate_apply] using
      (mem_subdifferential_iff_fenchel_young_eq (f := f) hf.2.nonempty x u).1 hu
  have hfu_top : (f⋆ u : EReal) ≠ ⊤ := by
    intro hfu_top
    have hsum_top : (f x : EReal) + (f⋆ u : EReal) = ⊤ := by
      rw [hfu_top]
      exact EReal.add_top_of_ne_bot hfx_bot
    exact EReal.coe_ne_top _ <| by
      calc
        (((⟪x, u⟫_ℝ : ℝ) : EReal)) = (f x : EReal) + (f⋆ u : EReal) := by
          simpa using hfy.symm
        _ = ⊤ := hsum_top
  -- Effective-domain membership is exactly finiteness for `]-∞,+∞]`-valued functions.
  rw [mem_effectiveDomain_iff]
  exact lt_of_le_of_ne le_top hfu_top

/-- Helper for Proposition 16 37: Fenchel--Young equality along `∂ f(x)` becomes a real-valued
formula for the trace of the Fenchel conjugate. -/
lemma gammaZeroConjugate_toReal_eq_inner_sub_of_mem_subdifferential
    {x u : H} (hu : u ∈ (∂ f) x) :
    (f⋆ u : EReal).toReal = ⟪x, u⟫_ℝ - (f x : EReal).toReal := by
  -- Convert Fenchel--Young equality to a real equality once both sides are known to be finite.
  have hx_dom : x ∈ effectiveDomain f := by
    have hx_subdom : x ∈ SetValuedOperator.dom (∂ f) := by
      rw [SetValuedOperator.mem_dom_iff]
      exact ⟨u, hu⟩
    exact subdifferential_domain_subset_effectiveDomain f hf.2.nonempty hx_subdom
  have hu_dom : u ∈ effectiveDomain f⋆ :=
    gammaZeroConjugate_mem_effectiveDomain_of_mem_subdifferential (f := f) hf hu
  have hfx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx_dom)
  have hfx_bot : (f x : EReal) ≠ ⊥ := ne_of_gt (f x).2
  have hfu_top : (f⋆ u : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hu_dom)
  have hfu_bot : (f⋆ u : EReal) ≠ ⊥ := ne_of_gt (f⋆ u).2
  have hfy :
      (f x : EReal) + (f⋆ u : EReal) =
        ((⟪x, u⟫_ℝ : ℝ) : EReal) := by
    simpa [gammaZeroConjugate_apply] using
      (mem_subdifferential_iff_fenchel_young_eq (f := f) hf.2.nonempty x u).1 hu
  have hfy' := hfy
  rw [← EReal.coe_toReal hfx_top hfx_bot, ← EReal.coe_toReal hfu_top hfu_bot,
    ← EReal.coe_add] at hfy'
  have hfy_toReal :
      (f x : EReal).toReal + (f⋆ u : EReal).toReal = ⟪x, u⟫_ℝ := by
    exact EReal.coe_eq_coe_iff.mp hfy'
  linarith

/-- Helper for Proposition 16 37: Corollary 16.30 transports a subgradient of the Fenchel
conjugate back to a subgradient of the original function. -/
lemma mem_subdifferential_of_mem_subdifferential_gammaZeroConjugate
    {x u : H} (hu : x ∈ (∂ f⋆) u) :
    u ∈ (∂ f) x := by
  -- Corollary 16.30 identifies `∂ f⋆` with the inverse graph of `∂ f`.
  rw [← inverse_subdifferential_eq_subdifferential_gammaZeroConjugate (f := f) hf] at hu
  simpa [SetValuedOperator.mem_inverse_iff] using hu

/-- Helper for Proposition 16 37: one interior point of `∂ f*` together with affine trace data on
`[u₀,u₁]` forces both endpoints into `∂ f(x)`. -/
lemma endpoint_mem_subdifferential_of_affine_conjugate_trace
    {x u0 u1 : H} {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1)
    (hfin : segment ℝ u0 u1 ⊆ effectiveDomain f⋆)
    (haff :
      EqOn
        (fun β : ℝ ↦ (f⋆ (AffineMap.lineMap u0 u1 β) : EReal).toReal)
        (AffineMap.lineMap
          ((f⋆ u0 : EReal).toReal)
          ((f⋆ u1 : EReal).toReal))
        (Icc (0 : ℝ) 1))
    (hxconj : x ∈ (∂ f⋆) (AffineMap.lineMap u0 u1 α)) :
    u0 ∈ (∂ f) x ∧ u1 ∈ (∂ f) x := by
  let m : H := AffineMap.lineMap u0 u1 α
  -- Route correction: first transport the interior `∂ f⋆` datum back to `∂ f`, then compare the
  -- affine trace identity with the endpoint Fenchel--Young inequalities in real form.
  have hm_sub : m ∈ (∂ f) x := by
    simpa [m] using
      mem_subdifferential_of_mem_subdifferential_gammaZeroConjugate
        (f := f) hf hxconj
  have hα_Icc : α ∈ Icc (0 : ℝ) 1 := ⟨hα.1.le, hα.2.le⟩
  have hx_dom : x ∈ effectiveDomain f := by
    have hx_subdom : x ∈ SetValuedOperator.dom (∂ f) := by
      rw [SetValuedOperator.mem_dom_iff]
      exact ⟨m, hm_sub⟩
    exact subdifferentialDomain_subset_effectiveDomain_of_mem_gammaZero hf hx_subdom
  have hu0_dom : u0 ∈ effectiveDomain f⋆ := hfin (left_mem_segment ℝ u0 u1)
  have hu1_dom : u1 ∈ effectiveDomain f⋆ := hfin (right_mem_segment ℝ u0 u1)
  have hfx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx_dom)
  have hfx_bot : (f x : EReal) ≠ ⊥ := ne_of_gt (f x).2
  have hu0_top : (f⋆ u0 : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hu0_dom)
  have hu1_top : (f⋆ u1 : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hu1_dom)
  have hu0_bot : (f⋆ u0 : EReal) ≠ ⊥ := ne_of_gt (f⋆ u0).2
  have hu1_bot : (f⋆ u1 : EReal) ≠ ⊥ := ne_of_gt (f⋆ u1).2
  have hmid_trace :
      (f⋆ m : EReal).toReal =
        AffineMap.lineMap
          ((f⋆ u0 : EReal).toReal)
          ((f⋆ u1 : EReal).toReal) α := by
    simpa [m] using haff hα_Icc
  have hmid_affine :
      (f⋆ m : EReal).toReal =
        (1 - α) * ((f⋆ u0 : EReal).toReal) + α * ((f⋆ u1 : EReal).toReal) := by
    calc
      (f⋆ m : EReal).toReal =
          AffineMap.lineMap
            ((f⋆ u0 : EReal).toReal)
            ((f⋆ u1 : EReal).toReal) α := hmid_trace
      _ = (1 - α) * ((f⋆ u0 : EReal).toReal) + α * ((f⋆ u1 : EReal).toReal) := by
        simp [AffineMap.lineMap_apply_module, smul_eq_mul, sub_eq_add_neg, add_comm]
  have hmid_formula :
      (f⋆ m : EReal).toReal = ⟪x, m⟫_ℝ - (f x : EReal).toReal :=
    gammaZeroConjugate_toReal_eq_inner_sub_of_mem_subdifferential (f := f) hf hm_sub
  have hmid_linear :
      ⟪x, m⟫_ℝ - (f x : EReal).toReal =
        (1 - α) * (⟪x, u0⟫_ℝ - (f x : EReal).toReal) +
          α * (⟪x, u1⟫_ℝ - (f x : EReal).toReal) := by
    calc
      ⟪x, m⟫_ℝ - (f x : EReal).toReal =
          (1 - α) * ⟪x, u0⟫_ℝ + α * ⟪x, u1⟫_ℝ - (f x : EReal).toReal := by
            simp [m, AffineMap.lineMap_apply_module, inner_add_right, inner_smul_right,
              sub_eq_add_neg, add_mul, add_left_comm, add_comm]
      _ = (1 - α) * (⟪x, u0⟫_ℝ - (f x : EReal).toReal) +
            α * (⟪x, u1⟫_ℝ - (f x : EReal).toReal) := by
            ring
  -- Fenchel--Young gives the endpoint inequalities, and finiteness turns them into real bounds.
  have hfy0 :
      ((⟪x, u0⟫_ℝ : ℝ) : EReal) ≤ (f x : EReal) + (f⋆ u0 : EReal) := by
    simpa [gammaZeroConjugate_apply] using
      (fenchel_young_inequality (isProper_of_mem_gammaZero hf) x u0)
  have hfy1 :
      ((⟪x, u1⟫_ℝ : ℝ) : EReal) ≤ (f x : EReal) + (f⋆ u1 : EReal) := by
    simpa [gammaZeroConjugate_apply] using
      (fenchel_young_inequality (isProper_of_mem_gammaZero hf) x u1)
  have hsum0_top : (f x : EReal) + (f⋆ u0 : EReal) ≠ ⊤ :=
    EReal.add_ne_top hfx_top hu0_top
  have hsum1_top : (f x : EReal) + (f⋆ u1 : EReal) ≠ ⊤ :=
    EReal.add_ne_top hfx_top hu1_top
  have hfy0_toReal :
      ⟪x, u0⟫_ℝ ≤ (f x : EReal).toReal + (f⋆ u0 : EReal).toReal := by
    have hfy0' := hfy0
    rw [← EReal.coe_toReal hfx_top hfx_bot, ← EReal.coe_toReal hu0_top hu0_bot,
      ← EReal.coe_add] at hfy0'
    exact_mod_cast hfy0'
  have hfy1_toReal :
      ⟪x, u1⟫_ℝ ≤ (f x : EReal).toReal + (f⋆ u1 : EReal).toReal := by
    have hfy1' := hfy1
    rw [← EReal.coe_toReal hfx_top hfx_bot, ← EReal.coe_toReal hu1_top hu1_bot,
      ← EReal.coe_add] at hfy1'
    exact_mod_cast hfy1'
  have hweighted :
      (1 - α) *
          (((f⋆ u0 : EReal).toReal) - (⟪x, u0⟫_ℝ - (f x : EReal).toReal)) +
        α * (((f⋆ u1 : EReal).toReal) - (⟪x, u1⟫_ℝ - (f x : EReal).toReal)) = 0 := by
    linarith [hmid_affine, hmid_formula, hmid_linear]
  have hδ0_nonneg :
      0 ≤ ((f⋆ u0 : EReal).toReal) - (⟪x, u0⟫_ℝ - (f x : EReal).toReal) := by
    linarith
  have hδ1_nonneg :
      0 ≤ ((f⋆ u1 : EReal).toReal) - (⟪x, u1⟫_ℝ - (f x : EReal).toReal) := by
    linarith
  have hδ0_zero :
      ((f⋆ u0 : EReal).toReal) - (⟪x, u0⟫_ℝ - (f x : EReal).toReal) = 0 := by
    have hα_pos : 0 < α := hα.1
    have h_one_sub_pos : 0 < 1 - α := by
      linarith [hα.2]
    have hα_nonneg : 0 ≤ α := hα_pos.le
    have hδ1_scaled_nonneg :
        0 ≤ α * (((f⋆ u1 : EReal).toReal) - (⟪x, u1⟫_ℝ - (f x : EReal).toReal)) := by
      exact mul_nonneg hα_nonneg hδ1_nonneg
    by_contra hδ0_ne
    have hδ0_pos :
        0 < ((f⋆ u0 : EReal).toReal) - (⟪x, u0⟫_ℝ - (f x : EReal).toReal) := by
      exact lt_of_le_of_ne hδ0_nonneg (by simpa [eq_comm] using hδ0_ne)
    have hδ0_scaled_pos :
        0 <
          (1 - α) * (((f⋆ u0 : EReal).toReal) - (⟪x, u0⟫_ℝ - (f x : EReal).toReal)) := by
      exact mul_pos h_one_sub_pos hδ0_pos
    linarith [hweighted, hδ1_scaled_nonneg, hδ0_scaled_pos]
  have hδ1_zero :
      ((f⋆ u1 : EReal).toReal) - (⟪x, u1⟫_ℝ - (f x : EReal).toReal) = 0 := by
    have hα_pos : 0 < α := hα.1
    have h_one_sub_pos : 0 < 1 - α := by
      linarith [hα.2]
    have h_one_sub_nonneg : 0 ≤ 1 - α := h_one_sub_pos.le
    have hδ0_scaled_nonneg :
        0 ≤
          (1 - α) * (((f⋆ u0 : EReal).toReal) - (⟪x, u0⟫_ℝ - (f x : EReal).toReal)) := by
      exact mul_nonneg h_one_sub_nonneg hδ0_nonneg
    by_contra hδ1_ne
    have hδ1_pos :
        0 < ((f⋆ u1 : EReal).toReal) - (⟪x, u1⟫_ℝ - (f x : EReal).toReal) := by
      exact lt_of_le_of_ne hδ1_nonneg (by simpa [eq_comm] using hδ1_ne)
    have hδ1_scaled_pos :
        0 <
          α * (((f⋆ u1 : EReal).toReal) - (⟪x, u1⟫_ℝ - (f x : EReal).toReal)) := by
      exact mul_pos hα_pos hδ1_pos
    linarith [hweighted, hδ0_scaled_nonneg, hδ1_scaled_pos]
  have hsum0_real :
      (f x : EReal).toReal + (f⋆ u0 : EReal).toReal = ⟪x, u0⟫_ℝ := by
    linarith
  have hsum1_real :
      (f x : EReal).toReal + (f⋆ u1 : EReal).toReal = ⟪x, u1⟫_ℝ := by
    linarith
  have hfy0_eq :
      (f x : EReal) + (f⋆ u0 : EReal) = ((⟪x, u0⟫_ℝ : ℝ) : EReal) := by
    have hsum0_coe :
        (((f x : EReal).toReal + (f⋆ u0 : EReal).toReal : ℝ) : EReal) =
          (f x : EReal) + (f⋆ u0 : EReal) := by
      calc
        (((f x : EReal).toReal + (f⋆ u0 : EReal).toReal : ℝ) : EReal) =
            (((f x : EReal).toReal : EReal) + ((f⋆ u0 : EReal).toReal : EReal)) := by
              rw [EReal.coe_add]
        _ = (f x : EReal) + (f⋆ u0 : EReal) := by
              rw [EReal.coe_toReal hfx_top hfx_bot, EReal.coe_toReal hu0_top hu0_bot]
    calc
      (f x : EReal) + (f⋆ u0 : EReal) =
          (((f x : EReal).toReal + (f⋆ u0 : EReal).toReal : ℝ) : EReal) := by
            simpa using hsum0_coe.symm
      _ = ((⟪x, u0⟫_ℝ : ℝ) : EReal) := by
        exact_mod_cast hsum0_real
  have hfy1_eq :
      (f x : EReal) + (f⋆ u1 : EReal) = ((⟪x, u1⟫_ℝ : ℝ) : EReal) := by
    have hsum1_coe :
        (((f x : EReal).toReal + (f⋆ u1 : EReal).toReal : ℝ) : EReal) =
          (f x : EReal) + (f⋆ u1 : EReal) := by
      calc
        (((f x : EReal).toReal + (f⋆ u1 : EReal).toReal : ℝ) : EReal) =
            (((f x : EReal).toReal : EReal) + ((f⋆ u1 : EReal).toReal : EReal)) := by
              rw [EReal.coe_add]
        _ = (f x : EReal) + (f⋆ u1 : EReal) := by
              rw [EReal.coe_toReal hfx_top hfx_bot, EReal.coe_toReal hu1_top hu1_bot]
    calc
      (f x : EReal) + (f⋆ u1 : EReal) =
          (((f x : EReal).toReal + (f⋆ u1 : EReal).toReal : ℝ) : EReal) := by
            simpa using hsum1_coe.symm
      _ = ((⟪x, u1⟫_ℝ : ℝ) : EReal) := by
        exact_mod_cast hsum1_real
  constructor
  · exact (mem_subdifferential_iff_fenchel_young_eq (f := f) hf.2.nonempty x u0).2 <| by
      simpa [gammaZeroConjugate_apply] using hfy0_eq
  · exact (mem_subdifferential_iff_fenchel_young_eq (f := f) hf.2.nonempty x u1).2 <| by
      simpa [gammaZeroConjugate_apply] using hfy1_eq

/- Source/core/bridge triage:
- `source-facing`: Proposition 16.37 is the segment-affineness statement for the Fenchel conjugate.
- `core/canonical`: the owner objects are `gammaZeroConjugate f hf`, `effectiveDomain`, and the
  subdifferential `∂ f`.
- `bridge/view`: the real-valued trace `u ↦ (f⋆ u : EReal).toReal` is used only after explicit
  finiteness on the whole segment, so the public statement does not silently collapse `⊤` via
  `EReal.toReal`.
-/

-- Proof sketch: if every point of the closed segment lies in `(∂ f) x`, then Theorem 16.29 gives
-- Fenchel--Young equality at each point of that segment. Evaluating this equality along the
-- parameterization `AffineMap.lineMap u0 u1` shows that the conjugate values coincide with the
-- affine interpolation of their endpoint values on `Set.Icc (0 : ℝ) 1`.
/-- Proposition 16 37 (1): if the whole segment `[u₀,u₁]` lies in the subdifferential `∂ f(x)`,
then the Fenchel conjugate `f*`, represented by `gammaZeroConjugate f hf`, is finite on that
segment, and its finite-valued trace is affine there. In Lean, the affineness clause is expressed
by equality with the affine interpolation of the endpoint values along the line-map
parameterization of `[u₀,u₁]`, after recording the needed effective-domain control explicitly. -/
theorem gammaZeroConjugate_eq_lineMap_on_segment_of_segment_subset_subdifferential
    (x u0 u1 : H) (hseg : segment ℝ u0 u1 ⊆ (∂ f) x) :
    segment ℝ u0 u1 ⊆ effectiveDomain f⋆ ∧
      EqOn
        (fun α : ℝ ↦ (f⋆ (AffineMap.lineMap u0 u1 α) : EReal).toReal)
        (AffineMap.lineMap
          ((f⋆ u0 : EReal).toReal)
          ((f⋆ u1 : EReal).toReal))
        (Icc (0 : ℝ) 1) := by
  constructor
  · -- Every point of the subdifferential fiber gives a finite conjugate value.
    intro z hz
    exact gammaZeroConjugate_mem_effectiveDomain_of_mem_subdifferential
      (f := f) hf (hseg hz)
  · intro α hα
    -- Rewrite the whole trace through the common Fenchel--Young identity along the segment.
    have hu0_sub : u0 ∈ (∂ f) x := by
      exact hseg <| by simpa using left_mem_segment ℝ u0 u1
    have hu1_sub : u1 ∈ (∂ f) x := by
      exact hseg <| by simpa using right_mem_segment ℝ u0 u1
    have hline_sub : AffineMap.lineMap u0 u1 α ∈ (∂ f) x := by
      exact hseg <| by
        rw [segment_eq_image_lineMap]
        exact ⟨α, hα, rfl⟩
    calc
      (f⋆ (AffineMap.lineMap u0 u1 α) : EReal).toReal
          = ⟪x, AffineMap.lineMap u0 u1 α⟫_ℝ - (f x : EReal).toReal :=
            gammaZeroConjugate_toReal_eq_inner_sub_of_mem_subdifferential
              (f := f) hf hline_sub
      _ = (1 - α) * ⟪x, u0⟫_ℝ + α * ⟪x, u1⟫_ℝ - (f x : EReal).toReal := by
            simp [AffineMap.lineMap_apply_module, inner_add_right, inner_smul_right,
              sub_eq_add_neg, add_mul, add_left_comm, add_comm]
      _ = (1 - α) * (⟪x, u0⟫_ℝ - (f x : EReal).toReal) +
            α * (⟪x, u1⟫_ℝ - (f x : EReal).toReal) := by
            ring
      _ = (1 - α) * ((f⋆ u0 : EReal).toReal) + α * ((f⋆ u1 : EReal).toReal) := by
            rw [← gammaZeroConjugate_toReal_eq_inner_sub_of_mem_subdifferential
                  (f := f) hf hu0_sub,
              ← gammaZeroConjugate_toReal_eq_inner_sub_of_mem_subdifferential
                  (f := f) hf hu1_sub]
      _ = AffineMap.lineMap
            ((f⋆ u0 : EReal).toReal)
            ((f⋆ u1 : EReal).toReal) α := by
            simp [AffineMap.lineMap_apply_module, smul_eq_mul, sub_eq_add_neg, add_comm]

-- Proof sketch: choose an interior point `u` on `]u₀,u₁[` with `x ∈ ∂ f*(u)` from the image
-- hypothesis. Theorem 16.29 rewrites this as Fenchel--Young equality at `u`. Affineness of `f*`
-- on the closed segment then forces the same equality at the endpoints `u₀` and `u₁`, so
-- Theorem 16.29 yields `u₀, u₁ ∈ (∂ f) x`. Finally, Proposition 16.4 gives convexity of
-- `(∂ f) x`, hence the whole closed segment lies in `(∂ f) x`.
/-- Proposition 16 37 (2): if the Fenchel conjugate `f*`, represented by `gammaZeroConjugate f hf`,
is finite on `[u₀,u₁]`, its finite-valued trace is affine there, and `x` belongs to the image of
the open segment `]u₀,u₁[` under `∂ f*`, then the entire segment `[u₀,u₁]` is contained in
`∂ f(x)`. -/
theorem segment_subset_subdifferential_of_eq_lineMap_on_segment_of_mem_image_openSegment
    (x u0 u1 : H)
    (hfin : segment ℝ u0 u1 ⊆ effectiveDomain f⋆)
    (haff :
      EqOn
        (fun α : ℝ ↦ (f⋆ (AffineMap.lineMap u0 u1 α) : EReal).toReal)
        (AffineMap.lineMap
          ((f⋆ u0 : EReal).toReal)
          ((f⋆ u1 : EReal).toReal))
        (Icc (0 : ℝ) 1))
    (hint : x ∈ SetValuedOperator.image (∂ f⋆) (openSegment ℝ u0 u1)) :
    segment ℝ u0 u1 ⊆ (∂ f) x := by
  rcases (SetValuedOperator.mem_image (∂ f⋆) (openSegment ℝ u0 u1) x).1 hint with
    ⟨m, hm_open, hxconj⟩
  rw [openSegment_eq_image_lineMap] at hm_open
  rcases hm_open with ⟨α, hα, rfl⟩
  rcases endpoint_mem_subdifferential_of_affine_conjugate_trace
      (f := f) hf hα hfin haff hxconj with ⟨hu0, hu1⟩
  -- Convexity of the subdifferential fiber upgrades endpoint membership to the whole segment.
  exact (convex_subdifferential f x).segment_subset hu0 hu1

end SubdifferentialConjugation

end ERealFunction
