import Mathlib
import BauschkeLean.Chap07.Exercise_7_1
import BauschkeLean.Chap13.Example_13_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace
universe u

namespace ERealFunction

noncomputable section

section Conjugation

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Proposition 13 11: view `H × ℝ` with the `ℓ²` product metric used by epigraph
support-function computations. -/
local instance prod_pseudoMetricSpace_l2 : PseudoMetricSpace (H × ℝ) :=
  WithLp.pseudoMetricSpaceToProd (p := 2) H ℝ

/-- Helper for Proposition 13 11: equip `H × ℝ` with the `ℓ²` product norm coming from
`WithLp 2 (H × ℝ)`. -/
local instance prod_normedAddCommGroup_l2 : NormedAddCommGroup (H × ℝ) :=
  WithLp.normedAddCommGroupToProd (p := 2) H ℝ

/-- Helper for Proposition 13 11: the `ℓ²` product norm on `H × ℝ` is compatible with scalar
multiplication. -/
local instance prod_normedSpace_l2 : NormedSpace ℝ (H × ℝ) := by
  letI : NormedAddCommGroup (H × ℝ) := prod_normedAddCommGroup_l2 (H := H)
  exact WithLp.normedSpaceSeminormedAddCommGroupToProd (p := 2) H ℝ

/-- Helper for Proposition 13 11: the product Hilbert structure on `H × ℝ` is the textbook one
`⟪(x, ξ), (u, μ)⟫ = ⟪x, u⟫ + ξμ`. -/
local instance prod_innerProductSpace_l2 : InnerProductSpace ℝ (H × ℝ) where
  inner x y := ⟪x.1, y.1⟫_ℝ + x.2 * y.2
  norm_sq_eq_re_inner x := by
    rw [show ‖x‖ = ‖WithLp.toLp 2 x‖ by rfl, WithLp.prod_norm_sq_eq_of_L2]
    simp [sq]
  conj_inner_symm x y := by
    simp [real_inner_comm, mul_comm]
  add_left x y z := by
    simp [inner_add_left, add_mul, add_assoc, add_left_comm, add_comm]
  smul_left x y r := by
    simp [inner_smul_left, mul_add, mul_left_comm, mul_comm]

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
/-- Helper for Proposition 13 11: every point of `dom f` lifts to a real-height point of the
epigraph of `f`. -/
private theorem exists_real_mem_epigraph_of_mem_dom
    {f : H → EReal} {x : H} (hx : x ∈ dom f) :
    ∃ ξ : ℝ, (x, ξ) ∈ epigraph f := by
  -- A finite-above value of `f x` admits a real point strictly above it.
  rcases EReal.lt_iff_exists_real_btwn.mp ((mem_dom_iff f x).1 hx) with ⟨ξ, hξ, -⟩
  exact ⟨ξ, (mem_epigraph_iff f x ξ).2 hξ.le⟩

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
/-- Helper for Proposition 13 11: an epigraph point projects to a base point in the effective
domain. -/
private theorem mem_dom_of_mem_epigraph
    {f : H → EReal} {x : H} {ξ : ℝ} (hxξ : (x, ξ) ∈ epigraph f) :
    x ∈ dom f := by
  -- The real ordinate bounds `f x` above by a finite quantity.
  exact (mem_dom_iff f x).2 <| lt_of_le_of_lt ((mem_epigraph_iff f x ξ).1 hxξ) (EReal.coe_lt_top ξ)

/-- Helper for Proposition 13 11: at height `0`, the inner-product image of the epigraph is
exactly the inner-product image of the effective domain. -/
private theorem inner_image_epigraph_zero_eq_inner_image_dom
    (f : H → EReal) (u : H) :
    (fun p : H × ℝ ↦ ((⟪p, (u, 0)⟫_ℝ : ℝ) : EReal)) '' epigraph f =
      (fun x : H ↦ ((⟪x, u⟫_ℝ : ℝ) : EReal)) '' dom f := by
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨p.1, mem_dom_of_mem_epigraph (f := f) hp, ?_⟩
    -- The zero vertical component removes the second-coordinate contribution.
    change ((⟪p.1, u⟫_ℝ : ℝ) : EReal) = ((⟪p, (u, 0)⟫_ℝ : ℝ) : EReal)
    calc
      ((⟪p.1, u⟫_ℝ : ℝ) : EReal) = ((⟪p.1, u⟫_ℝ + p.2 * 0 : ℝ) : EReal) := by
        simp
      _ = ((⟪p, (u, 0)⟫_ℝ : ℝ) : EReal) := by
        rfl
  · rintro ⟨x, hx, rfl⟩
    rcases exists_real_mem_epigraph_of_mem_dom (f := f) hx with ⟨ξ, hξ⟩
    refine ⟨(x, ξ), hξ, ?_⟩
    -- Any epigraph lift of `x` has the same horizontal pairing with `(u, 0)`.
    change ((⟪(x, ξ), (u, 0)⟫_ℝ : ℝ) : EReal) = ((⟪x, u⟫_ℝ : ℝ) : EReal)
    calc
      ((⟪(x, ξ), (u, 0)⟫_ℝ : ℝ) : EReal) = ((⟪x, u⟫_ℝ + ξ * 0 : ℝ) : EReal) := by
        rfl
      _ = ((⟪x, u⟫_ℝ : ℝ) : EReal) := by
        simp

/-- Helper for Proposition 13 11: for positive `μ`, the epigraph support function scales to the
Fenchel conjugate slice from Proposition 13.10. -/
private theorem conjugate_eq_support_function_epigraph_slice
    {f : H → EReal} :
    f∗ = fun u ↦ σ[epigraph f] (u, -1) := by
  funext u
  rw [← conjugate_indicator_eq_supportFunction (C := epigraph f)]
  let B : H × ℝ → EReal := fun p ↦
    ((⟪p, (u, (-1 : ℝ))⟫_ℝ : ℝ) : EReal) -
      (((ι[epigraph f] p : Set.Ioi (⊥ : EReal)) : EReal))
  change (⨆ x : H, ((⟪x, u⟫_ℝ : ℝ) : EReal) - f x) = ⨆ p : H × ℝ, B p
  apply le_antisymm
  · refine iSup_le ?_
    intro x
    by_cases htop : f x = ⊤
    · simp [htop]
    · by_cases hbot : f x = ⊥
      · have hsup_top :
            (⨆ p : H × ℝ, B p) = ⊤ := by
          refine (EReal.eq_top_iff_forall_lt _).2 ?_
          intro M
          let ξ : ℝ := ⟪x, u⟫_ℝ - M - 1
          have hmem : (x, ξ) ∈ epigraph f := by
            rw [mem_epigraph_iff, hbot]
            exact bot_le
          have hvalue : B (x, ξ) = ((M + 1 : ℝ) : EReal) := by
            calc
              B (x, ξ) = ((⟪(x, ξ), (u, (-1 : ℝ))⟫_ℝ : ℝ) : EReal) := by
                simp [B, indicator_apply, hmem]
              _ = ((⟪x, u⟫_ℝ - ξ : ℝ) : EReal) := by
                change (((⟪x, u⟫_ℝ + ξ * (-1) : ℝ)) : EReal) = ((⟪x, u⟫_ℝ - ξ : ℝ) : EReal)
                congr 1
                ring
              _ = ((M + 1 : ℝ) : EReal) := by
                have hreal : ⟪x, u⟫_ℝ - (⟪x, u⟫_ℝ - M - 1) = M + 1 := by
                  ring
                simpa [ξ] using congrArg (fun r : ℝ ↦ (r : EReal)) hreal
          have hlt : (M : EReal) < ((M + 1 : ℝ) : EReal) := by
            exact_mod_cast (show M < M + 1 by linarith)
          exact lt_of_lt_of_le hlt <| by
            rw [← hvalue]
            exact le_iSup B (x, ξ)
        rw [show ((⟪x, u⟫_ℝ : ℝ) : EReal) - f x = ⊤ by simp [hbot]]
        rw [hsup_top]
      · let ξ : ℝ := (f x).toReal
        have hmem : (x, ξ) ∈ epigraph f := by
          rw [mem_epigraph_iff]
          exact EReal.le_coe_toReal htop
        have hξ : ((ξ : ℝ) : EReal) = f x := by
          dsimp [ξ]
          simpa using EReal.coe_toReal htop hbot
        have hpoint :
            ((⟪x, u⟫_ℝ : ℝ) : EReal) - f x =
              B (x, ξ) := by
          calc
            ((⟪x, u⟫_ℝ : ℝ) : EReal) - f x
                = ((⟪x, u⟫_ℝ : ℝ) : EReal) - ((ξ : ℝ) : EReal) := by
                    rw [hξ]
            _ = ((⟪x, u⟫_ℝ - ξ : ℝ) : EReal) := by
                    rw [← EReal.coe_sub]
            _ = B (x, ξ) := by
                calc
                  ((⟪x, u⟫_ℝ - ξ : ℝ) : EReal)
                      = ((⟪(x, ξ), (u, (-1 : ℝ))⟫_ℝ : ℝ) : EReal) := by
                          change ((⟪x, u⟫_ℝ - ξ : ℝ) : EReal) =
                            (((⟪x, u⟫_ℝ + ξ * (-1) : ℝ)) : EReal)
                          congr 1
                          ring
                  _ = B (x, ξ) := by
                          simp [B, indicator_apply, hmem]
        rw [hpoint]
        exact le_iSup B (x, ξ)
  · refine iSup_le ?_
    intro p
    by_cases hp : p ∈ epigraph f
    · have hp_le : f p.1 ≤ (p.2 : EReal) := (mem_epigraph_iff f p.1 p.2).1 hp
      have hp_term :
          B p ≤ ((⟪p.1, u⟫_ℝ : ℝ) : EReal) - f p.1 := by
        by_cases hbot : f p.1 = ⊥
        · rw [show ((⟪p.1, u⟫_ℝ : ℝ) : EReal) - f p.1 = ⊤ by simp [hbot]]
          exact le_top
        · have htop : f p.1 ≠ ⊤ := by
            exact ne_of_lt <| lt_of_le_of_lt hp_le (EReal.coe_lt_top p.2)
          have htoReal_le : (f p.1).toReal ≤ p.2 := by
            simpa using EReal.toReal_le_toReal hp_le hbot (EReal.coe_ne_top p.2)
          have hreal :
              (⟪p.1, u⟫_ℝ - p.2 : ℝ) ≤ ⟪p.1, u⟫_ℝ - (f p.1).toReal :=
            sub_le_sub_left htoReal_le _
          have hcast :
              ((⟪p.1, u⟫_ℝ - p.2 : ℝ) : EReal) ≤
                ((⟪p.1, u⟫_ℝ - (f p.1).toReal : ℝ) : EReal) := by
            exact_mod_cast hreal
          have htoReal : ((((f p.1).toReal : ℝ) : EReal)) = f p.1 := by
            simpa using EReal.coe_toReal htop hbot
          calc
            B p = ((⟪p.1, u⟫_ℝ - p.2 : ℝ) : EReal) := by
              have hpair : ⟪p, (u, (-1 : ℝ))⟫_ℝ = ⟪p.1, u⟫_ℝ - p.2 := by
                change ⟪p.1, u⟫_ℝ + p.2 * (-1 : ℝ) = ⟪p.1, u⟫_ℝ - p.2
                ring
              simp [B, indicator_apply, hp, hpair]
            _ ≤ ((⟪p.1, u⟫_ℝ - (f p.1).toReal : ℝ) : EReal) := hcast
            _ = ((⟪p.1, u⟫_ℝ : ℝ) : EReal) - (((f p.1).toReal : ℝ) : EReal) := by
              rw [← EReal.coe_sub]
            _ = ((⟪p.1, u⟫_ℝ : ℝ) : EReal) - f p.1 := by
              rw [htoReal]
      exact le_trans hp_term <| le_iSup (fun x ↦ ((⟪x, u⟫_ℝ : ℝ) : EReal) - f x) p.1
    · have hp_term : B p = ⊥ := by
        simp [B, indicator_apply, hp]
      rw [hp_term]
      exact bot_le

private theorem supportFunction_epigraph_pos_eq_mul_conjugate
    {f : H → EReal} (u : H) {μ : ℝ} (hμ : 0 < μ) :
    σ[epigraph f] (u, -μ) = (μ : EReal) * f∗ (μ⁻¹ • u) := by
  have hpair : μ • (μ⁻¹ • u, (-1 : ℝ)) = (u, -μ) := by
    -- Scaling the canonical slice `(μ⁻¹ • u, -1)` produces the target point `(u, -μ)`.
    ext
    · simp [smul_smul, hμ.ne']
    · simp
  have hscale :=
    congrFun
      (supportFunction_comp_pos_smul_eq_mul_supportFunction (C := epigraph f) hμ)
      (μ⁻¹ • u, (-1 : ℝ))
  have hconj := congrFun (conjugate_eq_support_function_epigraph_slice (f := f)) (μ⁻¹ • u)
  -- Proposition 13.10 identifies the support function on the `-1` slice with the conjugate.
  rw [← hpair]
  calc
    σ[epigraph f] (μ • (μ⁻¹ • u, (-1 : ℝ))) =
        (μ : EReal) * σ[epigraph f] (μ⁻¹ • u, (-1 : ℝ)) := by
          simpa [Function.comp_apply] using hscale
    _ = (μ : EReal) * f∗ (μ⁻¹ • u) := by
          rw [← hconj]

/-- Helper for Proposition 13 11: on the horizontal slice, the epigraph support function depends
only on the projection onto `dom f`. -/
private theorem supportFunction_epigraph_zero_eq_supportFunction_dom
    {f : H → EReal} (u : H) :
    σ[epigraph f] (u, 0) = σ[dom f] u := by
  -- Rewrite both support functions as suprema of inner-product images.
  rw [supportFunction_eq_sSup_image, supportFunction_eq_sSup_image]
  -- The zero-height image of the epigraph is exactly the image of the effective domain.
  rw [inner_image_epigraph_zero_eq_inner_image_dom]

/-- Helper for Proposition 13 11: when `μ < 0`, the vertical rays in `epigraph f` make the support
functional at `(u, -μ)` exceed any real lower bound. -/
private theorem exists_epigraph_support_value_gt_of_neg
    {f : H → EReal} (hdom : (dom f).Nonempty) (u : H) {μ : ℝ} (hμ : μ < 0) (M : ℝ) :
    ∃ p ∈ epigraph f, (M : EReal) < ((⟪p, (u, -μ)⟫_ℝ : ℝ) : EReal) := by
  rcases hdom with ⟨x0, hx0⟩
  rcases exists_real_mem_epigraph_of_mem_dom (f := f) hx0 with ⟨ξ0, hξ0⟩
  let A : ℝ := ⟪x0, u⟫_ℝ + ξ0 * (-μ)
  let δ : ℝ := |M - A| + 1
  let t : ℝ := δ / (-μ)
  have hμpos : 0 < -μ := by
    linarith
  have hδpos : 0 < δ := by
    -- The offset `δ` is strictly positive so the ray moves upward.
    dsimp [δ]
    positivity
  have ht_nonneg : 0 ≤ t := by
    dsimp [t]
    exact div_nonneg hδpos.le hμpos.le
  have hmul : t * (-μ) = δ := by
    -- The chosen `t` makes the vertical contribution equal to `δ`.
    dsimp [t]
    rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hμpos.ne', mul_one]
  refine ⟨(x0, ξ0 + t), ?_, ?_⟩
  · rw [mem_epigraph_iff] at hξ0 ⊢
    have hξ_le : ((ξ0 : ℝ) : EReal) ≤ ((ξ0 + t : ℝ) : EReal) := by
      exact_mod_cast le_add_of_nonneg_right ht_nonneg
    exact le_trans hξ0 hξ_le
  · apply EReal.coe_lt_coe_iff.mpr
    have hbound : M < A + δ := by
      -- The positive offset `δ = |M - A| + 1` dominates the gap from `A` to `M`.
      have habs : M - A ≤ |M - A| := le_abs_self (M - A)
      linarith
    have hinner :
        ⟪(x0, ξ0 + t), (u, -μ)⟫_ℝ = A + δ := by
      have hA : ⟪x0, u⟫_ℝ + ξ0 * (-μ) = A := rfl
      -- Expanding the product inner product isolates the ray parameter `t`.
      calc
        ⟪(x0, ξ0 + t), (u, -μ)⟫_ℝ = ⟪x0, u⟫_ℝ + (ξ0 + t) * (-μ) := by
          rfl
        _ = ⟪x0, u⟫_ℝ + ξ0 * (-μ) + t * (-μ) := by
          ring
        _ = A + δ := by
          rw [hA, hmul]
    simpa [hinner] using hbound

/-- Helper for Proposition 13 11: a negative vertical weight sends the epigraph support function
to `+∞`. -/
private theorem supportFunction_epigraph_neg_eq_top
    {f : H → EReal} (hdom : (dom f).Nonempty) (u : H) {μ : ℝ} (hμ : μ < 0) :
    σ[epigraph f] (u, -μ) = ⊤ := by
  -- Rewrite the support function as a supremum and realize arbitrarily large values on a ray.
  rw [supportFunction_eq_sSup_image]
  refine (EReal.eq_top_iff_forall_lt _).2 ?_
  intro M
  rcases exists_epigraph_support_value_gt_of_neg (f := f) hdom u hμ M with ⟨p, hp, hM⟩
  exact lt_of_lt_of_le hM ((isLUB_sSup _).1 ⟨p, hp, rfl⟩)

-- Proof sketch: for `μ > 0`, scale the support function and apply Proposition 13.10 (8); for
-- `μ = 0`, only the horizontal component remains, so the support function reduces to that of
-- `dom f`; for `μ < 0`, the upward vertical rays in the epigraph make the support value equal to
-- `+∞`, and nonempty domain rules out the empty-epigraph pathology.
/-- Proposition 13 11: if `dom f` is nonempty, then the support function of the epigraph of `f`,
evaluated at `(u, -μ)` in the Hilbert product space `H × ℝ`, equals `μ f*(u / μ)` for `μ > 0`,
equals the support function of `dom f` for `μ = 0`, and equals `+∞` for `μ < 0`. -/
theorem supportFunction_epigraph_eq
    {f : H → EReal} (hdom : (dom f).Nonempty) (u : H) (μ : ℝ) :
    σ[epigraph f] (u, -μ) =
      if 0 < μ then (μ : EReal) * f∗ (μ⁻¹ • u)
      else if μ = 0 then σ[dom f] u
      else ⊤ := by
  by_cases hμ_pos : 0 < μ
  · -- The positive branch is exactly the scaled `-1` slice from Proposition 13.10.
    simp [hμ_pos, supportFunction_epigraph_pos_eq_mul_conjugate (f := f) u hμ_pos]
  · by_cases hμ_zero : μ = 0
    · -- On the horizontal slice, only the domain projection contributes.
      simpa [hμ_pos, hμ_zero] using supportFunction_epigraph_zero_eq_supportFunction_dom (f := f) u
    · have hμ_neg : μ < 0 := by
        exact lt_of_le_of_ne (le_of_not_gt hμ_pos) hμ_zero
      -- A negative vertical weight sees the unbounded upward rays of the epigraph.
      simp [hμ_pos, hμ_zero, supportFunction_epigraph_neg_eq_top (f := f) hdom u hμ_neg]

/-- Proposition 13.11, positive branch: for `μ > 0`, the support function of the epigraph at
`(u, -μ)` is `μ f*(u / μ)`. -/
theorem supportFunction_epigraph_eq_mul_conjugate_of_pos
    {f : H → EReal} (u : H) {μ : ℝ} (hμ : 0 < μ) :
    σ[epigraph f] (u, -μ) = (μ : EReal) * f∗ (μ⁻¹ • u) := by
  -- This is the positive helper proved directly from the scaling rule.
  exact supportFunction_epigraph_pos_eq_mul_conjugate (f := f) u hμ

/-- Proposition 13.11, zero branch: on the horizontal slice, the support function of the epigraph
reduces to the support function of the effective domain. -/
theorem supportFunction_epigraph_eq_supportFunction_dom_zero
    {f : H → EReal} (u : H) :
    σ[epigraph f] (u, 0) = σ[dom f] u := by
  -- The zero branch is exactly the projection identity for the epigraph image.
  exact supportFunction_epigraph_zero_eq_supportFunction_dom (f := f) u

/-- Proposition 13.11, negative branch: for `μ < 0`, the upward rays in the epigraph force the
support value at `(u, -μ)` to be `+∞`. -/
theorem supportFunction_epigraph_eq_top_of_neg
    {f : H → EReal} (hdom : (dom f).Nonempty) (u : H) {μ : ℝ} (hμ : μ < 0) :
    σ[epigraph f] (u, -μ) = ⊤ := by
  have hnot_pos : ¬ 0 < μ := by
    exact not_lt_of_ge hμ.le
  have hne : μ ≠ 0 := ne_of_lt hμ
  simpa [hnot_pos, hne] using supportFunction_epigraph_eq hdom u μ

end Conjugation

end

end ERealFunction
