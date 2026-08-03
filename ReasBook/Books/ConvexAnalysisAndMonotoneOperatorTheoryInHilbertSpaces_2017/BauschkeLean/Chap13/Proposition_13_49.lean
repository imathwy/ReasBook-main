import Mathlib
import BauschkeLean.Chap07.Definition_7_8
import BauschkeLean.Chap07.Exercise_7_1
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap09.Definition_9_28
import BauschkeLean.Chap09.Proposition_9_30
import BauschkeLean.Chap13.Proposition_13_10
import BauschkeLean.Chap13.Proposition_13_13
import BauschkeLean.Chap13.Proposition_13_12
import BauschkeLean.Chap13.Proposition_13_15
import BauschkeLean.Chap13.Theorem_13_37

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

noncomputable section

section Conjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax
attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

/-- Helper for Proposition 13 49: the canonical product inner product on `H × ℝ` splits into the
horizontal inner product plus the scalar-product contribution. -/
private theorem inner_pair_eq {z w : H × ℝ} :
    ⟪z, w⟫_ℝ = ⟪z.1, w.1⟫_ℝ + z.2 * w.2 := by
  rcases z with ⟨z₁, z₂⟩
  rcases w with ⟨w₁, w₂⟩
  change ⟪z₁, w₁⟫_ℝ + ⟪z₂, w₂⟫_ℝ = ⟪z₁, w₁⟫_ℝ + z₂ * w₂
  have hreal : ⟪z₂, w₂⟫_ℝ = z₂ * w₂ := by
    rw [real_inner_eq_re_inner]
    simp [RCLike.inner_apply, mul_comm]
  simp [hreal]

/-- Helper for Proposition 13 49: a `Γ₀(H)` function has conjugate with nonempty domain in the
noncomplete section. -/
private theorem dom_conjugate_nonempty_of_mem_gammaZero_noncomplete
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    (dom f.asEReal∗).Nonempty := by
  -- Route correction: in the actual textbook hypothesis `H` is Hilbert, so completeness is
  -- available here and the Chapter 13 proper-conjugate theorem gives the dual-domain witness.
  have hproper_f : IsProper f.asEReal := isProper_of_mem_gammaZero hf
  have hgamma_f : f.asEReal ∈ gamma H := asEReal_mem_gamma_of_mem_gammaZero hf
  exact (conjugate_is_proper_of_mem_gamma hproper_f hgamma_f).2

/-- Helper for Proposition 13 49: the canonical Fenchel conjugate of a `Γ₀(H)` function is
proper. -/
private theorem gammaZeroConjugate_isProper
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    IsProper f.asEReal∗ := by
  -- Route correction: the noncomplete section cannot use `Theorem_13_37`; this proof needs an
  -- earlier dependency-closed dual witness showing `dom f.asEReal∗` is nonempty from `hf`.
  refine ⟨fun u ↦ conjugate_ne_bot_of_isProper (isProper_of_mem_gammaZero hf) u, ?_⟩
  exact dom_conjugate_nonempty_of_mem_gammaZero_noncomplete f hf

/-- Helper for Proposition 13 49: the canonical `Γ₀(H)` Fenchel conjugate, packaged back into
`]-∞,+∞]`. -/
noncomputable abbrev gammaZeroConjugate
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    H → Set.Ioi (⊥ : EReal) :=
  properIoi (f.asEReal∗) (gammaZeroConjugate_isProper f hf)

/-- Helper for Proposition 13 49: coercing the packaged Fenchel conjugate back to `EReal`
recovers the raw conjugate. -/
@[simp] theorem gammaZeroConjugate_apply
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (u : H) :
    (gammaZeroConjugate f hf u : EReal) = f.asEReal∗ u :=
  rfl

/-- Helper for Proposition 13 49: packaging the Fenchel conjugate through `properIoi` yields a
member of `Γ₀(H)`. -/
theorem gammaZeroConjugate_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    gammaZeroConjugate f hf ∈ Γ₀(H) := by
  exact properIoi_mem_gammaZero_of_mem_gamma
    (gammaZeroConjugate_isProper f hf)
    (conjugate_mem_gamma f.asEReal)

/-- Helper for Proposition 13 49: a real-height epigraph point of `f.asEReal` projects to the
effective domain of `f`. -/
private theorem mem_effectiveDomain_of_mem_epigraph_asEReal
    {f : H → Set.Ioi (⊥ : EReal)} {x : H} {ξ : ℝ}
    (hxξ : (x, ξ) ∈ epigraph f.asEReal) :
    x ∈ effectiveDomain f := by
  -- The real epigraph height is strictly below `⊤`, so it forces the base point into the domain.
  rw [mem_effectiveDomain_iff]
  exact lt_of_le_of_lt ((mem_epigraph_iff f.asEReal x ξ).mp hxξ) (EReal.coe_lt_top ξ)

/-- Helper for Proposition 13 49: every effective-domain point of `f` lifts to a real-height point
of `epigraph f.asEReal`. -/
private theorem exists_real_mem_epigraph_asEReal_of_mem_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} {x : H} (hx : x ∈ effectiveDomain f) :
    ∃ ξ : ℝ, (x, ξ) ∈ epigraph f.asEReal := by
  -- Choose any real number strictly between the finite value `f x` and `⊤`.
  rcases EReal.lt_iff_exists_real_btwn.mp (mem_effectiveDomain_iff.mp hx) with ⟨ξ, hξ, _⟩
  exact ⟨ξ, (mem_epigraph_iff f.asEReal x ξ).2 hξ.le⟩

/-- Helper for Proposition 13 49: Proposition 13.11 identifies the zero-height slice of the
epigraph support function of `f.asEReal` with the support function of `effectiveDomain f`. -/
private theorem supportFunction_epigraph_asEReal_zero_eq_supportFunction_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (u : H) :
    σ[epigraph f.asEReal] (u, 0) = σ[effectiveDomain f] u := by
  -- Route correction: prove the Proposition 13.11 zero-slice identity directly at the support
  -- function level to avoid importing the conflicting owner file.
  rw [supportFunction_eq_sSup_image, supportFunction_eq_sSup_image]
  congr 1
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨p.1, mem_effectiveDomain_of_mem_epigraph_asEReal (f := f) hp, ?_⟩
    change ((⟪p.1, u⟫_ℝ : ℝ) : EReal) = ((⟪p, (u, 0)⟫_ℝ : ℝ) : EReal)
    calc
      ((⟪p.1, u⟫_ℝ : ℝ) : EReal) = ((⟪p.1, u⟫_ℝ + p.2 * 0 : ℝ) : EReal) := by simp
      _ = ((⟪p, (u, 0)⟫_ℝ : ℝ) : EReal) := by rw [inner_pair_eq]
  · rintro ⟨x, hx, rfl⟩
    rcases exists_real_mem_epigraph_asEReal_of_mem_effectiveDomain (f := f) hx with ⟨ξ, hξ⟩
    refine ⟨(x, ξ), hξ, ?_⟩
    change ((⟪(x, ξ), (u, 0)⟫_ℝ : ℝ) : EReal) = ((⟪x, u⟫_ℝ : ℝ) : EReal)
    calc
      ((⟪(x, ξ), (u, 0)⟫_ℝ : ℝ) : EReal) = ((⟪x, u⟫_ℝ + ξ * 0 : ℝ) : EReal) := by
        rw [inner_pair_eq]
      _ = ((⟪x, u⟫_ℝ : ℝ) : EReal) := by simp

/-- Helper for Proposition 13 49: every positive epigraph support slice of `f.asEReal` equals the
corresponding scaled Fenchel conjugate value. -/
private theorem supportFunction_epigraph_asEReal_neg_one_eq_conjugate
    (f : H → Set.Ioi (⊥ : EReal)) (u : H) :
    σ[epigraph f.asEReal] (u, -1) = f.asEReal∗ u := by
  -- Re-express the `-1` slice through the same affine-defect supremum as Proposition 13.10.
  calc
    σ[epigraph f.asEReal] (u, -1) =
        sSup ((fun p : H × ℝ ↦ ((⟪p.1, u⟫_ℝ - p.2 : ℝ) : EReal)) '' epigraph f.asEReal) := by
          rw [supportFunction_eq_sSup_image]
          congr 1
          ext z
          constructor
          · rintro ⟨p, hp, rfl⟩
            refine ⟨p, hp, ?_⟩
            have hpair : ⟪p, (u, (-1 : ℝ))⟫_ℝ = ⟪p.1, u⟫_ℝ - p.2 := by
              rw [inner_pair_eq]
              ring
            simp [hpair]
          · rintro ⟨p, hp, rfl⟩
            refine ⟨p, hp, ?_⟩
            have hpair : ⟪p, (u, (-1 : ℝ))⟫_ℝ = ⟪p.1, u⟫_ℝ - p.2 := by
              rw [inner_pair_eq]
              ring
            simp [hpair]
    _ = f.asEReal∗ u := by
          simpa using (conjugate_eq_sSup_image_epigraph (f := f.asEReal) u).symm

/-- Helper for Proposition 13 49: every positive epigraph support slice of `f.asEReal` equals the
corresponding scaled Fenchel conjugate value. -/
private theorem supportFunction_epigraph_asEReal_eq_mul_conjugate_of_pos
    (f : H → Set.Ioi (⊥ : EReal)) (u : H) {μ : ℝ} (hμ : 0 < μ) :
    σ[epigraph f.asEReal] (u, -μ) = (μ : EReal) * f.asEReal∗ (μ⁻¹ • u) := by
  -- Route correction: recover the positive slice directly from Proposition 13.10 and the Chapter
  -- 7 support-function scaling identity, avoiding the conflicting Proposition 13.11 owner file.
  have hpair : μ • (μ⁻¹ • u, (-1 : ℝ)) = (u, -μ) := by
    -- Scaling the canonical `-1` slice produces the requested positive-height slice.
    ext
    · simp [smul_smul, hμ.ne']
    · simp
  have hscale :=
    congrFun
      (supportFunction_comp_pos_smul_eq_mul_supportFunction (C := epigraph f.asEReal) hμ)
      (μ⁻¹ • u, (-1 : ℝ))
  -- Proposition 13.10 identifies the support function on the `-1` slice with the conjugate.
  rw [← hpair]
  calc
    σ[epigraph f.asEReal] (μ • (μ⁻¹ • u, (-1 : ℝ))) =
        (μ : EReal) * σ[epigraph f.asEReal] (μ⁻¹ • u, (-1 : ℝ)) := by
          simpa [Function.comp_apply] using hscale
    _ = (μ : EReal) * f.asEReal∗ (μ⁻¹ • u) := by
          rw [supportFunction_epigraph_asEReal_neg_one_eq_conjugate]

/-- Helper for Proposition 13 49: along the reciprocal ray approaching the zero slice, the
epigraph support function equals the scaled value from Proposition 9.30 for `f*`. -/
private theorem supportFunction_epigraph_asEReal_reciprocal_ray_eq_scaled_gammaZeroConjugate
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (u x : H) (α : Set.Ioi (0 : ℝ)) :
    σ[epigraph f.asEReal] (u + ((α : ℝ)⁻¹) • x, -((α : ℝ)⁻¹)) =
      (gammaZeroConjugate f hf (x + (α : ℝ) • u) : EReal) / (α : ℝ) := by
  have hα_pos : 0 < (α : ℝ) := by
    exact α.2
  have hα_ne : (α : ℝ) ≠ 0 := ne_of_gt hα_pos
  have hαinv_pos : 0 < ((α : ℝ)⁻¹) := by
    simpa [one_div] using (one_div_pos.mpr hα_pos)
  have harg :
      (((α : ℝ)⁻¹)⁻¹) • (u + ((α : ℝ)⁻¹) • x) = x + (α : ℝ) • u := by
    simp [smul_add, smul_smul, hα_ne, add_comm]
  -- Rewrite the positive slice using Proposition 13.10 and then normalize the reciprocal scalar.
  calc
    σ[epigraph f.asEReal] (u + ((α : ℝ)⁻¹) • x, -((α : ℝ)⁻¹)) =
        (((α : ℝ)⁻¹ : ℝ) : EReal) *
          f.asEReal∗ ((((α : ℝ)⁻¹)⁻¹) • (u + ((α : ℝ)⁻¹) • x)) := by
          rw [supportFunction_epigraph_asEReal_eq_mul_conjugate_of_pos
            (f := f) (u := u + ((α : ℝ)⁻¹) • x) (μ := (α : ℝ)⁻¹) hαinv_pos]
    _ = (((α : ℝ)⁻¹ : ℝ) : EReal) * f.asEReal∗ (x + (α : ℝ) • u) := by
          rw [harg]
    _ = (f.asEReal∗ (x + (α : ℝ) • u)) / (α : ℝ) := by
          rw [div_eq_mul_inv, EReal.coe_inv]
          simp [mul_comm]
    _ = (gammaZeroConjugate f hf (x + (α : ℝ) • u) : EReal) / (α : ℝ) := by
          rw [gammaZeroConjugate_apply]

/-- Helper for Proposition 13 49: the support function of `epigraph f.asEReal` is lower
semicontinuous because it is the conjugate of the epigraph indicator. -/
private theorem lowerSemicontinuous_supportFunction_epigraph_asEReal
    (f : H → Set.Ioi (⊥ : EReal)) :
    LowerSemicontinuous (fun p : H × ℝ ↦ σ[epigraph f.asEReal] p) := by
  have hgamma : ((ι[epigraph f.asEReal]).asEReal)∗ ∈ Γ(H × ℝ) := by
    -- The conjugate of any extended-real function belongs to `Γ`.
    exact conjugate_mem_gamma ((ι[epigraph f.asEReal]).asEReal)
  -- Rewrite the support function as that conjugate and read off lower semicontinuity.
  rw [← conjugate_indicator_eq_supportFunction (C := epigraph f.asEReal)]
  exact (mem_gamma_iff _).mp hgamma |>.2

/-- Helper for Proposition 13 49: a finite value of `gammaZeroConjugate f hf` gives the
corresponding real-height point in the epigraph of `f.asEReal∗`. -/
private theorem gammaZeroConjugate_toReal_mem_epigraph_conjugate
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    {y : H} (hy : y ∈ effectiveDomain (gammaZeroConjugate f hf)) :
    (y, ((gammaZeroConjugate f hf y : EReal).toReal)) ∈ epigraph (f.asEReal∗) := by
  -- Effective-domain membership is exactly the finiteness needed to place the conjugate value in
  -- the real-height epigraph.
  rw [mem_epigraph_iff]
  have hy_top : (gammaZeroConjugate f hf y : EReal) ≠ ⊤ :=
    ne_of_lt (mem_effectiveDomain_iff.mp hy)
  simpa [gammaZeroConjugate_apply] using EReal.le_coe_toReal hy_top

/-- Helper for Proposition 13 49: adding one extra pairing term to an affine defect over
`f.asEReal` changes only the horizontal part of that defect. -/
private theorem affine_defect_add_inner
    {f : H → Set.Ioi (⊥ : EReal)} (x y u : H) :
    (((⟪x, y + u⟫_ℝ : ℝ) : EReal) - f.asEReal x) =
      (((⟪x, u⟫_ℝ : ℝ) : EReal) +
        (((⟪x, y⟫_ℝ : ℝ) : EReal) - f.asEReal x)) := by
  -- Reassociate the affine defect as addition by `-f x`, then split the pairing in the second
  -- argument.
  have hinner :
      (((⟪x, y + u⟫_ℝ : ℝ) : EReal)) =
        (((⟪x, u⟫_ℝ : ℝ) : EReal) + ((⟪x, y⟫_ℝ : ℝ) : EReal)) := by
    have hreal : ⟪x, y + u⟫_ℝ = ⟪x, u⟫_ℝ + ⟪x, y⟫_ℝ := by
      calc
        ⟪x, y + u⟫_ℝ = ⟪x, y⟫_ℝ + ⟪x, u⟫_ℝ := by
          rw [inner_add_right]
        _ = ⟪x, u⟫_ℝ + ⟪x, y⟫_ℝ := by simp [add_comm]
    rw [hreal, EReal.coe_add]
  rw [hinner, sub_eq_add_neg, sub_eq_add_neg]
  simp [add_assoc, add_comm]

/-- Helper for Proposition 13 49: Proposition 13.12 yields the additive translated estimate
`f*(y + u) ≤ σ[dom f] u + f*(y)` once `f* y` is finite. -/
private theorem gammaZeroConjugate_add_le_supportFunction_effectiveDomain_add
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (y u : H) (hy : y ∈ effectiveDomain (gammaZeroConjugate f hf)) :
    (gammaZeroConjugate f hf (y + u) : EReal) ≤
      σ[effectiveDomain f] u + (gammaZeroConjugate f hf y : EReal) := by
  -- Route correction: use Proposition 13.12 at the finite epigraph point
  -- `(y, (gammaZeroConjugate f hf y).toReal)` instead of expanding affine defects globally.
  have hy_bot : (gammaZeroConjugate f hf y : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (gammaZeroConjugate f hf y : EReal) from
      (gammaZeroConjugate f hf y).2)
  have hy_top : (gammaZeroConjugate f hf y : EReal) ≠ ⊤ :=
    ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hminorant :
      ∀ x : H,
        (((⟪x, y⟫_ℝ - ((gammaZeroConjugate f hf y : EReal).toReal) : ℝ) : EReal) ≤ f.asEReal x) :=
    (mem_epigraph_conjugate_iff (f := f.asEReal) y
      ((gammaZeroConjugate f hf y : EReal).toReal)).1
      (gammaZeroConjugate_toReal_mem_epigraph_conjugate (f := f) hf hy)
  have hdefect_y :
      ∀ x : H,
        (((⟪x, y⟫_ℝ : ℝ) : EReal) - f.asEReal x) ≤
          (gammaZeroConjugate f hf y : EReal) := by
    intro x
    have htoReal :
        (((⟪x, y⟫_ℝ : ℝ) : EReal) - f.asEReal x) ≤
          ((((gammaZeroConjugate f hf y : EReal).toReal : ℝ) : EReal)) :=
      (affine_defect_le_real_iff (f := f.asEReal) x y
        ((gammaZeroConjugate f hf y : EReal).toReal)).2
        (hminorant x)
    calc
      (((⟪x, y⟫_ℝ : ℝ) : EReal) - f.asEReal x)
          ≤ ((((gammaZeroConjugate f hf y : EReal).toReal : ℝ) : EReal)) := htoReal
      _ = (gammaZeroConjugate f hf y : EReal) := by
            rw [EReal.coe_toReal hy_top hy_bot]
  rw [gammaZeroConjugate_apply, conjugate_apply]
  refine iSup_le fun x ↦ ?_
  by_cases hx : x ∈ effectiveDomain f
  · -- Finite points of `f` contribute a support-function bound on the added pairing term.
    have hsupport :
        (((⟪x, u⟫_ℝ : ℝ) : EReal)) ≤ σ[effectiveDomain f] u := by
      rw [supportFunction_eq_sSup_image]
      exact (isLUB_sSup _).1 ⟨x, hx, rfl⟩
    calc
      (((⟪x, y + u⟫_ℝ : ℝ) : EReal) - f.asEReal x)
          = (((⟪x, u⟫_ℝ : ℝ) : EReal) +
              (((⟪x, y⟫_ℝ : ℝ) : EReal) - f.asEReal x)) := by
                simpa using affine_defect_add_inner (f := f) x y u
      _ ≤ σ[effectiveDomain f] u + (gammaZeroConjugate f hf y : EReal) := by
            exact add_le_add hsupport (hdefect_y x)
  · -- Outside the effective domain of `f`, the affine defect is `-∞`, so the estimate is
    -- immediate.
    have hxtop : f.asEReal x = ⊤ := by
      exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hx))
    have hbot :
        (((⟪x, y + u⟫_ℝ : ℝ) : EReal) - f.asEReal x) = ⊥ := by
      simp [hxtop]
    rw [hbot]
    exact bot_le

/-- Helper for Proposition 13 49: every translated increment of the canonical conjugate is bounded
by the support function of `effectiveDomain f`. -/
private theorem gammaZeroConjugate_increment_le_supportFunction_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (y u : H) (hy : y ∈ effectiveDomain (gammaZeroConjugate f hf)) :
    ((gammaZeroConjugate f hf (y + u) : EReal) - (gammaZeroConjugate f hf y : EReal)) ≤
      σ[effectiveDomain f] u := by
  -- Rewrite the additive estimate into subtraction form using the finiteness of `f* y`.
  have hy_bot : (gammaZeroConjugate f hf y : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (gammaZeroConjugate f hf y : EReal) from
      (gammaZeroConjugate f hf y).2)
  have hy_top : (gammaZeroConjugate f hf y : EReal) ≠ ⊤ :=
    ne_of_lt (mem_effectiveDomain_iff.mp hy)
  exact
    (EReal.sub_le_iff_le_add (Or.inl hy_bot) (Or.inl hy_top)).2
      (by
        simpa [add_comm] using
          gammaZeroConjugate_add_le_supportFunction_effectiveDomain_add
            (f := f) hf y u hy)

/-- Helper for Proposition 13 49: the recession function of `gammaZeroConjugate f hf` is
pointwise bounded above by `σ[effectiveDomain f]`. -/
private theorem recessionFunction_gammaZeroConjugate_le_supportFunction_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (u : H) :
    (recessionFunction (gammaZeroConjugate f hf)
      (gammaZeroConjugate_mem_gammaZero hf).2.nonempty u : EReal) ≤
      σ[effectiveDomain f] u := by
  -- Every translated increment appearing in the recession supremum satisfies the increment bound.
  rw [recessionFunction_apply]
  refine sSup_le ?_
  rintro _ ⟨y, hy, rfl⟩
  exact gammaZeroConjugate_increment_le_supportFunction_effectiveDomain f hf y u hy

/-- Helper for Proposition 13 49: the zero-height epigraph support slice is bounded above by the
recession function of the canonical conjugate. -/
private theorem supportFunction_epigraph_asEReal_zero_le_recessionFunction_gammaZeroConjugate
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (u : H) :
    σ[epigraph f.asEReal] (u, 0) ≤
      (recessionFunction (gammaZeroConjugate f hf)
        (gammaZeroConjugate_mem_gammaZero hf).2.nonempty u : EReal) := by
  rcases (gammaZeroConjugate_mem_gammaZero hf).2.nonempty with ⟨x, hx⟩
  have hcoe :
      Filter.Tendsto (fun α : Set.Ioi (0 : ℝ) ↦ (α : ℝ)) Filter.atTop Filter.atTop := by
    simpa [Filter.Tendsto] using (Filter.map_val_Ioi_atTop (0 : ℝ))
  have hinv :
      Filter.Tendsto (fun α : Set.Ioi (0 : ℝ) ↦ ((α : ℝ)⁻¹))
        Filter.atTop (nhds (0 : ℝ)) := by
    simpa only [Function.comp_def] using (tendsto_inv_atTop_zero.comp hcoe)
  have hpath :
      Filter.Tendsto
        (fun α : Set.Ioi (0 : ℝ) ↦ (u + ((α : ℝ)⁻¹) • x, -((α : ℝ)⁻¹)))
        Filter.atTop (nhds (u, 0)) := by
    have hfirst :
        Filter.Tendsto
          (fun α : Set.Ioi (0 : ℝ) ↦ u + ((α : ℝ)⁻¹) • x)
          Filter.atTop (nhds (u + (0 : ℝ) • x)) := by
      -- The reciprocal perturbation vanishes, so the horizontal component tends back to `u`.
      exact tendsto_const_nhds.add (hinv.smul tendsto_const_nhds)
    have hsecond :
        Filter.Tendsto
          (fun α : Set.Ioi (0 : ℝ) ↦ -((α : ℝ)⁻¹))
          Filter.atTop (nhds (-(0 : ℝ))) := by
      -- The vertical component is just the negative reciprocal.
      exact hinv.neg
    simpa using hfirst.prodMk_nhds hsecond
  have hscaled :
      Filter.Tendsto
        (fun α : Set.Ioi (0 : ℝ) ↦
          (gammaZeroConjugate f hf (x + (α : ℝ) • u) : EReal) / (α : ℝ))
        Filter.atTop
        (nhds ((recessionFunction (gammaZeroConjugate f hf)
          (gammaZeroConjugate_mem_gammaZero hf).2.nonempty u : EReal))) := by
    -- Proposition 9.30 identifies the scaled values of `f*` along the ray `x + α • u`.
    exact tendsto_scaled_ray_values_to_recessionFunction
      (f := gammaZeroConjugate f hf) (hf := gammaZeroConjugate_mem_gammaZero hf) (hx := hx) u
  have hrewrite :
      (fun α : Set.Ioi (0 : ℝ) ↦
        σ[epigraph f.asEReal] (u + ((α : ℝ)⁻¹) • x, -((α : ℝ)⁻¹))) =
        fun α : Set.Ioi (0 : ℝ) ↦
          (gammaZeroConjugate f hf (x + (α : ℝ) • u) : EReal) / (α : ℝ) := by
    -- The reciprocal-ray slice is exactly the scaled conjugate value from the previous helper.
    funext α
    exact
      supportFunction_epigraph_asEReal_reciprocal_ray_eq_scaled_gammaZeroConjugate
        f hf u x α
  calc
    σ[epigraph f.asEReal] (u, 0) ≤
        Filter.liminf (fun p : H × ℝ ↦ σ[epigraph f.asEReal] p) (nhds (u, 0)) := by
          exact (lowerSemicontinuous_supportFunction_epigraph_asEReal (f := f)).le_liminf (u, 0)
    _ ≤
        Filter.liminf
          (fun α : Set.Ioi (0 : ℝ) ↦
            σ[epigraph f.asEReal] (u + ((α : ℝ)⁻¹) • x, -((α : ℝ)⁻¹)))
          Filter.atTop := by
          simpa [Filter.liminf_comp] using
            (Filter.liminf_le_liminf_of_le hpath :
              Filter.liminf (fun p : H × ℝ ↦ σ[epigraph f.asEReal] p) (nhds (u, 0)) ≤
                Filter.liminf
                  (fun p : H × ℝ ↦ σ[epigraph f.asEReal] p)
                  (Filter.map
                    (fun α : Set.Ioi (0 : ℝ) ↦
                      (u + ((α : ℝ)⁻¹) • x, -((α : ℝ)⁻¹)))
                    Filter.atTop))
    _ = (recessionFunction (gammaZeroConjugate f hf)
          (gammaZeroConjugate_mem_gammaZero hf).2.nonempty u : EReal) := by
          rw [hrewrite]
          exact hscaled.liminf_eq

-- Proof sketch: apply Proposition 13.11 to the support function of the epigraph of the
-- `EReal`-valued coercion of `f`, identify the zero-height slice with the recession function of
-- `f*`, and rewrite the remaining support term as the support function of `effectiveDomain f`.
/-- Proposition 13.49 (1): for `f ∈ Γ₀(ℋ)`, the recession function of the Fenchel conjugate `f*`
coincides with the support function of the effective domain of `f`. -/
theorem recessionFunction_gammaZeroConjugate_eq_supportFunction_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    (recessionFunction (gammaZeroConjugate f hf)
      (gammaZeroConjugate_mem_gammaZero hf).2.nonempty).asEReal =
      σ[effectiveDomain f] := by
  ext u
  apply le_antisymm
  · -- The translated-increment estimate gives the easy inequality directly from the definition.
    exact recessionFunction_gammaZeroConjugate_le_supportFunction_effectiveDomain f hf u
  · -- TODO: finish the source zero-slice route by proving the lower bound helper below:
    -- rewrite `σ[effectiveDomain f] u` as the zero-height slice of `σ[epigraph f.asEReal]`, then
    -- compare that slice with the scaled-ray limit defining `recessionFunction (gammaZeroConjugate f hf)`.
    calc
      σ[effectiveDomain f] u = σ[epigraph f.asEReal] (u, 0) := by
        symm
        exact supportFunction_epigraph_asEReal_zero_eq_supportFunction_effectiveDomain f u
      _ ≤
          (recessionFunction (gammaZeroConjugate f hf)
            (gammaZeroConjugate_mem_gammaZero hf).2.nonempty u : EReal) :=
        supportFunction_epigraph_asEReal_zero_le_recessionFunction_gammaZeroConjugate f hf u

end Conjugation

section FenchelMoreau

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Proposition 13 49: the Fenchel biconjugate of a `Γ₀(H)` function agrees with its
canonical `EReal` coercion. -/
private theorem biconjugate_eq_of_mem_gammaZero_local
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    f.asEReal∗∗ = f.asEReal := by
  have hproper_f : IsProper f.asEReal := isProper_of_mem_gammaZero hf
  have hgamma_f : f.asEReal ∈ gamma H := asEReal_mem_gamma_of_mem_gammaZero hf
  exact (mem_gamma_iff_eq_biconjugate_of_is_proper hproper_f).mp hgamma_f

/-- Helper for Proposition 13 49: the Fenchel conjugate of the packaged conjugate evaluates to
the original `EReal`-valued function. -/
private theorem gammaZeroConjugate_biconjugate_eval
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (y : H) :
    (gammaZeroConjugate f hf).asEReal∗ y = (f y : EReal) := by
  -- Rewrite the packaged conjugate back to the raw conjugate, then apply Fenchel--Moreau.
  have hbiconj : f.asEReal∗∗ y = f.asEReal y :=
    congrFun (biconjugate_eq_of_mem_gammaZero_local f hf) y
  simpa [gammaZeroConjugate_apply, Function.asEReal] using hbiconj

/-- Helper for Proposition 13 49: the canonical `Γ₀(H)` Fenchel conjugate is involutive on
`Γ₀(H)`. -/
theorem gammaZeroConjugate_gammaZeroConjugate
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    gammaZeroConjugate (gammaZeroConjugate f hf) (gammaZeroConjugate_mem_gammaZero hf) = f := by
  ext x
  simpa [Function.asEReal] using congrFun (biconjugate_eq_of_mem_gammaZero_local f hf) x

-- Proof sketch: apply clause (1) to `g := gammaZeroConjugate f hf`, use Corollary 13.40 to
-- identify `g*` with `f`, and then rewrite the `EReal`-valued recession function through
-- `recessionFunction_apply`.
/-- Proposition 13.49 (2): for `f ∈ Γ₀(ℋ)`, the recession function of `f` coincides with the
support function of the effective domain of its Fenchel conjugate `f*`. -/
theorem recessionFunction_eq_supportFunction_effectiveDomain_gammaZeroConjugate
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    (recessionFunction f hf.2.nonempty).asEReal =
      σ[effectiveDomain (gammaZeroConjugate f hf)] := by
  have hdouble :
      gammaZeroConjugate (gammaZeroConjugate f hf) (gammaZeroConjugate_mem_gammaZero hf) = f := by
    exact gammaZeroConjugate_gammaZeroConjugate f hf
  ext u
  simpa [Function.asEReal, recessionFunction_apply, hdouble] using
    congrFun
      (recessionFunction_gammaZeroConjugate_eq_supportFunction_effectiveDomain
        (gammaZeroConjugate f hf) (gammaZeroConjugate_mem_gammaZero hf))
      u

end FenchelMoreau

end

end ERealFunction
