import Mathlib
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap12.Proposition_12_14
import BauschkeLean.Chap12.Definition_12_20
import BauschkeLean.Chap12.Proposition_12_15
import BauschkeLean.Chap13.Definition_13_1
import BauschkeLean.Chap13.GammaZeroConjugate
import BauschkeLean.Chap13.Proposition_13_24

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

/- Source/core/bridge triage:
- `source-facing`: Proposition 14.1 identifies the Fenchel conjugate of `f + γ q` with the
  `γ`-Moreau envelope of `f*` and records exactness of the defining infimal convolution.
- `core/canonical`: the owner abstractions are `halfSquaredNorm.asEReal`, `{}^[γ] f`, and
  `infimalConvolution.Exact`.
- `bridge/view`: `gammaZeroConjugate f hf` is only the canonical `Γ₀(H)`-valued packaging of
  `f∗`, so it should be used through those owner abstractions rather than through a parallel local
  wrapper API. -/

section MoreauDecomposition

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 14 1: the `p = 2` norm-power kernel is exactly the quadratic Moreau
kernel. -/
private theorem normPowerKernel_two_eq_moreauQuadraticKernel_local
    (γ : Set.Ioi (0 : ℝ)) :
    (normPowerKernel (H := H) ⟨(2 : ℝ), by norm_num⟩ γ : H → Set.Ioi (⊥ : EReal)) =
      moreauQuadraticKernel (H := H) γ := by
  ext x
  have hγ0 : (γ : ℝ) ≠ 0 := ne_of_gt γ.2
  have hreal :
      ‖x‖ ^ (2 : ℕ) / ((γ : ℝ) * 2) = (1 / (2 * (γ : ℝ))) * ‖x‖ ^ 2 := by
    field_simp [hγ0]
  simpa [normPowerKernel_apply, moreauQuadraticKernel_apply, Real.rpow_natCast] using
    congrArg (fun r : ℝ ↦ (r : EReal)) hreal

omit [CompleteSpace H] in
/-- Helper for Proposition 14 1: the Moreau quadratic kernel belongs to `Γ₀(H)` because it is
the canonical `p = 2` norm-power kernel. -/
private theorem moreauQuadraticKernel_mem_gammaZero_local
    (γ : Set.Ioi (0 : ℝ)) :
    moreauQuadraticKernel (H := H) γ ∈ Γ₀(H) := by
  let pTwo : Set.Ici (1 : ℝ) := ⟨(2 : ℝ), by norm_num⟩
  have hpTwo : (1 : ℝ) < pTwo := by
    change (1 : ℝ) < (2 : ℝ)
    norm_num
  have hkernel_eq :
      normPowerKernel (H := H) pTwo γ = moreauQuadraticKernel (H := H) γ := by
    simpa [pTwo] using normPowerKernel_two_eq_moreauQuadraticKernel_local (H := H) γ
  -- Route correction: reuse the canonical `p = 2` Chapter 12 kernel owner instead of reproving
  -- convexity and lower semicontinuity for the quadratic kernel from scratch.
  simpa [hkernel_eq] using normPowerKernel_mem_gammaZero (H := H) pTwo γ hpTwo

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 14 1: the Moreau quadratic kernel is supercoercive because it is the
`p = 2` norm-power kernel. -/
private theorem supercoercive_moreauQuadraticKernel_local
    (γ : Set.Ioi (0 : ℝ)) :
    Supercoercive ((moreauQuadraticKernel (H := H) γ : H → Set.Ioi (⊥ : EReal)).asEReal) := by
  let pTwo : Set.Ici (1 : ℝ) := ⟨(2 : ℝ), by norm_num⟩
  have hpTwo : (1 : ℝ) < pTwo := by
    change (1 : ℝ) < (2 : ℝ)
    norm_num
  have hkernel_eq :
      normPowerKernel (H := H) pTwo γ = moreauQuadraticKernel (H := H) γ := by
    simpa [pTwo] using normPowerKernel_two_eq_moreauQuadraticKernel_local (H := H) γ
  -- Route correction: import the supercoercive `p`-power kernel theorem and specialize to `p=2`
  -- instead of rebuilding the growth estimate in this file.
  simpa [hkernel_eq] using supercoercive_normPowerKernel (H := H) pTwo γ hpTwo

/-- Helper for Proposition 14 1: the Moreau envelope of the canonical conjugate is proper and
belongs to `gamma H`. -/
private theorem moreauEnvelope_gammaZeroConjugate_isProper_and_mem_gamma
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (γ : Set.Ioi (0 : ℝ)) :
    IsProper ({}^[γ] (gammaZeroConjugate f hf)) ∧
      ({}^[γ] (gammaZeroConjugate f hf)) ∈ gamma H := by
  have hconj : gammaZeroConjugate f hf ∈ Γ₀(H) :=
    gammaZeroConjugate_mem_gammaZero hf
  have hkernel : moreauQuadraticKernel γ ∈ Γ₀(H) :=
    moreauQuadraticKernel_mem_gammaZero_local (H := H) γ
  have hsuper :
      Supercoercive ((moreauQuadraticKernel (H := H) γ : H → Set.Ioi (⊥ : EReal)).asEReal) :=
    supercoercive_moreauQuadraticKernel_local (H := H) γ
  -- Proposition 12.14 applies once the supercoercive quadratic kernel is moved to the first slot.
  simpa [moreauEnvelope, infimalConvolution_comm] using
    isProper_and_mem_gamma_infimalConvolution_of_supercoercive_or_coercive_bddBelow
      (f := moreauQuadraticKernel γ)
      (g := gammaZeroConjugate f hf)
      (hf := hkernel)
      (hg := hconj)
      (hcase := Or.inl hsuper)

omit [CompleteSpace H] in
/-- Helper for Proposition 14 1: coercing the packaged canonical conjugate back to `EReal`
recovers the Fenchel conjugate of `f`. -/
private theorem gammaZeroConjugate_asEReal_eq_conjugate
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    (gammaZeroConjugate f hf).asEReal = f.asEReal∗ :=
  rfl

/-- Helper for Proposition 14 1: conjugating the Moreau envelope of `f*` yields
`f + γ q`. -/
private theorem conjugate_moreauEnvelope_gammaZeroConjugate_eq_add_scaledQuadratic
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (γ : Set.Ioi (0 : ℝ)) :
    ({}^[γ] (gammaZeroConjugate f hf))∗ =
      f.asEReal + (((γ : ℝ) : EReal) • halfSquaredNorm.asEReal) := by
  -- Compute the conjugate of the Moreau envelope and rewrite the packaged biconjugate back to `f`.
  calc
    ({}^[γ] (gammaZeroConjugate f hf))∗ =
        (gammaZeroConjugate f hf).asEReal∗ +
          (((γ : ℝ) : EReal) • halfSquaredNorm.asEReal) := by
            simpa using conjugate_moreauEnvelope_eq (f := gammaZeroConjugate f hf) (γ := γ)
    _ = f.asEReal∗∗ + (((γ : ℝ) : EReal) • halfSquaredNorm.asEReal) := by
          rw [gammaZeroConjugate_asEReal_eq_conjugate (f := f) (hf := hf)]
    _ = f.asEReal + (((γ : ℝ) : EReal) • halfSquaredNorm.asEReal) := by
          rw [biconjugate_eq_of_mem_gammaZero hf]

-- Proof sketch: Corollary 13.38 puts `gammaZeroConjugate f hf` in `Γ₀(H)`, and the quadratic
-- kernel is the canonical Moreau regularizer. Proposition 12.14 then gives attainment for the
-- translated sums defining the infimal convolution.
/-- Proposition 14 1: for `f ∈ Γ₀(H)` and `γ ∈ ℝ_{++}`, if
`q(x) = (1 / 2) ‖x‖^2`, then the Fenchel conjugate of `f + γ q` is the
`γ`-Moreau envelope of `f*`; equivalently,
`(f + γ q)^* = f* □ (γ⁻¹ q) = {}^γ(f^*)`, and this infimal convolution is exact. -/
theorem conjugate_add_scaledQuadratic_eq_moreauEnvelope_gammaZeroConjugate
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (γ : Set.Ioi (0 : ℝ)) :
    (f.asEReal + (((γ : ℝ) : EReal) • halfSquaredNorm.asEReal))∗ =
      {}^[γ] (gammaZeroConjugate f hf) := by
  have hmoreau :
      IsProper ({}^[γ] (gammaZeroConjugate f hf)) ∧
        ({}^[γ] (gammaZeroConjugate f hf)) ∈ gamma H :=
    moreauEnvelope_gammaZeroConjugate_isProper_and_mem_gamma (H := H) f hf γ
  have hmoreau_biconj :
      ({}^[γ] (gammaZeroConjugate f hf))∗∗ =
        {}^[γ] (gammaZeroConjugate f hf) :=
    (mem_gamma_iff_eq_biconjugate_of_is_proper hmoreau.1).mp hmoreau.2
  have hconj_moreau :
      ({}^[γ] (gammaZeroConjugate f hf))∗ =
        f.asEReal + (((γ : ℝ) : EReal) • halfSquaredNorm.asEReal) :=
    conjugate_moreauEnvelope_gammaZeroConjugate_eq_add_scaledQuadratic
      (H := H) f hf γ
  -- Conjugate the Moreau-envelope identity once more and use the proper `gamma` owner to remove
  -- the outer biconjugate.
  calc
    (f.asEReal + (((γ : ℝ) : EReal) • halfSquaredNorm.asEReal))∗ =
        (({}^[γ] (gammaZeroConjugate f hf))∗)∗ := by
          rw [hconj_moreau]
    _ = {}^[γ] (gammaZeroConjugate f hf) := by
          simpa using hmoreau_biconj

-- Proof sketch: Corollary 13.38 puts `gammaZeroConjugate f hf` in `Γ₀(H)`, and the quadratic
-- kernel is the canonical Moreau regularizer. Proposition 12.14 then gives attainment for the
-- translated sums defining the infimal convolution.
/-- Proposition 14.1 companion: the infimal convolution `f* □ (γ⁻¹ q)` occurring in the Moreau
envelope representation is exact. -/
theorem infimalConvolution_exact_gammaZeroConjugate_moreauQuadraticKernel
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (γ : Set.Ioi (0 : ℝ)) :
    infimalConvolution.Exact (gammaZeroConjugate f hf) (moreauQuadraticKernel γ) := by
  have hconj : gammaZeroConjugate f hf ∈ Γ₀(H) :=
    gammaZeroConjugate_mem_gammaZero hf
  have hkernel : moreauQuadraticKernel γ ∈ Γ₀(H) :=
    moreauQuadraticKernel_mem_gammaZero_local (H := H) γ
  have hsuper :
      Supercoercive ((moreauQuadraticKernel (H := H) γ : H → Set.Ioi (⊥ : EReal)).asEReal) :=
    supercoercive_moreauQuadraticKernel_local (H := H) γ
  -- Proposition 12.14 attains the infimal convolution because the quadratic kernel is the
  -- supercoercive branch in the source proof; commute once to put that branch first and then
  -- transfer exactness back by symmetry.
  intro x hx
  have hx_comm : x ∈ dom (moreauQuadraticKernel γ □ gammaZeroConjugate f hf) := by
    simpa [infimalConvolution_comm] using hx
  exact
    exactAt_symm_of_exactAt <|
      infimalConvolution_exact_of_supercoercive_or_coercive_bddBelow
        (f := moreauQuadraticKernel γ)
        (g := gammaZeroConjugate f hf)
        (hf := hkernel)
        (hg := hconj)
        (hcase := Or.inl hsuper)
        hx_comm

end MoreauDecomposition

end ERealFunction
