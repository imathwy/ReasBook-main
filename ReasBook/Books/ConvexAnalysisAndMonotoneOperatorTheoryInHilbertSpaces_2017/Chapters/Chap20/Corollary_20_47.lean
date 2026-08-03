import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap13.Corollary_13_38
import BauschkeLean.Chap13.Proposition_13_36
import BauschkeLean.Chap20.Definition_20_20
import BauschkeLean.Chap20.PairingEqualityOperator
import BauschkeLean.Chap20.Theorem_20_46

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace
open ERealFunction
open WithLp

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-
Source/core/bridge triage:
- `source-facing`: Corollary 20.47 states that an autoconjugate member of `Γ₀(H × H)` defines a
  maximally monotone pairing-contact operator.
- `core/canonical`: the owner abstraction is `pairingEqualityOperator` together with the maximal
  monotonicity theorem for the transpose-conjugate contact operator from Theorem 20.46.
- `bridge/view`: autoconjugacy identifies the transpose-conjugate pairing-contact operator with
  the original pairing-contact operator, so the corollary is a thin transport of the owner
  theorem.

Primitive data: `F ∈ Γ₀(H × H)` and autoconjugacy of `F.asEReal`.
Derived API: convexity/properness of `F.asEReal` and `F.asEReal∗`, the two pairing lower bounds,
and the induced owner-level transport for `pairingEqualityOperator`.
Semantic recall: `lean_leansearch` returned no item-specific hit, so the owner theorem was
verified directly from `Theorem_20_46`. -/

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

-- Proof sketch: `hF` gives properness of `F`, while autoconjugacy and Proposition 13.36 yield the
-- pointwise lower bounds `⟪x, u⟫ ≤ F (x, u)` and `⟪x, u⟫ ≤ (F∗)ᵀ (x, u)`. Apply Theorem 20.46 to
-- the transpose-conjugate contact operator `pairingEqualityOperator (F∗ᵀ[hF])`;
-- autoconjugacy identifies this operator with the original pairing-contact operator
-- `pairingEqualityOperator F`.
/-- For an autoconjugate member `F ∈ Γ₀(H × H)`, the canonical packaged transpose-conjugate
`F∗ᵀ[hF]` is exactly `F`. -/
theorem gammaZeroConjugateTranspose_eq_of_autoconjugate
    (F : H × H → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(H × H))
    (hauto : autoconjugate F.asEReal) :
    F∗ᵀ[hF] = F := by
  -- Compare the two packaged `Γ₀` representatives pointwise after coercing back to `EReal`.
  funext p
  rcases p with ⟨x, u⟩
  apply Subtype.ext
  -- Autoconjugacy rewrites the transpose-conjugate value to the original one.
  simpa [gammaZeroConjugateTranspose_apply, gammaZeroConjugate_apply] using
    conjugate_swap_eq_of_autoconjugate hauto x u

/-- Corollary 20.47: on a real Hilbert space, if `F ∈ Γ₀(H × H)` is autoconjugate, then the
operator defined by `gra A = {(x, u) | F (x, u) = ⟪x, u⟫}` is maximally monotone. -/
theorem pairingEqualityOperator_isMaximallyMonotone_of_mem_gammaZero_of_autoconjugate
    (F : H × H → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(H × H))
    (hauto : autoconjugate F.asEReal) :
    Maximal IsMonotone (pairingEqualityOperator F) := by
  have hF_proper : IsProper F.asEReal := isProper_of_mem_gammaZero hF
  have hF_conv : IsConvex F.asEReal := by
    -- Membership in `Γ₀` packages the convexity needed by Theorem 20.46.
    exact (mem_gamma_iff _).1 (asEReal_mem_gamma_of_mem_gammaZero hF) |>.1
  have hFstar_proper : IsProper F.asEReal∗ := by
    -- The packaged conjugate still lies in `Γ₀`, so its raw coercion is proper.
    simpa [gammaZeroConjugate_apply] using
      isProper_of_mem_gammaZero (gammaZeroConjugate_mem_gammaZero hF)
  have hF_ge : ∀ x u : H, pairing (x, u) ≤ F.asEReal (x, u) := by
    -- Proposition 13.36 gives the primal lower bound for a proper autoconjugate function.
    intro x u
    simpa [pairing_apply] using pairing_le_autoconjugate hF_proper hauto x u
  have hFstarT_ge : ∀ x u : H, pairing (x, u) ≤ ((F.asEReal∗)ᵀ) (x, u) := by
    -- The conjugate lower bound is the second input of Theorem 20.46.
    intro x u
    simpa [pairing_apply, transpose_apply, real_inner_comm] using
      pairing_le_conjugate_of_autoconjugate hF_proper hauto u x
  have hmax_raw : Maximal IsMonotone (pairingEqualityOperator ((F.asEReal∗)ᵀ)) := by
    -- Apply Theorem 20.46(ii) to the raw `EReal` representative `F.asEReal`.
    exact pairingEqualityOperator_conjugateTranspose_isMaximallyMonotone
      (F := F.asEReal) hFstarT_ge hF_conv hFstar_proper hF_ge
  have hmax_pkg : Maximal IsMonotone (pairingEqualityOperator (F∗ᵀ[hF])) := by
    -- Repackage the raw transpose-conjugate contact operator into the `Γ₀` notation.
    simpa [SetValuedOperator.pairingEqualityOperator, gammaZeroConjugateTranspose,
      gammaZeroConjugate_apply, transpose_apply] using hmax_raw
  -- Autoconjugacy identifies the packaged transpose-conjugate with the original `F`.
  simpa [gammaZeroConjugateTranspose_eq_of_autoconjugate F hF hauto] using hmax_pkg

end SetValuedOperator
