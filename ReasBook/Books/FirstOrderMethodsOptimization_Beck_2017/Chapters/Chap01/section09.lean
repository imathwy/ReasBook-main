import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_1_9 (from Chap01) -/
universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]
variable (s : Set E) (Q : AffineSubspace ℝ E)

/- Definition 1.9 (1): an affine subset of a real vector space is represented in mathlib by an
`AffineSubspace ℝ E`. -/
#check AffineSubspace ℝ E

/- Definition 1.9 (2): the affine hull of a set `s` is the canonical affine subspace
`affineSpan ℝ s`. Since its codomain is `AffineSubspace ℝ E`, the affine hull is itself affine. -/
#check (affineSpan ℝ : Set E → AffineSubspace ℝ E)

/- Definition 1.9 (3): every set is contained in its affine hull, via the canonical theorem
`subset_affineSpan`. -/
#check (subset_affineSpan ℝ s : s ⊆ affineSpan ℝ s)

/- Definition 1.9 (4): the affine hull is the smallest affine subspace containing `s`; equivalently,
`affineSpan ℝ s ≤ Q` if and only if `s ⊆ Q`. -/
#check (affineSpan_le : affineSpan ℝ s ≤ Q ↔ s ⊆ Q)

/- Definition 1.9 (5): the affine hull is the intersection of all affine subspaces containing the
given set, as expressed by `AffineSubspace.affineSpan_eq_sInf`. -/
#check (AffineSubspace.affineSpan_eq_sInf ℝ E s :
  affineSpan ℝ s = sInf {Q : AffineSubspace ℝ E | s ⊆ Q})

end

/-! ### Proposition_1_9 (from Chap01) -/
open Matrix
open WithLp (linearEquiv ofLp toLp)

noncomputable section

section

variable {ι : Type*} [Fintype ι] {p q : ENNReal}

private theorem holderConjugate_one_le_left (hpq : ENNReal.HolderConjugate p q) : 1 ≤ p := by
  letI : ENNReal.HolderConjugate p q := hpq
  simpa using ENNReal.HolderConjugate.one_le p q

/-- The coordinate-pairing functional on `WithLp p (ι → ℝ)` associated to `y`. -/
def lpPairingDual (p : ENNReal) (y : ι → ℝ) : Module.Dual ℝ (WithLp p (ι → ℝ)) :=
  ((dotProductBilin ℝ ℝ).flip y).comp (linearEquiv p ℝ (ι → ℝ)).toLinearMap

@[simp] theorem lpPairingDual_apply (y : ι → ℝ) (x : WithLp p (ι → ℝ)) :
    lpPairingDual p y x = dotProduct (ofLp x) y :=
  rfl

-- Proof sketch: the main object is the canonical functional `lpPairingDual p y` on the `WithLp`
-- model of `ℝ^n` with its `l_p` norm. Hölder gives the upper bound
-- `|lpPairingDual p y x| ≤ ‖toLp q y‖ * ‖x‖`, while the standard finite-dimensional extremizers
-- show the bound is sharp, including the endpoint pairs `(1, ∞)` and `(∞, 1)`.
/-- Proposition 1.9: the dual norm of the coordinate-pairing functional on
`WithLp p (ι → ℝ)` is the `l_q` norm of the coefficient vector whenever `p` and `q` are
Hölder-conjugate. -/
theorem dualNorm_lpPairingDual_eq_conjugate_lp_norm
    (hpq : ENNReal.HolderConjugate p q) (y : ι → ℝ) :
    letI : Fact (1 ≤ p) := ⟨holderConjugate_one_le_left hpq⟩
    dualNorm (lpPairingDual p y) = ‖toLp q y‖ := sorry

-- Proof sketch: rewrite the source set as the closed unit ball in `WithLp p (ι → ℝ)`,
-- apply the chapter dual-norm inequality for the upper bound, and use
-- `exists_dualNorm_eq_apply` for the lower bound.
/-- The source-facing supremum formula is the unit-ball realization of the dual norm of
`lpPairingDual p y`. -/
theorem unit_lp_pairing_sSup_eq_dualNorm (hp : 1 ≤ p) (y : ι → ℝ) :
    letI : Fact (1 ≤ p) := ⟨hp⟩
    sSup ((fun x : ι → ℝ ↦ dotProduct x y) '' {x | ‖toLp p x‖ ≤ 1}) =
      dualNorm (lpPairingDual p y) := sorry

-- Proof sketch: combine the owner-level dual-norm computation with the unit-ball companion.
/-- The supremum of the coordinate pairing over the closed `l_p` unit ball is the conjugate
`l_q` norm. -/
theorem unit_lp_pairing_sSup_eq_conjugate_lp_norm
    (hpq : ENNReal.HolderConjugate p q) (y : ι → ℝ) :
    sSup ((fun x : ι → ℝ ↦ dotProduct x y) '' {x | ‖toLp p x‖ ≤ 1}) =
      ‖toLp q y‖ := by
  let hp : 1 ≤ p := holderConjugate_one_le_left hpq
  letI : Fact (1 ≤ p) := ⟨hp⟩
  rw [unit_lp_pairing_sSup_eq_dualNorm hp, dualNorm_lpPairingDual_eq_conjugate_lp_norm hpq]

end
