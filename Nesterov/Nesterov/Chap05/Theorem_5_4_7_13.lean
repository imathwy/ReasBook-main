import Mathlib
import Nesterov.Chap05.Definition_5_4_3_2
import Nesterov.Chap05.Definition_5_4_6_2
import Nesterov.Chap05.Definition_5_4_7_16
import Nesterov.Chap05.Definition_5_4_7_17
import Nesterov.Chap05.Theorem_5_4_7_8
import Nesterov.Chap05.Theorem_5_4_7_11
import Nesterov.Chap05.Theorem_5_4_7_12

-- Declarations for this item will be appended below by the statement pipeline.

open scoped HessianLocalNorm MonomialXi StandardSimplex
open EuclideanSpace (positiveOrthant)

noncomputable section

variable {n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Xₙ" => positiveOrthant n

/- Theorem 5.4.7.13 lies in the Chapter 5 simplex-monomial / barrier-compatibility domain.

Sampled owner declarations:
* `IsBetaCompatibleWith` from `Definition_5_4_6_2`, the chapter owner for compatibility with a
  self-concordant barrier;
* `ambientMonomialXi` and `ξ_[a]` from `Definition_5_4_7_17`, the simplex-monomial owner and its
  ambient bridge;
* `monomialXi_secondDirectionalDerivative_eq_neg_mul_quantityS2` from `Theorem_5_4_7_11`, the
  owner-level formula for `D² ξ_a`;
* `monomialXi_thirdDirectionalDerivative_eq_mul_two_S3_add_three_mean_S2` from
  `Theorem_5_4_7_12`, the owner-level formula for `D³ ξ_a`;
* `positiveOrthantLogarithmicBarrier_localNorm_eq_norm_relativeDirection` from
  `Theorem_5_4_7_8`, the bridge identifying the barrier local norm with the relative-direction
  norm.

Source/core/bridge triage:
* source-facing: the textbook `β = 1` compatibility statement for the monomial `ξ_a`;
* core/canonical: `IsBetaCompatibleWith` on `positiveOrthant n`;
* bridge/view: the derivative identities for `ξ_a` and the local-norm formula for the orthant
  logarithmic barrier.

The public statement is already at the correct owner level, so this file keeps that owner surface
and avoids introducing any parallel wrapper around the ambient monomial or the barrier.
-/

private theorem positiveOrthant_eq_preimage_piIoi :
    (Xₙ : Set Eₙ) =
      ((EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph) ⁻¹'
        Set.pi Set.univ (fun _ : Fin n ↦ Set.Ioi (0 : ℝ)) := by
  ext x
  simp [EuclideanSpace.positiveOrthant]

private theorem positiveOrthant_isOpen : IsOpen (Xₙ : Set Eₙ) := by
  rw [positiveOrthant_eq_preimage_piIoi]
  exact (isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_Ioi).preimage
    ((EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph.continuous)

private theorem positiveOrthant_convex : Convex ℝ (Xₙ : Set Eₙ) := by
  rw [positiveOrthant_eq_preimage_piIoi]
  exact (convex_pi fun _ _ ↦ convex_Ioi (0 : ℝ)).linear_preimage
    (EuclideanSpace.equiv (Fin n) ℝ).toLinearMap

private theorem positiveOrthant_interior_eq : interior (Xₙ : Set Eₙ) = Xₙ :=
  positiveOrthant_isOpen.interior_eq

private theorem positiveOrthant_interior_nonempty :
    (interior (Xₙ : Set Eₙ)).Nonempty := by
  have hx : WithLp.toLp 2 (fun _ : Fin n ↦ (1 : ℝ)) ∈ Xₙ := by
    rw [EuclideanSpace.mem_positiveOrthant_iff]
    intro j
    exact (zero_lt_one : (0 : ℝ) < 1)
  exact ⟨_, by rwa [positiveOrthant_interior_eq]⟩

private theorem ambientMonomialXi_contDiffOn_positiveOrthant (a : Δ[n]) :
    ContDiffOn ℝ 3 (ambientMonomialXi a) (Xₙ : Set Eₙ) := by
  unfold ambientMonomialXi
  refine contDiffOn_prod fun i _ ↦ ?_
  have hcoord : ContDiffOn ℝ 3 (fun x : Eₙ ↦ x i) (Xₙ : Set Eₙ) := by
    simpa using
      (show ContDiffOn ℝ 3 (fun x : Eₙ ↦ x i) (Xₙ : Set Eₙ) from
        contDiffOn_piLp_apply (2 : ENNReal))
  exact hcoord.rpow_const_of_ne fun x hx ↦
    ne_of_gt ((EuclideanSpace.mem_positiveOrthant_iff.mp hx) i)

private theorem standardLogarithmicBarrierAmbient_isSelfConcordantBarrierOn_positiveOrthant :
    IsSelfConcordantBarrierOnWith (Xₙ : Set Eₙ) (n : NNReal)
      (standardLogarithmicBarrierAmbient n) := by
  sorry

private theorem monomialXi_compatibility_bound
    (a : Δ[n]) {x : Eₙ} (hx : x ∈ Xₙ) (h : Eₙ) :
    (3 * ‖h‖[standardLogarithmicBarrierAmbient n; x]) •
        (-vectorSecondDirectionalDerivative (ambientMonomialXi a) x h) -
      vectorThirdDirectionalDerivative (ambientMonomialXi a) x h ∈
        ConvexCone.positive ℝ ℝ := by
  sorry

-- Proof sketch: use the explicit formulas for the second and third directional derivatives of the
-- monomial `x ↦ x^a`, rewrite the third derivative in terms of the centered quantities `S₂` and
-- `S₃`, bound `S₃` by `S₂ * ‖δ_x(h)‖`, and then identify `‖δ_x(h)‖` with the local norm of the
-- positive-orthant logarithmic barrier.
/-- Theorem 5.4.7.13: for `a ∈ Δₙ`, the monomial
`ξ_a(x) = x^a = ∏_{i=1}^n (x^(i))^(a^(i))` is `1`-compatible with the logarithmic barrier
`F(x) = -\sum_{i=1}^n \log x^(i)` on the strict positive orthant `\mathbb{R}^n_{++}`. -/
theorem monomial_isOneCompatibleWith_positiveOrthantLogarithmicBarrier
    (a : Δ[n]) :
    IsBetaCompatibleWith
      Xₙ
      (ConvexCone.positive ℝ ℝ)
      (standardLogarithmicBarrierAmbient n)
      (1 : NNReal)
      (ambientMonomialXi a) := by
  refine
    { convex_domain := positiveOrthant_convex
      interior_nonempty := positiveOrthant_interior_nonempty
      one_le_parameter := by norm_num
      selfConcordantBarrier := ?_
      contDiffOn := ?_
      compatibility_bound := ?_ }
  · refine ⟨(n : NNReal), ?_⟩
    simpa [positiveOrthant_interior_eq] using
      standardLogarithmicBarrierAmbient_isSelfConcordantBarrierOn_positiveOrthant
  · simpa [positiveOrthant_interior_eq] using
      ambientMonomialXi_contDiffOn_positiveOrthant a
  · intro x hx h
    simpa [one_mul, positiveOrthant_interior_eq] using
      monomialXi_compatibility_bound a (by simpa [positiveOrthant_interior_eq] using hx) h
