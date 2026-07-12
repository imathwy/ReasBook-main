import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_5
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_1_3
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_2_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Metric
open scoped Pointwise RealInnerProductSpace Rockafellar

section Pairing

variable {X E : Type*}
variable [SeminormedAddCommGroup E] [Module ℝ E] [NormSMulClass ℝ E] [T1Space E]
variable [HasPairing X E ℝ]
variable [HasPairingAddRight X E ℝ]
variable [HasPairingSMulRight X E ℝ]
variable [HasPairingZeroRight X E ℝ]

/-
Source/core/bridge triage:
- `source-facing`: Text 13.2.5 gives the support-function formula for the translated Euclidean
  ball `a + λ B`.
- `core/canonical`: the metric-ball owner `closedBall a r` and the support-function owner
  `supportFunction C` are the primary abstractions.
- `bridge/view`: the textbook set `a + λ B` is represented by `({a} : Set E) + λ • B`, with
  `closedBall_eq_add_smul_unitClosedBall` as the canonical bridge.
- Primitive data vs derived API:
  the translation/dilation step for closed balls only needs pairing-level support-function algebra.
  The unit-ball profile enters as a bridge hypothesis `hunit`.

Layer target:
- primary owner theorem below lives on the primitive pairing owner layer
  `[HasPairing X E ℝ] [HasPairingAddRight X E ℝ] [HasPairingSMulRight X E ℝ]
  [HasPairingZeroRight X E ℝ]` with codomain surface `WithTopBot ℝ`;
- inner-product self-pairing and norm identities are downstream specializations.
-/

/-- Pairing-layer closed-ball support formula from the unit-ball bridge identity.

The theorem separates owner responsibilities:
- this file handles the translation/dilation owner algebra for `closedBall a r`;
- the unit-ball profile remains on the canonical owner surface `δᵛ(· | B)`. -/
theorem supportFunction_closedBall_of_unitClosedBall
    (a : E) (r : ℝ) (hr : 0 ≤ r) (xStar : X) :
    δᵛ(xStar | closedBall a r) =
      (⟪xStar, a⟫ₚ : WithTopBot ℝ) + (r : WithTopBot ℝ) * δᵛ(xStar | (B : Set E)) := by
  have hB_nonempty : (B : Set E).Nonempty := by
    refine ⟨0, ?_⟩
    simp
  have hsmul :
      δᵛ(xStar | (r • (B : Set E))) =
        (r : WithTopBot ℝ) * δᵛ(xStar | (B : Set E)) := by
    simpa using
      supportFunction_smul_set_of_nonempty_apply
        (C := (B : Set E)) hB_nonempty (c := r) hr xStar
  calc
    δᵛ(xStar | closedBall a r)
        = δᵛ(xStar | a +ᵥ (r • (B : Set E))) := by
            rw [closedBall_eq_add_smul_unitClosedBall_of_nonneg (a := a) hr]
    _ = δᵛ(xStar | ({a} : Set E) + r • B) := by
          simp [← vadd_eq_add, Set.singleton_vadd]
    _ = δᵛ(xStar | ({a} : Set E)) +
          δᵛ(xStar | r • (B : Set E)) := by
          simpa using
            supportFunction_set_add_apply ({a} : Set E) (r • (B : Set E)) xStar
    _ = δᵛ(xStar | ({a} : Set E)) +
          (r : WithTopBot ℝ) * δᵛ(xStar | (B : Set E)) := by
          exact congrArg (fun t : WithTopBot ℝ ↦ δᵛ(xStar | ({a} : Set E)) + t) hsmul
    _ = (⟪xStar, a⟫ₚ : WithTopBot ℝ) + (r : WithTopBot ℝ) * δᵛ(xStar | (B : Set E)) := by
          rw [supportFunction_singleton]

/-- Pairing-layer textbook-form companion theorem from
`supportFunction_closedBall_of_unitClosedBall`. -/
theorem supportFunction_add_smul_unitClosedBall_of_unitClosedBall
    (a : E) (r : ℝ) (hr : 0 ≤ r) (xStar : X) :
    δᵛ(xStar | ({a} : Set E) + r • B) =
      (⟪xStar, a⟫ₚ : WithTopBot ℝ) + (r : WithTopBot ℝ) * δᵛ(xStar | (B : Set E)) := by
  calc
    δᵛ(xStar | ({a} : Set E) + r • B) =
        δᵛ(xStar | a +ᵥ (r • (B : Set E))) := by
          simp [← vadd_eq_add, Set.singleton_vadd]
    _ =
        δᵛ(xStar | closedBall a r) := by
          rw [← closedBall_eq_add_smul_unitClosedBall_of_nonneg (a := a) hr]
    _ = (⟪xStar, a⟫ₚ : WithTopBot ℝ) + (r : WithTopBot ℝ) * δᵛ(xStar | (B : Set E)) := by
          simpa using
            supportFunction_closedBall_of_unitClosedBall a r hr xStar

/-- Pairing-layer closed-ball support formula where the unit-ball profile is the norm. -/
theorem supportFunction_closedBall_of_unitClosedBall_eq_norm
    [SeminormedAddCommGroup X]
    (hunit : ∀ xStar : X, δᵛ(xStar | (B : Set E)) = (‖xStar‖ : WithTopBot ℝ))
    (a : E) (r : ℝ) (hr : 0 ≤ r) (xStar : X) :
    δᵛ(xStar | closedBall a r) =
      (⟪xStar, a⟫ₚ + r * ‖xStar‖ : WithTopBot ℝ) := by
  calc
    δᵛ(xStar | closedBall a r)
        = (⟪xStar, a⟫ₚ : WithTopBot ℝ) +
            (r : WithTopBot ℝ) * δᵛ(xStar | (B : Set E)) := by
          simpa using
            supportFunction_closedBall_of_unitClosedBall a r hr xStar
    _ = (⟪xStar, a⟫ₚ : WithTopBot ℝ) +
            (r : WithTopBot ℝ) * (‖xStar‖ : WithTopBot ℝ) := by
          simp [hunit xStar]
    _ = (⟪xStar, a⟫ₚ : WithTopBot ℝ) + ((r * ‖xStar‖ : ℝ) : WithTopBot ℝ) := by
          simp
    _ = (⟪xStar, a⟫ₚ + r * ‖xStar‖ : WithTopBot ℝ) := by
          simp

/-- Pairing-layer textbook-form companion theorem where the unit-ball profile is the norm. -/
theorem supportFunction_add_smul_unitClosedBall_of_unitClosedBall_eq_norm
    [SeminormedAddCommGroup X]
    (hunit : ∀ xStar : X, δᵛ(xStar | (B : Set E)) = (‖xStar‖ : WithTopBot ℝ))
    (a : E) (r : ℝ) (hr : 0 ≤ r) (xStar : X) :
    δᵛ(xStar | ({a} : Set E) + r • B) =
      (⟪xStar, a⟫ₚ + r * ‖xStar‖ : WithTopBot ℝ) := by
  calc
    δᵛ(xStar | ({a} : Set E) + r • B)
        = (⟪xStar, a⟫ₚ : WithTopBot ℝ) +
            (r : WithTopBot ℝ) * δᵛ(xStar | (B : Set E)) := by
          simpa using
            supportFunction_add_smul_unitClosedBall_of_unitClosedBall a r hr xStar
    _ = (⟪xStar, a⟫ₚ : WithTopBot ℝ) +
            (r : WithTopBot ℝ) * (‖xStar‖ : WithTopBot ℝ) := by
          simp [hunit xStar]
    _ = (⟪xStar, a⟫ₚ : WithTopBot ℝ) + ((r * ‖xStar‖ : ℝ) : WithTopBot ℝ) := by
          simp
    _ = (⟪xStar, a⟫ₚ + r * ‖xStar‖ : WithTopBot ℝ) := by
          simp

end Pairing

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Text 13.2.5, inner-product specialization of the pairing-layer owner theorem:
the support function of `closedBall a r` is `⟪xStar, a⟫ + r ‖xStar‖`. -/
theorem supportFunction_closedBall
    (a : E) (r : ℝ) (hr : 0 ≤ r) (xStar : E) :
    δᵛ(xStar | closedBall a r) =
      (⟪xStar, a⟫ + r * ‖xStar‖ : WithTopBot ℝ) := by
  refine supportFunction_closedBall_of_unitClosedBall_eq_norm
      ?_ a r hr xStar
  intro y
  simpa using (supportFunction_unitClosedBall_eq_norm_inner (x := y))

/-- Text 13.2.5, inner-product textbook notation companion:
`δᵛ(xStar | ({a} : Set E) + r • B) = ⟪xStar, a⟫ + r ‖xStar‖`. -/
theorem supportFunction_add_smul_unitClosedBall
    (a : E) (r : ℝ) (hr : 0 ≤ r) (xStar : E) :
    δᵛ(xStar | ({a} : Set E) + r • B) =
      (⟪xStar, a⟫ + r * ‖xStar‖ : WithTopBot ℝ) := by
  refine supportFunction_add_smul_unitClosedBall_of_unitClosedBall_eq_norm
      ?_ a r hr xStar
  intro y
  simpa using (supportFunction_unitClosedBall_eq_norm_inner (x := y))

end InnerProduct
