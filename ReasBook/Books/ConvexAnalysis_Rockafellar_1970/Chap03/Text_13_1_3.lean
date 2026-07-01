import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_2
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Operations

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Pointwise Rockafellar

section

variable {𝕜 : Type*} [AddCommGroup 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsOrderedAddMonoid 𝕜] [DenselyOrdered 𝕜]
variable {X Y : Type*}
variable [Add Y] [HasPairing X Y 𝕜] [HasPairingAddRight X Y 𝕜]

/-
Source/core/bridge triage:
- `source-facing`: Text 13.1.3 states the support-function formula for the Minkowski sum
  `C1 + C2`.
- `core/canonical`: the owner abstractions are the project support function `supportFunction` on
  subsets of a pairing space and pointwise set addition.
- `bridge/view`: Rockafellar's notation `δ*(x* | C)` is represented by `δᵛ(xStar | C)`.
- Primitive data vs derived API: both the support function and the pointwise set sum are already
  canonical owners; the item contributes only their interaction theorem. The main declarations use
  the chapter support-function notation `δᵛ(· | C)` on theorem surfaces while
  keeping the same owner-level proof route.

Domain-style sampling used here:
- the project declarations `supportFunction`, `supportFunction_def`, and
  `supportFunction_eq_iSup`;
- the owner expansion `supportFunction_eq_iSup`, which confirms the theorem belongs at the same
  ambient support-function level as `supportFunction` itself, namely the primitive pairing/addition
  owners `[HasPairing X Y 𝕜] [HasPairingAddRight X Y 𝕜]`, rather than the concrete `R^n` model;
- mathlib's pointwise set addition identity `Set.image2_add`;
- mathlib's indexed-supremum witness theorem `lt_iSup_iff`;
- the extended-codomain approximation lemma `WithBotTop.add_le_of_forall_lt`.

Layer target: `source-facing`, stated directly for the support function of the Minkowski sum and
reusing only the canonical owner abstractions already present upstream.

Semantic note:
- the displayed identity already holds for arbitrary subsets `C1` and `C2`; the textbook's
  convexity and nonemptiness assumptions are redundant and are therefore omitted from the Lean
  statement.
- because the owner `supportFunction` is defined on arbitrary pairing spaces, the theorem is
  refined to that ambient owner level instead of the concrete model `EuclideanSpace ℝ (Fin n)`.
- the public codomain surface is the chapter owner `WithTopBot 𝕜`.
-/

-- Proof sketch: expand `supportFunction` using `supportFunction_def`, rewrite the inner-product
-- image of `C1 + C2` as the pointwise sum of the two separate inner-product images, and compare
-- the resulting indexed suprema directly. The upper bound is immediate from `iSup_le`. For the
-- reverse inequality, use `WithBotTop.add_le_of_forall_lt` and `lt_iSup_iff` to approximate each
-- function strictly from below by values attained on `C1` and `C2`.
/-- Text 13.1.3: the support function of the pointwise sum of two sets is the sum of their support
functions. This already holds for arbitrary subsets of a pairing space, so the textbook's
convexity and nonemptiness assumptions are redundant. -/
theorem supportFunction_set_add
    (C1 C2 : Set Y) :
    (δᵛ(· | C1 + C2) : X → WithTopBot 𝕜) =
      (δᵛ(· | C1) : X → WithTopBot 𝕜) + (δᵛ(· | C2) : X → WithTopBot 𝕜) := by
  sorry

/-- Text 13.1.3 in pointwise form: evaluating the support function of a Minkowski sum at `xStar`
gives the sum of the two support values. -/
theorem supportFunction_set_add_apply
    (C1 C2 : Set Y) (xStar : X) :
    (δᵛ(xStar | C1 + C2) : WithTopBot 𝕜) = δᵛ(xStar | C1) + δᵛ(xStar | C2) := by
  simpa using congrFun (supportFunction_set_add C1 C2) xStar

end

-- Proof sketch: expand `supportFunction` using `supportFunction_def`, rewrite the pairing on
-- the dilate by `pairing_smul_right`, and compare the resulting suprema directly. The reverse
-- inequality uses division by the positive scalar `c` to pull a witness in `c • C` back to `C`.
section

variable {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {X Y : Type*}
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasPairing X Y 𝕜] [HasPairingSMulRight X Y 𝕜]

local instance : SMul 𝕜 (WithTopBot 𝕜) where
  smul := fun c z ↦ (c : WithTopBot 𝕜) * z

/-- Positive dilations scale the support function by the same positive scalar. This is an owner
operation theorem for `supportFunction` on arbitrary subsets of a pairing space. -/
private theorem supportFunction_smul_set_of_pos_withTopBot
    (C : Set Y) {c : 𝕜} (hc : 0 < c) :
    (supportFunction (c • C) : X → WithTopBot 𝕜) =
      c • supportFunction C := by
  sorry

/-- Positive dilations scale the support function by the same positive scalar. This is an owner
operation theorem for `supportFunction` on arbitrary subsets of a pairing space. -/
theorem supportFunction_smul_set_of_pos
    (C : Set Y) {c : 𝕜} (hc : 0 < c) :
    (δᵛ(· | c • C) : X → WithTopBot 𝕜) =
      c • (δᵛ(· | C) : X → WithTopBot 𝕜) := by
  simpa using supportFunction_smul_set_of_pos_withTopBot (C := C) hc

/-- Positive dilations scale the support value at `xStar` by the same scalar. -/
theorem supportFunction_smul_set_of_pos_apply
    (C : Set Y) {c : 𝕜} (hc : 0 < c) (xStar : X) :
    (δᵛ(xStar | c • C) : WithTopBot 𝕜) = c • (δᵛ(xStar | C) : WithTopBot 𝕜) := by
  simpa [Pi.smul_apply] using congrFun (supportFunction_smul_set_of_pos C hc) xStar

-- Proof sketch: split into the existing positive-scalar owner theorem and the endpoint `c = 0`.
-- In the zero case, nonemptiness of `C` gives `0 • C = {0}`, and the support function of `{0}`
-- is the zero function by `supportFunction_def`.
/-- Nonnegative dilations of a nonempty set scale the support function by the same scalar. The
positive case is `supportFunction_smul_set_of_pos`; nonemptiness is needed only for the endpoint
`c = 0`. -/
private theorem supportFunction_smul_set_of_nonempty_withTopBot
    [HasPairingZeroRight X Y 𝕜]
    (C : Set Y) (hC : C.Nonempty) {c : 𝕜} (hc : 0 ≤ c) :
    (supportFunction (c • C) : X → WithTopBot 𝕜) =
      c • supportFunction C := by
  sorry

/-- Nonnegative dilations of a nonempty set scale the support function by the same scalar. The
positive case is `supportFunction_smul_set_of_pos`; nonemptiness is needed only for the endpoint
`c = 0`. -/
theorem supportFunction_smul_set_of_nonempty
    [HasPairingZeroRight X Y 𝕜]
    (C : Set Y) (hC : C.Nonempty) {c : 𝕜} (hc : 0 ≤ c) :
    (δᵛ(· | c • C) : X → WithTopBot 𝕜) =
      c • (δᵛ(· | C) : X → WithTopBot 𝕜) := by
  simpa using
    supportFunction_smul_set_of_nonempty_withTopBot
      (C := C) hC (c := c) hc

/-- Evaluating the support function of the nonnegative dilate `c • C` at `xStar` multiplies the
support value by `c`. -/
theorem supportFunction_smul_set_of_nonempty_apply
    [HasPairingZeroRight X Y 𝕜]
    (C : Set Y) (hC : C.Nonempty) {c : 𝕜} (hc : 0 ≤ c) (xStar : X) :
    (δᵛ(xStar | c • C) : WithTopBot 𝕜) = c • (δᵛ(xStar | C) : WithTopBot 𝕜) := by
  simpa [Pi.smul_apply] using congrFun (supportFunction_smul_set_of_nonempty C hC hc) xStar

end

section

variable {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {X Y : Type*}
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

local instance : SMul 𝕜 (WithTopBot 𝕜) where
  smul := fun c z ↦ (c : WithTopBot 𝕜) * z

-- Proof sketch: rewriting `δᵛ(c • x⋆ | C)` as `δᵛ(x⋆ | c • C)` is a direct owner-level
-- reindexing of `supportFunction_def`; combine this with
-- `supportFunction_smul_set_of_nonempty_apply`.
/-- Evaluating the support function at a nonnegative scalar multiple of the primal argument scales
the value by the same scalar. -/
theorem supportFunction_smul_left_of_nonempty_apply
    (C : Set Y) (hC : C.Nonempty) {c : 𝕜} (hc : 0 ≤ c) (xStar : X) :
    (δᵛ(c • xStar | C) : WithTopBot 𝕜) = c • (δᵛ(xStar | C) : WithTopBot 𝕜) := by
  have hswap :
      (δᵛ(c • xStar | C) : WithTopBot 𝕜) = δᵛ(xStar | c • C) := by
    rw [supportFunction_def, supportFunction_def]
    apply le_antisymm
    · refine iSup_le fun y ↦ ?_
      refine le_iSup_of_le (⟨c • (y : Y), ⟨(y : Y), y.2, rfl⟩⟩ : {y : Y // y ∈ c • C}) ?_
      change ((⟪c • xStar, (y : Y)⟫ₚ : 𝕜) : WithTopBot 𝕜) ≤
        ((⟪xStar, c • (y : Y)⟫ₚ : 𝕜) : WithTopBot 𝕜)
      simp [HasLinearPairing.pairing_eq_pairingLinear]
    · refine iSup_le fun y ↦ ?_
      rcases y.2 with ⟨z, hz, hyz⟩
      refine le_iSup_of_le (⟨z, hz⟩ : C) ?_
      rw [← hyz]
      change ((⟪xStar, c • z⟫ₚ : 𝕜) : WithTopBot 𝕜) ≤ ((⟪c • xStar, z⟫ₚ : 𝕜) : WithTopBot 𝕜)
      simp [HasLinearPairing.pairing_eq_pairingLinear]
  rw [hswap]
  simpa using supportFunction_smul_set_of_nonempty_apply C hC hc xStar

end
