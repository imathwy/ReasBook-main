import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_1_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_0_5

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E] [Module 𝕜 E]
variable [IsScalarTower ℝ 𝕜 E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
variable [LocallyConvexSpace ℝ E]

local instance instHasPairingStrongDualPrimalRealCor1311 :
    HasPairing (StrongDual 𝕜 E) E ℝ where
  pairing l x := RCLike.re (l x)

local instance instHasPairingPrimalStrongDualRealCor1311 :
    HasPairing E (StrongDual 𝕜 E) ℝ where
  pairing x l := RCLike.re (l x)

local instance instHasPairingPrimalStrongDualWithTopBotRealCor1311 :
    HasPairing E (StrongDual 𝕜 E) (WithTopBot ℝ) :=
  instHasPairingWithBotTop

local instance instHasPairingSwapPrimalStrongDualRealCor1311 :
    HasPairingSwap E (StrongDual 𝕜 E) ℝ where
  pairing_swap _ _ := rfl

local instance instHasContinuousPairingPrimalStrongDualRealCor1311 :
    HasContinuousPairing E (StrongDual 𝕜 E) ℝ where
  continuous_pairing_left l := RCLike.continuous_re.comp l.continuous

/-!
Source/core/bridge triage:
- `source-facing`: Corollary 13.1.1 says that for convex sets, inclusion of closures is
  equivalent to the pointwise order relation between their support functions.
- `core/canonical`: the owner abstractions are `closure`, the project support function
  `supportFunction`, and the closed-convex support cutout theorem
  `setOf_forall_dual_le_supportFunction_eq_of_isClosed_convex`.
- `bridge/view`: Rockafellar's `δ*(· | C)` is represented by the chapter notation `δᵛ(· | C)` for
  the owner `supportFunction C`; this file upgrades the evaluation side from self-pairing vectors
  to the intrinsic dual owner `StrongDual 𝕜 E` and reads dual evaluations through `re`, so the
  theorem surface is no longer tied to an inner-product model and keeps the canonical
  `WithTopBot ℝ` support-value codomain instead of a local `EReal` specialization.
- Primitive data vs derived API: the only primitive input is convexity of `closure C₂`; no
  convexity on `C₁` belongs in the statement.

Domain-style sampling used here:
- `supportFunction`;
- `supportFunction_closure`;
- `setOf_forall_dual_le_supportFunction_eq_of_isClosed_convex`.

Layer target: `bridge/view`, stated directly in the canonical closure/support-function API without
introducing any local wrapper notion.
- Ambient refinement: only locally-convex dual half-space separation is used, so the theorem is
  stated on real locally-convex topological modules with an `RCLike` scalar action rather than on
  normed or inner-product specializations.
- Topology abstraction audit: the upstream owner theorem
  `setOf_forall_dual_le_supportFunction_eq_of_isClosed_convex` is an ambient closed-convex cutout
  theorem, so this corollary is canonically about ambient `closure`. An intrinsic/relative-closure
  replacement here would force a stronger finite-dimensional layer (via
  `intrinsicClosure_eq_closure`) that is not primitive to this owner.
-/

/-- Corollary 13.1.1, at the intrinsic dual owner layer: for sets `C₁`, `C₂` with convex
`closure C₂` in a real locally-convex topological module carrying an `RCLike` scalar action, one has
`closure C₁ ⊆ closure C₂` if and only if the support-function inequality on the continuous dual
holds pointwise:
`δᵛ(xStar | C₁) ≤ δᵛ(xStar | C₂)` for all `xStar : StrongDual 𝕜 E`, where support values are in
`WithTopBot ℝ`. -/
theorem closure_subset_closure_iff_supportFunction_le {C₁ C₂ : Set E}
    (hC₂ : Convex ℝ (closure C₂)) :
    closure C₁ ⊆ closure C₂ ↔
      ∀ xStar : StrongDual 𝕜 E,
        (δᵛ(xStar | C₁) : WithTopBot ℝ) ≤ (δᵛ(xStar | C₂) : WithTopBot ℝ) := by
  constructor
  · intro h xStar
    have hClosure :
        (δᵛ(xStar | closure C₁) : WithTopBot ℝ) ≤ (δᵛ(xStar | closure C₂) : WithTopBot ℝ) := by
      rw [supportFunction_def, supportFunction_def]
      refine iSup_le ?_
      intro y
      exact le_iSup_of_le ⟨y, h y.2⟩ le_rfl
    calc
      (δᵛ(xStar | C₁) : WithTopBot ℝ) = (δᵛ(xStar | closure C₁) : WithTopBot ℝ) := by
        simpa using (congrFun (supportFunction_closure (C := C₁)) xStar).symm
      _ ≤ (δᵛ(xStar | closure C₂) : WithTopBot ℝ) := hClosure
      _ = (δᵛ(xStar | C₂) : WithTopBot ℝ) := by
        simpa using congrFun (supportFunction_closure (C := C₂)) xStar
  · intro h x hx
    have hxCutout :
        x ∈ {z : E | ∀ xStar : StrongDual 𝕜 E,
          ⟪z, xStar⟫ₚ ≤ (δᵛ(xStar | closure C₂) : WithTopBot ℝ)} := by
      intro l
      have hxLe :
          ⟪x, l⟫ₚ ≤ (δᵛ(l | closure C₁) : WithTopBot ℝ) := by
        rw [supportFunction_def]
        exact le_iSup (fun y : closure C₁ ↦ (⟪l, (y : E)⟫ₚ : WithTopBot ℝ)) ⟨x, hx⟩
      calc
        ⟪x, l⟫ₚ ≤ (δᵛ(l | closure C₁) : WithTopBot ℝ) := hxLe
        _ = (δᵛ(l | C₁) : WithTopBot ℝ) := by
          simpa using congrFun (supportFunction_closure (C := C₁)) l
        _ ≤ (δᵛ(l | C₂) : WithTopBot ℝ) := h l
        _ = (δᵛ(l | closure C₂) : WithTopBot ℝ) := by
          simpa using (congrFun (supportFunction_closure (C := C₂)) l).symm
    have hcutout :
        {z : E | ∀ xStar : StrongDual 𝕜 E,
          ⟪z, xStar⟫ₚ ≤ (δᵛ(xStar | closure C₂) : WithTopBot ℝ)} =
          closure C₂ :=
      setOf_forall_dual_le_supportFunction_eq_of_isClosed_convex
        (C := closure C₂) isClosed_closure hC₂
    rw [← hcutout]
    exact hxCutout

end
