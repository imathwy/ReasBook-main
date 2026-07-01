import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_0_3
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_0_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

open scoped Rockafellar

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E] [Module 𝕜 E]
variable [IsScalarTower ℝ 𝕜 E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
variable [LocallyConvexSpace ℝ E]

local notation "E⋆" => StrongDual 𝕜 E

local instance instHasPairingPrimalStrongDualReal : HasPairing E E⋆ ℝ where
  pairing x l := RCLike.re (l x)

local instance instHasPairingStrongDualPrimalReal : HasPairing E⋆ E ℝ :=
  HasPairing.swap (X := E) (Y := E⋆) (L := ℝ)

local instance instHasPairingPrimalStrongDualWithTopBotReal :
    HasPairing E E⋆ (WithTopBot ℝ) :=
  instHasPairingWithBotTop

local instance instHasPairingSwapPrimalStrongDualReal :
    HasPairingSwap E E⋆ ℝ where
  pairing_swap _ _ := rfl

local instance instHasContinuousPairingPrimalStrongDualReal :
    HasContinuousPairing E E⋆ ℝ where
  continuous_pairing_left l := RCLike.continuous_re.comp l.continuous

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 13.1.2 defines
  `D = {x | ∀ xStar, ⟪x, xStar⟫ ≤ δ*(xStar | C)}`
  for a closed convex set `C` and states that `D = C`, so `C` is determined by its support
  function.
- `core/canonical`: the owner abstractions are the project support function `supportFunction`,
  the support-function/half-space bridge
  `subset_closedHalfSpaceLE_iff_supportFunction_le_withTopBot`, and the closed-convex half-space
  owner theorem `RCLike.iInter_halfSpaces_eq'`.
- `bridge/view`: Rockafellar's `δ*(xStar | C)` is `supportFunction C xStar`, and the displayed set
  `D` is the source-facing dual-evaluation presentation of the dual-half-space intersection from
  the owner theorem.

Domain-style sampling used here:
- `supportFunction`;
- `subset_closedHalfSpaceLE_iff_supportFunction_le_withTopBot`;
- `RCLike.iInter_halfSpaces_eq'`.

Layer target: `bridge/view`, stated directly as the equality between `C` and the support-function
cutout set at the continuous-dual owner layer, with the uniqueness consequence exposed separately
as a thin companion theorem.
- Ambient refinement: only locally-convex dual half-space separation is used, so the primary
  theorem is stated on a real locally convex topological module with an `RCLike` scalar action,
  without adding an inner-product-specialized source-facing duplicate.
-/

-- Proof sketch: the forward implication sends each support-function inequality to the owner
-- dual-half-space intersection from `RCLike.iInter_halfSpaces_eq'`; the reverse implication is
-- immediate from `supportFunction_def` because each `x ∈ C` contributes one value in the defining
-- supremum.
/-- Text 13.1.2 at the intrinsic dual owner layer: for a closed convex set `C`, the set of points
whose dual evaluations are bounded above by the support function of `C` is exactly `C`. -/
theorem setOf_forall_dual_le_supportFunction_eq_of_isClosed_convex {C : Set E}
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    {x : E | ∀ xStar : E⋆,
      ⟪x, xStar⟫ₚ ≤ (δᵛ(xStar | C) : WithTopBot ℝ)} = C := by
  ext x
  constructor
  · intro hx
    have hx' :
        x ∈
          ⋂ (l : E⋆) (c : ℝ) (_ : ∀ y ∈ C, RCLike.re (l y) ≤ c),
            {z : E | RCLike.re (l z) ≤ c} := by
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      intro l c hc
      have hsubset : C ⊆ closedHalfSpaceLE l c := by
        intro y hyC
        exact mem_closedHalfSpaceLE_iff.mpr (hc y hyC)
      have hsupport_le : (δᵛ(l | C) : WithTopBot ℝ) ≤ c :=
        (subset_closedHalfSpaceLE_iff_supportFunction_le_withTopBot C l c).1 hsubset
      have hx_le : (⟪x, l⟫ₚ : WithTopBot ℝ) ≤ c :=
        (hx l).trans hsupport_le
      have hxWithBot : ((⟪x, l⟫ₚ : ℝ) : WithBot ℝ) ≤ ((c : ℝ) : WithBot ℝ) :=
        (WithTop.coe_le_coe).1 hx_le
      exact (WithBot.coe_le_coe).1 hxWithBot
    have hhalfspaces :
        ⋂ (l : E⋆) (c : ℝ) (_ : ∀ y ∈ C, RCLike.re (l y) ≤ c),
            {z : E | RCLike.re (l z) ≤ c} =
          C :=
      RCLike.iInter_halfSpaces_eq' (𝕜 := 𝕜) hC_convex hC_closed
    simpa [hhalfspaces] using hx'
  · intro hx xStar
    rw [supportFunction_def]
    exact le_iSup (fun y : C ↦ (⟪xStar, (y : E)⟫ₚ : WithTopBot ℝ)) ⟨x, hx⟩

/-- Closure-owner form of Text 13.1.2: if `closure C` is convex, then the support-function cutout
defined from `C` recovers `closure C`. -/
theorem setOf_forall_dual_le_supportFunction_eq_closure_of_convex_closure {C : Set E}
    (hC_convex : Convex ℝ (closure C)) :
    {x : E | ∀ xStar : E⋆,
      ⟪x, xStar⟫ₚ ≤ (δᵛ(xStar | C) : WithTopBot ℝ)} = closure C := by
  have hsupport_closure :
      (δᵛ(· | closure C) : E⋆ → WithTopBot ℝ) =
        (δᵛ(· | C) : E⋆ → WithTopBot ℝ) :=
    supportFunction_closure (C := C)
  have hcutout_closure :
      {x : E | ∀ xStar : E⋆,
        ⟪x, xStar⟫ₚ ≤ (δᵛ(xStar | closure C) : WithTopBot ℝ)} = closure C :=
    setOf_forall_dual_le_supportFunction_eq_of_isClosed_convex
      (C := closure C) isClosed_closure hC_convex
  rw [← hcutout_closure]
  ext x
  constructor <;> intro hx xStar
  · exact (congrFun hsupport_closure xStar).symm ▸
      (hx xStar : (⟪x, xStar⟫ₚ : WithTopBot ℝ) ≤ (δᵛ(xStar | C) : WithTopBot ℝ))
  · exact (congrFun hsupport_closure xStar) ▸
      (hx xStar : (⟪x, xStar⟫ₚ : WithTopBot ℝ) ≤ (δᵛ(xStar | closure C) : WithTopBot ℝ))

/-- Closure-owner uniqueness form: if `closure C` and `closure D` are convex and their support
functions agree on the continuous dual, then `closure C = closure D`. -/
theorem closure_eq_of_convex_closure_supportFunction_eq {C D : Set E}
    (hC_convex : Convex ℝ (closure C)) (hD_convex : Convex ℝ (closure D))
    (h_support :
      (δᵛ(· | C) : E⋆ → WithTopBot ℝ) =
        (δᵛ(· | D) : E⋆ → WithTopBot ℝ)) :
    closure C = closure D := by
  have hC_cutout :
      {x : E | ∀ xStar : E⋆, ⟪x, xStar⟫ₚ ≤ (δᵛ(xStar | C) : WithTopBot ℝ)} = closure C :=
    setOf_forall_dual_le_supportFunction_eq_closure_of_convex_closure hC_convex
  have hD_cutout :
      {x : E | ∀ xStar : E⋆, ⟪x, xStar⟫ₚ ≤ (δᵛ(xStar | D) : WithTopBot ℝ)} = closure D :=
    setOf_forall_dual_le_supportFunction_eq_closure_of_convex_closure hD_convex
  rw [← hC_cutout, ← hD_cutout]
  ext x
  constructor
  · intro hx xStar
    exact (hx xStar).trans (congrFun h_support xStar).le
  · intro hx xStar
    exact (hx xStar).trans (congrFun h_support xStar).symm.le

-- Proof sketch: first apply the closure-owner uniqueness theorem
-- `closure_eq_of_convex_closure_supportFunction_eq`. The closedness assumptions then identify
-- each closure with the original set.
/-- A closed convex set is uniquely determined by its support function on the continuous dual. -/
theorem eq_of_isClosed_convex_supportFunction_eq {C D : Set E}
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (hD_closed : IsClosed D) (hD_convex : Convex ℝ D)
    (h_support :
      (δᵛ(· | C) : E⋆ → WithTopBot ℝ) =
        (δᵛ(· | D) : E⋆ → WithTopBot ℝ)) :
    C = D := by
  have hC_closure_convex : Convex ℝ (closure C) := by
    simpa [hC_closed.closure_eq] using hC_convex
  have hD_closure_convex : Convex ℝ (closure D) := by
    simpa [hD_closed.closure_eq] using hD_convex
  have hclosure :
      closure C = closure D :=
    closure_eq_of_convex_closure_supportFunction_eq
      (C := C) (D := D) hC_closure_convex hD_closure_convex h_support
  simpa [hC_closed.closure_eq, hD_closed.closure_eq] using hclosure

end
