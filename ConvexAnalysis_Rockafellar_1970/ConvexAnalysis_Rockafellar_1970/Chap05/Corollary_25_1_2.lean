import Mathlib.Analysis.Convex.Exposed
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_1
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2
import ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_25_1

noncomputable section

open scoped Gradient RealInnerProductSpace Rockafellar

universe u v

section

variable {𝕜 : Type v}
variable [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} [Sub E]
variable {U : Set E} {f : E → 𝕜}
variable {Y : Type (max u v)} [HasPairing E Y 𝕜] [HasPairingSubLeft E Y 𝕜]

local notation "fExt" => Function.toWithTopBotOn f U
local notation "fStar" => (fExt⋆ : Y → WithTopBot 𝕜)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 25.1.2 identifies the geometric consequence of a singleton relative
  subdifferential owner at `x`: the boundary point of the conjugate epigraph `epi fStar` determined
  by that unique subgradient is an exposed point.
- `core/canonical`: this file now uses the canonical Chapter 25 owner
  `∂ᵣ[Y]f(x | U) : Set Y` directly at pairing level; no inner-product model is
  needed at this layer.
- `bridge/view`: the Euclidean gradient specialization appears later as a thin Fréchet-Riesz
  bridge via `InnerProductSpace.toDual`.

Primary mathematical domain:
- exposed points of conjugate epigraphs arising from unique subgradients.

Domain-style sampling used here:
- `epi` / `mem_epi_iff` from `Chap01.Definition_4_1`;
- `Set.exposedPoints` and `mem_exposedPoints_iff_exposed_singleton` from
  `Mathlib.Analysis.Convex.Exposed`;
- `convexConjugate` / `f⋆` from `Chap03.Defn_12_2`;
- `∂ᵣ[·]·(· | ·)` from `Chap05.Definition_25_1`.

Primitive data vs derived API:
- primitive source data: the canonical extension `fExt`, a base point `x ∈ U`, and
  a singleton owner identity `∂ᵣ[Y]f(x | U) = {xStar}`;
- source-facing owner statement: the Fenchel-Young contact point of the conjugate epigraph is
  exposed;
- derived companions: the Fenchel-Young height identity
  `fStar xStar = ⟪x, xStar⟫ₚ - f x`, and its `EReal.toReal` epigraph-height bridge.

Layer target:
- `convexConjugate_eq_apply_sub_of_mem_subdifferentialWithinAt`: `source-facing`;
- `mem_exposedPoints_epi_convexConjugate_of_subdifferentialWithinAt_eq_singleton`:
  `source-facing`;
- `mem_exposedPoints_epi_convexConjugate_of_subdifferentialWithinAt_eq_singleton_toRealHeight`:
  `bridge/view`.
-/

/-- If `xStar` is a relative subgradient of `f` at `x`, then the conjugate of the canonical
extension `fExt` attains the Fenchel-Young equality value `⟪x, xStar⟫ₚ - f x` at `xStar`. -/
theorem convexConjugate_eq_apply_sub_of_mem_subdifferentialWithinAt
    {x : E} {xStar : Y} (hxU : x ∈ U)
    (hxStar : xStar ∈ ∂ᵣ[Y]f(x | U)) :
    fStar xStar = (⟪x, xStar⟫ₚ - f x : 𝕜) := by
  rw [convexConjugate_eq_iSup_pairing_sub]
  apply le_antisymm
  · refine iSup_le ?_
    intro z
    by_cases hzU : z ∈ U
    · have hzineqW :
          (((f x + ⟪z - x, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜) ≤ (f z : WithTopBot 𝕜)) := by
        have hzineq := (_root_.mem_subdifferentialWithinAt_pairing
            (f := f) (U := U) (x := x) (Y := Y) (xStar := xStar)).1 hxStar z
        simpa [Function.toWithTopBotOn_of_mem (f := f) (C := U) hxU,
          Function.toWithTopBotOn_of_mem (f := f) (C := U) hzU, sub_eq_add_neg,
          add_assoc, add_comm, add_left_comm] using hzineq
      have hzineq : (⟪z, xStar⟫ₚ - f z : 𝕜) ≤ ⟪x, xStar⟫ₚ - f x := by
        have hpair : (⟪z - x, xStar⟫ₚ : 𝕜) = ⟪z, xStar⟫ₚ - ⟪x, xStar⟫ₚ :=
          HasPairingSubLeft.pairing_sub_left z x xStar
        have hzineqW' : (f x + (⟪z, xStar⟫ₚ - ⟪x, xStar⟫ₚ : 𝕜) : 𝕜) ≤ f z := by
          simpa [hpair] using (WithTopBot.coe_le_coe.mp hzineqW)
        linarith
      rw [Function.toWithTopBotOn_of_mem (f := f) (C := U) hzU]
      have hzcoew :
          (((⟪z, xStar⟫ₚ - f z : 𝕜) : WithTopBot 𝕜) ≤ ((⟪x, xStar⟫ₚ - f x : 𝕜) : WithTopBot 𝕜)) :=
        WithTopBot.coe_le_coe.mpr hzineq
      change (((⟪z, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜) + -((f z : 𝕜) : WithTopBot 𝕜)) ≤
        ((⟪x, xStar⟫ₚ - f x : 𝕜) : WithTopBot 𝕜)
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hzcoew
    · simp [Function.toWithTopBotOn_of_notMem (f := f) (C := U) hzU, sub_eq_add_neg]
  · have hxterm :
      (⟪x, xStar⟫ₚ : 𝕜) - fExt x ≤
        ⨆ z : E, (⟪z, xStar⟫ₚ : 𝕜) - fExt z := by
      exact le_iSup (fun z : E ↦ (⟪z, xStar⟫ₚ : 𝕜) - fExt z) x
    have hxterm_simpl :
        (-((f x : 𝕜) : WithTopBot 𝕜) + ((⟪x, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜)) ≤
          ⨆ z : E, -fExt z + ((⟪z, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜) := by
      simpa [Function.toWithTopBotOn_of_mem (f := f) (C := U) hxU,
        sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hxterm
    have hiSup_comm :
        (⨆ z : E, -fExt z + ((⟪z, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜)) =
          ⨆ z : E, ((⟪z, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜) + -fExt z := by
      refine iSup_congr ?_
      intro z
      exact add_comm (-fExt z) (((⟪z, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜))
    calc
      ((⟪x, xStar⟫ₚ - f x : 𝕜) : WithTopBot 𝕜)
          = -((f x : 𝕜) : WithTopBot 𝕜) + ((⟪x, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜) := by
            simp [sub_eq_add_neg, add_comm]
      _ ≤ ⨆ z : E, -fExt z + ((⟪z, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜) := hxterm_simpl
      _ = ⨆ z : E, ((⟪z, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜) + -fExt z := hiSup_comm
      _ = ⨆ z : E, (⟪z, xStar⟫ₚ : 𝕜) - fExt z := by
            simp [sub_eq_add_neg]

end

section

variable {𝕜 : Type v}
variable [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {Y : Type (max u v)} [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [HasLinearPairing E Y 𝕜] [HasPairingSubLeft E Y 𝕜]
variable [HasPairing Y E 𝕜] [HasPairingSwap E Y 𝕜] [HasContinuousPairing Y E 𝕜]
variable {U : Set E} {f : E → 𝕜}

local notation "fExt" => Function.toWithTopBotOn f U
local notation "fStar" => (fExt⋆ : Y → WithTopBot 𝕜)

/-- If `∂ᵣ[Y]f(x | U) = {xStar}`, then the corresponding
Fenchel-Young contact point of the conjugate epigraph is exposed. -/
theorem mem_exposedPoints_epi_convexConjugate_of_subdifferentialWithinAt_eq_singleton
    {x : E} {xStar : Y} (hxU : x ∈ U)
    (hsub : ∂ᵣ[Y]f(x | U) = {xStar}) :
    (xStar, ⟪x, xStar⟫ₚ - f x) ∈ (epi fStar).exposedPoints 𝕜 := by
  have hxStar : xStar ∈ ∂ᵣ[Y]f(x | U) := by
    simpa [hsub]
  have hvalue : fStar xStar = (⟪x, xStar⟫ₚ - f x : 𝕜) :=
    convexConjugate_eq_apply_sub_of_mem_subdifferentialWithinAt
      (f := f) (U := U) (Y := Y) hxU hxStar
  have hp0_epi : (xStar, ⟪x, xStar⟫ₚ - f x) ∈ epi fStar :=
    (mem_epi_iff).2 (le_of_eq hvalue)
  let pairingAtX : Y →L[𝕜] 𝕜 :=
    { toLinearMap := HasLinearPairing.pairingLinear x
      cont := by
        refine (HasContinuousPairing.continuous_pairing_left (X := Y) (Y := E) (𝕜 := 𝕜) x).congr ?_
        intro y
        simpa using (HasPairingSwap.pairing_swap (X := E) (Y := Y) x y).symm }
  let l : StrongDual 𝕜 (Y × 𝕜) :=
    (pairingAtX.comp (ContinuousLinearMap.fst 𝕜 Y 𝕜)) - ContinuousLinearMap.snd 𝕜 Y 𝕜
  have hl_p0 : l (xStar, ⟪x, xStar⟫ₚ - f x) = f x := by
    change (⟪x, xStar⟫ₚ : 𝕜) - (⟪x, xStar⟫ₚ - f x) = f x
    ring
  rw [exposed_point_def]
  refine ⟨hp0_epi, l, ?_⟩
  intro p hp
  rcases p with ⟨y, μ⟩
  have hyμ : fStar y ≤ μ := (mem_epi_iff.mp hp)
  have hFenchel_x : (((⟪x, y⟫ₚ - f x : 𝕜) : WithTopBot 𝕜) ≤ fStar y) := by
    rw [convexConjugate_eq_iSup_pairing_sub]
    have hxterm :
        (⟪x, y⟫ₚ : 𝕜) - fExt x ≤
          ⨆ z : E, (⟪z, y⟫ₚ : 𝕜) - fExt z := by
      exact le_iSup (fun z : E ↦ (⟪z, y⟫ₚ : 𝕜) - fExt z) x
    rw [Function.toWithTopBotOn_of_mem (f := f) (C := U) hxU] at hxterm
    change (((⟪x, y⟫ₚ - f x : 𝕜) : WithTopBot 𝕜) ≤
      ⨆ z : E, (⟪z, y⟫ₚ : 𝕜) - fExt z)
    have hco :
        (((⟪x, y⟫ₚ - f x : 𝕜) : WithTopBot 𝕜) =
          ((⟪x, y⟫ₚ : WithTopBot 𝕜) - (f x : WithTopBot 𝕜))) := by
      simpa [sub_eq_add_neg, WithTopBot.coe_add, WithTopBot.coe_neg]
    calc
      ((⟪x, y⟫ₚ - f x : 𝕜) : WithTopBot 𝕜) =
          ((⟪x, y⟫ₚ : WithTopBot 𝕜) - (f x : WithTopBot 𝕜)) := hco
      _ = (⟪x, y⟫ₚ : 𝕜) - (f x : WithTopBot 𝕜) := by rfl
      _ ≤ ⨆ z : E, (⟪z, y⟫ₚ : 𝕜) - fExt z := hxterm
  have hxy : (⟪x, y⟫ₚ - f x : 𝕜) ≤ μ :=
    WithTopBot.coe_le_coe.mp (hFenchel_x.trans hyμ)
  have hle_main : l (y, μ) ≤ l (xStar, ⟪x, xStar⟫ₚ - f x) := by
    rw [hl_p0]
    change (⟪x, y⟫ₚ : 𝕜) - μ ≤ f x
    have hle_fx : (⟪x, y⟫ₚ - μ : 𝕜) ≤ f x := by
      linarith [hxy]
    exact hle_fx
  refine ⟨hle_main, ?_⟩
  intro hrev
  have hle_fx : l (y, μ) ≤ f x := by
    rw [hl_p0] at hle_main
    exact hle_main
  have hge_fx : f x ≤ l (y, μ) := by
    rw [hl_p0] at hrev
    exact hrev
  have hl_eq : l (y, μ) = f x := le_antisymm hle_fx hge_fx
  have hmu_eq : μ = ⟪x, y⟫ₚ - f x := by
    have htmp : (⟪x, y⟫ₚ - μ : 𝕜) = f x := by
      have hl_eq' : l (y, μ) = f x := hl_eq
      change ⟪x, y⟫ₚ - μ = f x at hl_eq'
      exact hl_eq'
    have htmp' : μ = ⟪x, y⟫ₚ - f x := by
      linarith [htmp]
    exact htmp'
  have hyEqStar : fStar y = (⟪x, y⟫ₚ - f x : 𝕜) := by
    have hmu_eqW : (μ : WithTopBot 𝕜) = ((⟪x, y⟫ₚ - f x : 𝕜) : WithTopBot 𝕜) :=
      congrArg (fun t : 𝕜 => ((t : 𝕜) : WithTopBot 𝕜)) hmu_eq
    apply le_antisymm
    · exact le_trans hyμ (le_of_eq hmu_eqW)
    · exact hFenchel_x
  have hy_sub : y ∈ ∂ᵣ[Y]f(x | U) := by
    rw [_root_.mem_subdifferentialWithinAt_pairing]
    intro z
    by_cases hzU : z ∈ U
    · have hzSup :
          ((⟪z, y⟫ₚ - f z : 𝕜) : WithTopBot 𝕜) ≤ fStar y := by
        rw [convexConjugate_eq_iSup_pairing_sub]
        have hzterm :
            (⟪z, y⟫ₚ : 𝕜) - fExt z ≤
              ⨆ w : E, (⟪w, y⟫ₚ : 𝕜) - fExt w := by
          exact le_iSup (fun w : E ↦ (⟪w, y⟫ₚ : 𝕜) - fExt w) z
        rw [Function.toWithTopBotOn_of_mem (f := f) (C := U) hzU] at hzterm
        change (((⟪z, y⟫ₚ - f z : 𝕜) : WithTopBot 𝕜) ≤
          ⨆ w : E, (⟪w, y⟫ₚ : 𝕜) - fExt w)
        have hco :
            (((⟪z, y⟫ₚ - f z : 𝕜) : WithTopBot 𝕜) =
              ((⟪z, y⟫ₚ : WithTopBot 𝕜) - (f z : WithTopBot 𝕜))) := by
          simpa [sub_eq_add_neg, WithTopBot.coe_add, WithTopBot.coe_neg]
        calc
          ((⟪z, y⟫ₚ - f z : 𝕜) : WithTopBot 𝕜) =
              ((⟪z, y⟫ₚ : WithTopBot 𝕜) - (f z : WithTopBot 𝕜)) := hco
          _ = (⟪z, y⟫ₚ : 𝕜) - (f z : WithTopBot 𝕜) := by rfl
          _ ≤ ⨆ w : E, (⟪w, y⟫ₚ : 𝕜) - fExt w := hzterm
      have hzSup' : ((⟪z, y⟫ₚ - f z : 𝕜) : WithTopBot 𝕜) ≤ ((⟪x, y⟫ₚ - f x : 𝕜) : WithTopBot 𝕜) := by
        calc
          ((⟪z, y⟫ₚ - f z : 𝕜) : WithTopBot 𝕜) ≤ fStar y := hzSup
          _ = ((⟪x, y⟫ₚ - f x : 𝕜) : WithTopBot 𝕜) := hyEqStar
      have hzSup'' : (⟪z, y⟫ₚ - f z : 𝕜) ≤ ⟪x, y⟫ₚ - f x :=
        WithTopBot.coe_le_coe.mp hzSup'
      have hzineq : (f x + ⟪z - x, y⟫ₚ : 𝕜) ≤ f z := by
        have hpair : (⟪z - x, y⟫ₚ : 𝕜) = ⟪z, y⟫ₚ - ⟪x, y⟫ₚ :=
          HasPairingSubLeft.pairing_sub_left z x y
        linarith [hzSup'', hpair]
      have hzineqW :
          (((f x + ⟪z - x, y⟫ₚ : 𝕜) : WithTopBot 𝕜) ≤ (f z : WithTopBot 𝕜)) :=
        WithTopBot.coe_le_coe.mpr hzineq
      rw [Function.toWithTopBotOn_of_mem (f := f) (C := U) hxU,
        Function.toWithTopBotOn_of_mem (f := f) (C := U) hzU]
      exact hzineqW
    · rw [Function.toWithTopBotOn_of_notMem (f := f) (C := U) hzU]
      exact le_top
  have hy_eq_xStar : y = xStar := by
    simpa [hsub]
      using hy_sub
  have hmu_target : μ = ⟪x, xStar⟫ₚ - f x := by
    calc
      μ = ⟪x, y⟫ₚ - f x := hmu_eq
      _ = ⟪x, xStar⟫ₚ - f x := by rw [hy_eq_xStar]
  exact Prod.ext hy_eq_xStar hmu_target

end

section

variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
variable {U : Set E} {f : E → ℝ}

local instance : HasPairing E (StrongDual ℝ E) ℝ :=
  instHasPairingOfHasLinearPairing

local instance : HasPairingSubLeft E (StrongDual ℝ E) ℝ :=
  instHasPairingSubLeftOfHasLinearPairing

local instance : HasPairing (StrongDual ℝ E) E ℝ :=
  instHasPairingStrongDualPrimal

local instance : HasPairingSwap E (StrongDual ℝ E) ℝ where
  pairing_swap x xStar := rfl

local instance : HasContinuousPairing (StrongDual ℝ E) E ℝ where
  continuous_pairing_left x := by
    simpa using (ContinuousLinearMap.continuous (ContinuousLinearMap.apply ℝ ℝ x))

local notation "fExt" => Function.toWithTopBotOn f U
local notation "fStar" => (fExt⋆ : StrongDual ℝ E → WithTopBot ℝ)

/-- Bridge form of the previous theorem on the canonical real-height epigraph surface:
`EReal.toReal (fStar xStar)` equals the Fenchel-Young height `⟪x, xStar⟫ₚ - f x`. -/
theorem mem_exposedPoints_epi_convexConjugate_of_subdifferentialWithinAt_eq_singleton_toRealHeight
    {x : E} {xStar : StrongDual ℝ E} (hxU : x ∈ U)
    (hsub : ∂ᵣf(x | U) = {xStar}) :
    (xStar, EReal.toReal (fStar xStar)) ∈ (epi fStar).exposedPoints ℝ := by
  have hmain :
      (xStar, ⟪x, xStar⟫ₚ - f x) ∈ (epi fStar).exposedPoints ℝ :=
    mem_exposedPoints_epi_convexConjugate_of_subdifferentialWithinAt_eq_singleton
      hxU hsub
  have hxStar : xStar ∈ ∂ᵣf(x | U) := by
    simp [hsub]
  have hheight : EReal.toReal (fStar xStar) = ⟪x, xStar⟫ₚ - f x := by
    have hheight' :
        EReal.toReal (fStar xStar) = EReal.toReal (⟪x, xStar⟫ₚ - f x : ℝ) :=
      congrArg EReal.toReal
        (convexConjugate_eq_apply_sub_of_mem_subdifferentialWithinAt
          hxU hxStar)
    exact hheight'.trans (EReal.toReal_coe (⟪x, xStar⟫ₚ - f x))
  rw [hheight]
  exact hmain

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {U : Set E} {f : E → ℝ}

local instance : HasPairing E (StrongDual ℝ E) ℝ :=
  instHasPairingOfHasLinearPairing

local instance : HasPairingSubLeft E (StrongDual ℝ E) ℝ :=
  instHasPairingSubLeftOfHasLinearPairing

local instance : HasPairing (StrongDual ℝ E) E ℝ :=
  instHasPairingStrongDualPrimal

local instance : HasPairingSwap E (StrongDual ℝ E) ℝ where
  pairing_swap x xStar := rfl

local instance : HasContinuousPairing (StrongDual ℝ E) E ℝ where
  continuous_pairing_left x := by
    simpa using (ContinuousLinearMap.continuous (ContinuousLinearMap.apply ℝ ℝ x))

namespace Function

local notation "fExt" => toWithTopBotOn f U
local notation "fStar" => (fExt⋆ : StrongDual ℝ E → WithTopBot ℝ)

/-- Corollary 25.1.2 as a Euclidean bridge: if `f` is convex on `U` and differentiable at a
relative-interior point `x ∈ ri[ℝ](U)`, then the dual representative of the gradient determines an
exposed Fenchel-Young contact point on the conjugate epigraph. -/
theorem gradient_mem_exposedPoints_epi_convexConjugate
    (hf_convex : ConvexOn ℝ U f) {x : E} (hx : x ∈ ri[ℝ](U))
    (hfdx : DifferentiableAt ℝ f x) :
    (InnerProductSpace.toDual ℝ E (∇ f x),
      ⟪x, InnerProductSpace.toDual ℝ E (∇ f x)⟫ₚ - f x) ∈
      (epi fStar).exposedPoints ℝ := by
  have hsub :
      ∂ᵣf(x | U) =
        {InnerProductSpace.toDual ℝ E (∇ f x)} :=
    subdifferentialWithinAt_eq_singleton_toDual_gradient hf_convex hx hfdx
  exact mem_exposedPoints_epi_convexConjugate_of_subdifferentialWithinAt_eq_singleton
    (f := f) (U := U)
    (x := x) (xStar := InnerProductSpace.toDual ℝ E (∇ f x))
    (intrinsicInterior_subset hx) hsub

/-- Bridge form of Corollary 25.1.2 on the canonical real-height epigraph surface:
`EReal.toReal (fStar (toDual (∇ f x)))` equals the Fenchel-Young height
`⟪x, toDual (∇ f x)⟫ₚ - f x`. -/
theorem gradient_mem_exposedPoints_epi_convexConjugate_toRealHeight
    (hf_convex : ConvexOn ℝ U f) {x : E} (hx : x ∈ ri[ℝ](U))
    (hfdx : DifferentiableAt ℝ f x) :
    (InnerProductSpace.toDual ℝ E (∇ f x),
      EReal.toReal (fStar (InnerProductSpace.toDual ℝ E (∇ f x)))) ∈
      (epi fStar).exposedPoints ℝ := by
  have hmain :
      (InnerProductSpace.toDual ℝ E (∇ f x),
        ⟪x, InnerProductSpace.toDual ℝ E (∇ f x)⟫ₚ - f x) ∈
        (epi fStar).exposedPoints ℝ :=
    gradient_mem_exposedPoints_epi_convexConjugate hf_convex hx hfdx
  have hsub :
      ∂ᵣf(x | U) =
        {InnerProductSpace.toDual ℝ E (∇ f x)} :=
    subdifferentialWithinAt_eq_singleton_toDual_gradient hf_convex hx hfdx
  have hgrad :
      InnerProductSpace.toDual ℝ E (∇ f x) ∈ ∂ᵣf(x | U) := by
    simp [hsub]
  have hheight :
      EReal.toReal (fStar (InnerProductSpace.toDual ℝ E (∇ f x))) =
        ⟪x, InnerProductSpace.toDual ℝ E (∇ f x)⟫ₚ - f x := by
    have hheight' := congrArg EReal.toReal
      (convexConjugate_eq_apply_sub_of_mem_subdifferentialWithinAt
        (f := f) (U := U) (x := x) (xStar := InnerProductSpace.toDual ℝ E (∇ f x))
        (intrinsicInterior_subset hx) hgrad)
    have hco :
        EReal.toReal (⟪x, InnerProductSpace.toDual ℝ E (∇ f x)⟫ₚ - f x : ℝ) =
          ⟪x, InnerProductSpace.toDual ℝ E (∇ f x)⟫ₚ - f x :=
      EReal.toReal_coe (⟪x, InnerProductSpace.toDual ℝ E (∇ f x)⟫ₚ - f x)
    exact hheight'.trans hco
  rw [hheight]
  exact hmain

end Function

end
