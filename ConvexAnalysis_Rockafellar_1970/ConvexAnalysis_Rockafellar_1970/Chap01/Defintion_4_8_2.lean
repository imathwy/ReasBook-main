import ConvexAnalysis_Rockafellar_1970.Chap01.HasPairing
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Pointwise ENNReal NNReal

universe u v w

section SupportFunction

variable {X : Type u} {Y : Type v} {L : Type w}
variable [SupSet L] [HasPairing X Y L]

open scoped Rockafellar

/-
Source/core/bridge triage:
- `source-facing`: Definition 4.8.2 (1) introduces the support function `δᵛ(· | C)` attached to a
  subset `C` on the dual side of a pairing.
- `core/canonical`: no upstream project/mathlib owner names this support function, so the chapter
  owner is `supportFunction C : X → L` itself, defined directly as the supremum of the pairing
  image set over `C`.
- `bridge/view`: the source notation `δᵛ(x | C)` is a pointwise view of the owner, and
  `supportFunction_def` gives the subtype-indexed `iSup` bridge used by pointwise rewriting;
  `supportFunction_eq_iSup` is the canonical function-valued bridge used for rewriting under
  function operators. The theorem `supportFunction_eq_iSup_apply` is its pointwise companion.
- Primitive data vs derived API: the primitive data are only the set `C`, the ambient pairing, and
  the resulting function `supportFunction C`. No convexity or nonemptiness hypothesis belongs in
  the definition itself.
- Domain-style sampling used here: the intrinsic set-image supremum `sSup ((fun y ↦ ...) '' C)`,
  its subtype-indexed bridge `⨆ y : C, ...`, together with mathlib's canonical
  Minkowski-functional owners `gauge`/`egauge` for the adjacent clause of the same definition, and
  the existing chapter theorem surface that already writes support
  functions as `δᵛ(· | C)`.
-/
/-- The support-function owner attached to a subset `C`. -/
def supportFunction (C : Set Y) : X → L :=
  fun x ↦ sSup ((fun y : Y ↦ (⟪x, y⟫ₚ : L)) '' C)

scoped[Rockafellar] notation3:max "δᵛ(" x " | " C ")" => supportFunction C x
scoped[Rockafellar] notation3:max "δᵛ[" L "](" x " | " C ")" =>
  supportFunction (L := L) C x

/-- Defintion 4.8.2: clause (1) identifies the support-function value with the supremum of the
pairing image of the set. -/
theorem supportFunction_eq_sSup (C : Set Y) (x : X) :
    δᵛ(x | C) = sSup ((fun y : Y ↦ (⟪x, y⟫ₚ : L)) '' C) :=
  rfl

/-- The support-function owner is the supremum of the pairing values indexed by the set. -/
theorem supportFunction_def (C : Set Y) (x : X) :
    δᵛ(x | C) = (⨆ y : C, (⟪x, (y : Y)⟫ₚ : L)) := by
  rw [supportFunction]
  simpa using (sSup_image' (s := C) (f := fun y ↦ (⟪x, y⟫ₚ : L)))

/-- Function-valued bridge for rewriting under operators whose codomain already fixes the pairing
instance. -/
theorem supportFunction_eq_iSup (C : Set Y) :
    (δᵛ(· | C) : X → L) = (⨆ y : C, (⟪·, (y : Y)⟫ₚ : X → L)) := by
  funext x
  simpa [iSup_apply] using (supportFunction_def (C := C) (x := x))

/-- Pointwise form of `supportFunction_eq_iSup`. -/
theorem supportFunction_eq_iSup_apply (C : Set Y) (x : X) :
    δᵛ(x | C) = (⨆ y : C, (⟪x, (y : Y)⟫ₚ : L)) := by
  simpa [iSup_apply] using congrFun (supportFunction_eq_iSup (C := C)) x

end SupportFunction

section SupportFunctionSupSet

variable {X : Type u} {Y : Type v} {L : Type w}
variable [SupSet L] [HasPairing X Y L]

open scoped Rockafellar

/-- Intrinsic set-image bridge: at the primitive `SupSet` layer, the support-function value is the
supremum of the pairing image of the set. This is the set-level counterpart of the subtype-indexed
owner formula `supportFunction_def`. -/
theorem supportFunction_eq_sSup_image (C : Set Y) (x : X) :
    δᵛ(x | C) = sSup ((fun y : Y ↦ (⟪x, y⟫ₚ : L)) '' C) :=
  rfl

end SupportFunctionSupSet

section SupportFunctionSup

variable {X : Type u} {Y : Type v} {L : Type w}
variable [ConditionallyCompletePartialOrderSup L] [HasPairing X Y L]

open scoped Rockafellar

/-- The support function of a singleton is the corresponding pairing functional. -/
theorem supportFunction_singleton (a : Y) (x : X) :
    δᵛ(x | ({a} : Set Y)) = (⟪x, a⟫ₚ : L) := by
  simp [supportFunction_def]

end SupportFunctionSup

/- Definition 4.8.2 (2): the owner-level gauge notation over an explicit scalar type is
`γ[𝕜](x | C) = egauge 𝕜 C x`. The chapter-default source notation keeps Rockafellar's
nonnegative-scalar surface `γ(x | C) = egauge ℝ≥0 C x`. -/
scoped[Rockafellar] notation3:max "γ[" 𝕜 "](" x " | " C ")" => egauge 𝕜 C x
scoped[Rockafellar] notation3:max "γ(" x " | " C ")" => egauge ℝ≥0 C x

section Gauge

variable {𝕜 : Type w} [NNNorm 𝕜]
variable {E : Type u} [SMul 𝕜 E]

open scoped Rockafellar

/-
Source/core/bridge triage:
- `source-facing`: Definition 4.8.2 (2) introduces Rockafellar's gauge `γ(· | C)` for an arbitrary
  set `C`.
- `core/canonical`: the owner abstraction is mathlib's extended Minkowski functional
  `egauge 𝕜 : Set E → E → ℝ≥0∞`, at the primitive scalar layer `[NNNorm 𝕜] [SMul 𝕜 E]`.
- `bridge/view`: `γ[𝕜](x | C)` is the scalar-parameterized source view of this owner; `γ(x | C)`
  is the chapter-default specialization `𝕜 = ℝ≥0`.
- Primitive data vs derived API: there is no additional source-level data beyond the set `C`; the
  `sInf` expression is derived API for the existing owner `egauge 𝕜`.
- Domain-style sampling used here: mathlib's `egauge` and the lattice bridge `sInf_image`.
-/

/-- Owner-level infimum formula for the extended Minkowski functional over any scalar type with an
`NNNorm` and scalar action. -/
theorem egauge_eq_sInf_dilates (C : Set E) (x : E) :
    egauge 𝕜 C x = sInf (enorm '' {c : 𝕜 | x ∈ c • C}) := by
  rw [egauge, sInf_image]
  rfl

/-- Source-facing notation bridge for `egauge_eq_sInf_dilates`. -/
theorem gauge_eq_sInf_dilates (C : Set E) (x : E) :
    γ[𝕜](x | C) = sInf (enorm '' {c : 𝕜 | x ∈ c • C}) := by
  simpa using (egauge_eq_sInf_dilates (𝕜 := 𝕜) (C := C) (x := x))

end Gauge

section GaugeNNReal

variable {E : Type u} [SMul ℝ≥0 E]

open scoped Rockafellar

/-- The chapter-default gauge `γ(· | C)` is the infimum of nonnegative scalars whose dilates of
`C` contain `x`. -/
theorem egauge_eq_sInf_nonneg_dilates (C : Set E) (x : E) :
    egauge ℝ≥0 C x = sInf (enorm '' {c : ℝ≥0 | x ∈ c • C}) := by
  simpa using (egauge_eq_sInf_dilates (𝕜 := ℝ≥0) (C := C) (x := x))

/-- Source-facing notation bridge for `egauge_eq_sInf_nonneg_dilates`. -/
theorem gauge_eq_sInf_nonneg_dilates (C : Set E) (x : E) :
    γ(x | C) = sInf (enorm '' {c : ℝ≥0 | x ∈ c • C}) := by
  simpa using (egauge_eq_sInf_nonneg_dilates (C := C) (x := x))

end GaugeNNReal
