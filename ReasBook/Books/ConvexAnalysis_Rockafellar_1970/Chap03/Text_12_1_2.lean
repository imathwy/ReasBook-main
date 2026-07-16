import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section

variable {𝕜 : Type*} {E : Type u}
variable [Ring 𝕜] [Preorder 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]

namespace AffineMap

/-- Canonical codomain lift for a scalar-valued affine map. -/
abbrev toWithBotTop (h : AffineMap 𝕜 E 𝕜) : E → WithBotTop 𝕜 :=
  Function.toWithBotTop h

omit [Preorder 𝕜] in
@[simp] theorem toWithBotTop_apply (h : AffineMap 𝕜 E 𝕜) (x : E) :
    h.toWithBotTop x = (h x : WithBotTop 𝕜) :=
  rfl

/-- `EReal`-specialized codomain lift, kept as a bridge notation. -/
abbrev toEReal {E : Type u} [AddCommGroup E] [Module ℝ E] (h : AffineMap ℝ E ℝ) : E → EReal :=
  Function.toEReal h

@[simp] theorem toEReal_apply {E : Type u} [AddCommGroup E] [Module ℝ E]
    (h : AffineMap ℝ E ℝ) (x : E) :
    h.toEReal x = (h x : EReal) :=
  rfl

end AffineMap

/-- A scalar-valued affine minorant of `f` is an affine map whose canonical
`WithBotTop` lift lies pointwise below `f`. -/
abbrev AffineMinorant (f : E → WithBotTop 𝕜) :=
  {h : AffineMap 𝕜 E 𝕜 // AffineMap.toWithBotTop h ≤ f}

instance {f : E → WithBotTop 𝕜} : CoeFun (AffineMinorant f) (fun _ ↦ E → 𝕜) where
  coe h := h.1

namespace AffineMinorant

/-- Canonical codomain lift of an affine minorant. -/
abbrev toWithBotTop {f : E → WithBotTop 𝕜} (h : AffineMinorant f) : E → WithBotTop 𝕜 :=
  AffineMap.toWithBotTop h.1

@[simp] theorem toWithBotTop_apply {f : E → WithBotTop 𝕜} (h : AffineMinorant f) (x : E) :
    h.toWithBotTop x = (h x : WithBotTop 𝕜) :=
  rfl

/-- `EReal`-specialized codomain lift of an affine minorant, kept as a bridge surface. -/
abbrev toEReal {E : Type u} [AddCommGroup E] [Module ℝ E] {f : E → EReal}
    (h : AffineMinorant f) : E → EReal :=
  h.1.toEReal

@[simp] theorem toEReal_apply {E : Type u} [AddCommGroup E] [Module ℝ E] {f : E → EReal}
    (h : AffineMinorant f) (x : E) :
    h.toEReal x = (h x : EReal) :=
  rfl

end AffineMinorant

/-- Any affine minorant of `f` lies pointwise below `f`. -/
theorem affineMinorant_le {f : E → WithBotTop 𝕜} (h : AffineMinorant f) :
    h.toWithBotTop ≤ f :=
  h.property

end

open scoped Rockafellar

section

variable {𝕜 : Type*} {X : Type u} {Y : Type v}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommGroup X] [Module 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 12.1.2 characterizes when the affine function
  `x ↦ ⟪x, y⋆⟫ₚ - μ⋆` is majorized by `f`.
- `core/canonical`: the owner constructions are the Fenchel conjugate `convexConjugate` and the
  pairing linear functional `HasLinearPairing.pairingLinear.flip yStar`.
- `bridge/view`: the Chapter 12 affine-minorant owner `AffineMinorant f`, the concrete affine map
  `pairingSubConstAffineMap yStar μStar`, and the explicit textbook formula
  `convexConjugate_eq_iSup_pairing_sub`.

Domain-style sampling used here:
- `HasLinearPairing` and the induced raw pairing `⟪·, ·⟫ₚ`;
- `HasLinearPairing.pairingLinear.flip`;
- `AffineMinorant` and `affineMinorant_le`;
- `convexConjugate`;
- notation `f⋆` from `Defn_12_2`;
- `convexConjugate_eq_iSup_pairing_sub`;
- pointwise order on `WithBotTop 𝕜`-valued functions on a paired module.

Primitive data vs derived API:
- primitive inputs: the affine-minorant owner `AffineMinorant f` and its concrete source-facing
  representative `pairingSubConstAffineMap yStar μStar`;
- derived API: the owner-side inequality `f⋆ xStar ≤ μStar`, the canonical minorant constructor
  `pairingSubConstAffineMinorant`, and the textbook `iSup` reformulation.

Layer target: `source-facing`, stated directly as a criterion for one affine minorant while
reusing the canonical conjugate owner.
-/

variable (yStar : Y) (μStar : 𝕜)

omit [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
@[simp] theorem coe_sub (a b : 𝕜) :
    ((a - b : 𝕜) : WithBotTop 𝕜) = (a : WithBotTop 𝕜) - b := by
  simp [sub_eq_add_neg, WithBotTop.sub_eq_add_neg]

/-- The source-facing affine map `x ↦ ⟪x, y⋆⟫ₚ - μ⋆`. -/
abbrev pairingSubConstAffineMap : AffineMap 𝕜 X 𝕜 :=
  (HasLinearPairing.pairingLinear.flip yStar).toAffineMap + AffineMap.const 𝕜 X (-μStar)

omit [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
@[simp] theorem pairingSubConstAffineMap_apply (x : X) :
    pairingSubConstAffineMap yStar μStar x = ⟪x, yStar⟫ₚ - μStar := by
  simp [pairingSubConstAffineMap, sub_eq_add_neg]

variable {yStar μStar}

-- Proof sketch: rewrite the pointwise inequality
-- `⟪x, y⋆⟫ₚ - μ⋆ ≤ f x` as `⟪x, y⋆⟫ₚ - f x ≤ μ⋆` for each `x`. Taking the supremum over all `x`
-- gives `convexConjugate f y⋆ ≤ μ⋆`, and conversely any upper bound on that supremum bounds each
-- affine defect, recovering the pointwise majorization.
private theorem pairingSubConstAffineMap_le_iff_convexConjugate_le_withBotTop
    (f : X → WithBotTop 𝕜) (yStar : Y) (μStar : 𝕜) :
    (pairingSubConstAffineMap yStar μStar).toWithBotTop ≤ f ↔
      f⋆ yStar ≤ (μStar : WithBotTop 𝕜) := by
  rw [show f⋆ yStar =
      ⨆ x : X, (((⟪x, yStar⟫ₚ : 𝕜) : WithBotTop 𝕜) - f x) by
    simpa using convexConjugate_eq_iSup_pairing_sub f yStar]
  constructor
  · intro h
    refine iSup_le fun x ↦ ?_
    have hx' : (((⟪x, yStar⟫ₚ : 𝕜) : WithBotTop 𝕜) - (μStar : WithBotTop 𝕜)) ≤ f x := by
      simpa [AffineMap.toWithBotTop, Function.toWithBotTop, pairingSubConstAffineMap_apply,
        coe_sub] using
        h x
    have hx'' : (((⟪x, yStar⟫ₚ : 𝕜) : WithBotTop 𝕜)) ≤ f x + (μStar : WithBotTop 𝕜) :=
      (WithBotTop.sub_le_iff_le_add
        (b := (μStar : WithBotTop 𝕜))
        (c := f x)
        (.inl (WithBotTop.coe_ne_bot μStar))
        (.inl (WithBotTop.coe_ne_top μStar))).1 hx'
    exact
      (WithBotTop.sub_le_iff_le_add
        (b := f x)
        (c := (μStar : WithBotTop 𝕜))
        (.inr (WithBotTop.coe_ne_top μStar))
        (.inr (WithBotTop.coe_ne_bot μStar))).2
        (by simpa [add_comm] using hx'')
  · intro h x
    have hx : (((⟪x, yStar⟫ₚ : 𝕜) : WithBotTop 𝕜) - f x) ≤ (μStar : WithBotTop 𝕜) :=
      (le_iSup_of_le x le_rfl).trans h
    have hx' : (((⟪x, yStar⟫ₚ : 𝕜) : WithBotTop 𝕜)) ≤ (μStar : WithBotTop 𝕜) + f x := by
      exact
        (WithBotTop.sub_le_iff_le_add
          (b := f x)
          (c := (μStar : WithBotTop 𝕜))
          (.inr (WithBotTop.coe_ne_top μStar))
          (.inr (WithBotTop.coe_ne_bot μStar))).1 hx
    have hx'' : (((⟪x, yStar⟫ₚ : 𝕜) : WithBotTop 𝕜) - (μStar : WithBotTop 𝕜)) ≤ f x := by
      exact
        (WithBotTop.sub_le_iff_le_add
          (b := (μStar : WithBotTop 𝕜))
          (c := f x)
          (.inl (WithBotTop.coe_ne_bot μStar))
          (.inl (WithBotTop.coe_ne_top μStar))).2
          (by simpa [add_comm] using hx')
    simpa [AffineMap.toWithBotTop, Function.toWithBotTop, pairingSubConstAffineMap_apply,
      coe_sub] using hx''

/-- Text 12.1.2 on the named source-facing affine map: `pairingSubConstAffineMap y⋆ μ⋆`, viewed
in `WithBotTop 𝕜`, is majorized by `f` if and only if `μ⋆` dominates the Fenchel conjugate
`f⋆ y⋆`. -/
theorem pairingSubConstAffineMap_le_iff_convexConjugate_le
    (f : X → WithBotTop 𝕜) (yStar : Y) (μStar : 𝕜) :
    (pairingSubConstAffineMap yStar μStar).toWithBotTop ≤ f ↔
      f⋆ yStar ≤ (μStar : WithBotTop 𝕜) := by
  exact pairingSubConstAffineMap_le_iff_convexConjugate_le_withBotTop f yStar μStar

/-- Text 12.1.2 in the raw pointwise form appearing in the source. -/
theorem affineMinorant_iff_convexConjugate_le
    (f : X → WithBotTop 𝕜) (yStar : Y) (μStar : 𝕜) :
    (fun x : X ↦ ⟪x, yStar⟫ₚ - μStar).toWithBotTop ≤ f ↔
      f⋆ yStar ≤ (μStar : WithBotTop 𝕜) := by
  have hmap :
      (pairingSubConstAffineMap yStar μStar).toWithBotTop =
        (fun x : X ↦ ⟪x, yStar⟫ₚ - μStar).toWithBotTop := by
    funext (x : X)
    simp [pairingSubConstAffineMap_apply, AffineMap.toWithBotTop, Function.toWithBotTop, coe_sub]
  simpa [hmap] using
    (pairingSubConstAffineMap_le_iff_convexConjugate_le_withBotTop f yStar μStar)

/-- The canonical affine minorant attached to a dual point `y⋆` and scalar `μ⋆` dominating
`f⋆ y⋆`. -/
def pairingSubConstAffineMinorant
    (f : X → WithBotTop 𝕜) (yStar : Y) (μStar : 𝕜)
    (h : f⋆ yStar ≤ (μStar : WithBotTop 𝕜)) :
    AffineMinorant f :=
  ⟨pairingSubConstAffineMap yStar μStar,
    (pairingSubConstAffineMap_le_iff_convexConjugate_le f yStar μStar).2 h⟩

@[simp] theorem pairingSubConstAffineMinorant_apply
    (f : X → WithBotTop 𝕜) (yStar : Y) (μStar : 𝕜)
    (h : f⋆ yStar ≤ (μStar : WithBotTop 𝕜)) (x : X) :
    pairingSubConstAffineMinorant f yStar μStar h x = ⟪x, yStar⟫ₚ - μStar := by
  simp [pairingSubConstAffineMinorant]

-- Proof sketch: combine `affineMinorant_iff_convexConjugate_le` with the owner-side textbook
-- formula `convexConjugate_eq_iSup_pairing_sub`.
/-- The affine-minorant criterion can be written in the textbook form
`μ⋆ ≥ sup_x (⟪x, y⋆⟫ₚ - f x)`. -/
theorem pairingSubConstAffineMap_le_iff_ge_iSup_pairing_sub
    (f : X → WithBotTop 𝕜) (yStar : Y) (μStar : 𝕜) :
    (pairingSubConstAffineMap yStar μStar).toWithBotTop ≤ f ↔
      (μStar : WithBotTop 𝕜) ≥
        ⨆ x : X, (((⟪x, yStar⟫ₚ : 𝕜) : WithBotTop 𝕜) - f x) := by
  simpa [convexConjugate_eq_iSup_pairing_sub] using
    (pairingSubConstAffineMap_le_iff_convexConjugate_le f yStar μStar)

theorem affineMinorant_iff_ge_iSup_pairing_sub
    (f : X → WithBotTop 𝕜) (yStar : Y) (μStar : 𝕜) :
    (fun x : X ↦ ⟪x, yStar⟫ₚ - μStar).toWithBotTop ≤ f ↔
      (μStar : WithBotTop 𝕜) ≥
        ⨆ x : X, (((⟪x, yStar⟫ₚ : 𝕜) : WithBotTop 𝕜) - f x) := by
  have hmap :
      (pairingSubConstAffineMap yStar μStar).toWithBotTop =
        (fun x : X ↦ ⟪x, yStar⟫ₚ - μStar).toWithBotTop := by
    funext (x : X)
    simp [pairingSubConstAffineMap_apply, AffineMap.toWithBotTop, Function.toWithBotTop, coe_sub]
  simpa [hmap] using pairingSubConstAffineMap_le_iff_ge_iSup_pairing_sub f yStar μStar

end

section

open scoped Rockafellar

variable {𝕜 : Type*} {E : Type u}
variable [CommRing 𝕜] [AddCommGroup E] [Module 𝕜 E]

namespace AffineMap

/-- Canonical owner form: every affine map to scalars is a `pairingSubConstAffineMap` for the
evaluation pairing against the algebraic dual `Module.Dual 𝕜 E`. -/
theorem exists_eq_pairingSubConstAffineMap (h : AffineMap 𝕜 E 𝕜) :
    ∃ y : Module.Dual 𝕜 E, ∃ μ : 𝕜,
      h = pairingSubConstAffineMap (X := E) (Y := Module.Dual 𝕜 E) y μ := by
  refine ⟨h.linear, -h 0, ?_⟩
  ext x
  rw [pairingSubConstAffineMap_apply]
  have hx : h x = h.linear x + h 0 := by
    simpa using congrArg (fun g : E → 𝕜 ↦ g x) h.decomp
  calc
    h x = h.linear x + h 0 := hx
    _ = (⟪x, h.linear⟫ₚ : 𝕜) + h 0 := by rfl
    _ = (⟪x, h.linear⟫ₚ : 𝕜) - (-h 0) := by simp [sub_eq_add_neg]

end AffineMap

end
