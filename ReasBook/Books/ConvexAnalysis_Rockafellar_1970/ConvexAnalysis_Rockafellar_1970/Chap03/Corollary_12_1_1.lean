import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_5_3
import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_7_2_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_12_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

open scoped Rockafellar

variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] [FiniteDimensional ℝ E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 12.1.1 states that `cl (conv f)` is the pointwise supremum of all
  affine functions majorized by `f`.
- `core/canonical`: the owner constructions used here are `Function.convexHull` for `conv f`,
  `lowerSemicontinuousHull` for `cl`, and the Fenchel biconjugate
  `convexConjugate (convexConjugate f)`, with
  `biconjugate_apply_eq_iSup_affineMinorant`.
- `bridge/view`: the source-facing affine-minorant supremum is rendered by the subtype
  `AffineMinorant f`; the only extra bridge needed here is the canonical identification of the
  affine minorants of `f` with those of `cl (conv f)`.

Domain-style sampling used here:
- `Function.convexHull`, `Function.conv_le`, and `Function.le_conv_of_le`;
- `lowerSemicontinuousHull` and `le_lowerSemicontinuousHull`;
- `eq_iSup_affineMinorant_of_isConvex_of_lowerSemicontinuous`;
- `AffineMap`;
- pointwise `iSup`/`sInf` constructions on `WithBotTop ℝ`-valued functions.

Primitive data vs derived API:
- primitive input: the function `f : E → WithBotTop ℝ`;
- owner constructions reused directly from upstream: `conv(f)`, `cl`, and the affine-minorant
  owner theorem for closed convex functions;
- derived API here: the source-facing affine-minorant formula for `cl (conv f)`.

Layer target:
- `core/canonical`: this file now exposes the primitive pairing-level statement with the explicit
  representation datum `AffineMinorant.IsPairingSubConstRepresentable`;
- `source-facing`: a final bridge theorem specializes that canonical owner to finite-dimensional
  real inner-product spaces, where the representation datum is supplied by the canonical
  inner-product affine-representation bridge proved locally in this file.
-/

private theorem affineMap_lowerSemicontinuous (h : AffineMap ℝ E ℝ) :
    LowerSemicontinuous (fun x : E ↦ ((h x : ℝ) : WithBotTop ℝ)) := by
  have hcont_real : Continuous (fun x : E ↦ (h x : ℝ)) := by
    exact (AffineMap.continuous_linear_iff).1 (h.linear.continuous_of_finiteDimensional)
  have hcont : Continuous (fun x : E ↦ ((h x : ℝ) : WithBotTop ℝ)) := by
    simpa using continuous_coe_real_ereal.comp hcont_real
  exact hcont.lowerSemicontinuous

theorem affineMinorant_cl_conv_iff
    (f : E → WithBotTop ℝ) (h : AffineMap ℝ E ℝ) :
    (∀ x : E, ((h x : ℝ) : WithBotTop ℝ) ≤ cl(conv(f)) x) ↔
      ∀ x : E, ((h x : ℝ) : WithBotTop ℝ) ≤ f x := by
  constructor
  · intro hh x
    exact le_trans (hh x) <|
      le_trans (lowerSemicontinuousHull_le (conv(f)) x) (Function.conv_le f x)
  · intro hh x
    exact le_lowerSemicontinuousHull
      (affineMap_lowerSemicontinuous h)
      (Function.le_conv_of_le
        (by
          simpa [Function.toWithBotTop] using
            (Function.isConvex_coe_of_convexOn_univ h.convexOn_univ))
        hh) x

private abbrev affineMinorantClConvEquiv (f : E → WithBotTop ℝ) :
    AffineMinorant (cl(conv(f))) ≃ AffineMinorant f :=
  Equiv.subtypeEquivRight fun h : AffineMap ℝ E ℝ ↦ affineMinorant_cl_conv_iff f h

-- Proof sketch: `cl (conv f)` is closed and convex by the owner theorems for `cl`, `conv`, and
-- Fenchel biconjugacy, so Theorem 12.1 applies directly to it. The remaining point is that an
-- affine function is majorized by `cl (conv f)` exactly when it is majorized by `f`: the forward
-- implication uses `cl (conv f) ≤ conv f ≤ f`, while the reverse implication uses that every
-- affine function is convex and lower semicontinuous, hence is a minorant of both `conv f` and
-- `cl (conv f)`. Transport the `iSup` along that equivalence of affine-minorant types.
/-- Canonical owner form of Corollary 12.1.1 on the pairing layer: if affine minorants of
`cl(conv(f))` admit the Chapter 12 pairing representation, then `cl(conv(f)) x` is the supremum
of values of affine minorants of `f` at `x`. -/
theorem cl_conv_apply_eq_iSup_affineMinorant_of_isPairingSubConstRepresentable
    [HasLinearPairing E E ℝ] [HasContinuousPairing E E ℝ] [HasPairingSwap E E ℝ]
    (f : E → WithBotTop ℝ) (x : E)
    (h_affine : AffineMinorant.IsPairingSubConstRepresentable (cl(conv(f)))) :
    cl(conv(f)) x = ⨆ h : AffineMinorant f, h.toWithBotTop x := by
  let e : AffineMinorant (cl(conv(f))) ≃ AffineMinorant f := affineMinorantClConvEquiv f
  have hcl_convex : (cl(conv(f))).IsConvex ℝ := by
    exact Function.IsConvex.lowerSemicontinuousHull_isConvex
      (f := conv(f)) (Function.isConvex_conv f)
  calc
    _ = ⨆ h : AffineMinorant (cl(conv(f))), h.toWithBotTop x :=
      eq_iSup_affineMinorant_of_isConvex_of_lowerSemicontinuous
        (cl(conv(f))) hcl_convex (lowerSemicontinuous_lowerSemicontinuousHull (conv(f)))
        h_affine x
    _ = ⨆ h : AffineMinorant f, h.toWithBotTop x := Equiv.iSup_congr e fun _ ↦ rfl

end

section

open scoped RealInnerProductSpace Rockafellar

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- Proof sketch: on finite-dimensional real inner-product spaces, every affine map to `ℝ` is a
-- `pairingSubConstAffineMap`, so the representation datum in the canonical owner theorem above is
-- automatic.
private theorem affineMap_exists_eq_pairingSubConstAffineMap_of_inner
    (h : AffineMap ℝ E ℝ) :
    ∃ y : E, ∃ μ : ℝ, h = pairingSubConstAffineMap y μ := by
  letI : HasLinearPairing E E ℝ := instHasLinearPairingInner E
  let y : E := (InnerProductSpace.toDual ℝ E).symm (LinearMap.toContinuousLinearMap h.linear)
  let μ : ℝ := -h 0
  refine ⟨y, μ, ?_⟩
  ext x
  have hy : h.linear x = ⟪y, x⟫ := by
    dsimp [y]
    exact
      (InnerProductSpace.toDual_symm_apply
        (𝕜 := ℝ) (E := E) (x := x) (y := LinearMap.toContinuousLinearMap h.linear)).symm
  have hx : h x = h.linear x + h 0 := by
    simpa using congrArg (fun g : E → ℝ ↦ g x) h.decomp
  calc
    h x = h.linear x + h 0 := hx
    _ = ⟪y, x⟫ + h 0 := by rw [hy]
    _ = ⟪x, y⟫ₚ - μ := by
      calc
        ⟪y, x⟫ + h 0 = inner ℝ x y - μ := by
          simp [μ, real_inner_comm, sub_eq_add_neg, add_comm]
        _ = ⟪x, y⟫ₚ - μ := by rfl
    _ = pairingSubConstAffineMap y μ x := by
      rw [pairingSubConstAffineMap_apply]

/-- Corollary 12.1.1 (source-facing bridge): for any function `f` on a finite-dimensional real
inner-product space, and hence in particular on `R^n`, the closed convex hull `cl (conv f)` is
pointwise the supremum of all affine functions majorized by `f`. -/
theorem lowerSemicontinuousHull_convexHullFunction_apply_eq_iSup_affineMinorant
    (f : E → WithBotTop ℝ) (x : E) :
    cl(conv(f)) x = ⨆ h : AffineMinorant f, h.toWithBotTop x := by
  letI : HasLinearPairing E E ℝ := instHasLinearPairingInner E
  letI : HasContinuousPairing E E ℝ := instHasContinuousPairingInner E
  letI : HasPairingSwap E E ℝ := instHasPairingSwapInner E
  have h_affine : AffineMinorant.IsPairingSubConstRepresentable (cl(conv(f))) := by
    intro h
    exact affineMap_exists_eq_pairingSubConstAffineMap_of_inner h.1
  exact
    cl_conv_apply_eq_iSup_affineMinorant_of_isPairingSubConstRepresentable
      f x h_affine

end
