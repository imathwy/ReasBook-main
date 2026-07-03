import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_12_1_1 (from Chap03) -/
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

/-! ### Text_12_1_1 (from Chap03) -/
section

open scoped Rockafellar

universe u v

variable {X : Type u} {Y : Type v} {𝕜 : Type*}
variable [Preorder 𝕜] [HasPairing X Y 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 12.1.1 specializes the affine-minorant condition `h ≤ f` to the indicator
  function of a convex set `C` and to the source affine profile `h(x) = ⟪x, y⋆⟫ₚ - β`.
- `core/canonical`: the owner abstractions are the pointwise order on
  `WithBotTop`-valued functions, the chapter indicator bridge `indicatorFunction C`,
  the generic codomain lift `Function.toWithBotTop`, and the half-space
  `closedHalfSpaceLE yStar β`.
- `bridge/view`: the intermediate source wording "`h(x) ≤ 0` for every `x ∈ C`" is kept as a thin
  companion theorem between the function-order statement and the half-space containment statement.

Domain-style sampling used here:
- `indicatorFunction` and `indicator_def` from `Defintion_4_8_1`;
- `Function.toWithBotTop` from `Chap01.EOrder.Basic`;
- `closedHalfSpaceLE` and `mem_closedHalfSpaceLE_iff` from `Definition_2_0_3`;
- the pointwise order on `WithBotTop`-valued functions already used in Chapter 12.

Layer target: `bridge/view`; the public statement keeps the source specialization explicit and
expresses the final conclusion through the canonical half-space containment API.

Although the source states this in `R^n`, the owner declarations used here only need a pairing into
an ordered scalar layer, so the file is kept at that primitive ambient level.
-/

-- Proof sketch: outside `C`, the indicator has value `⊤`, so the inequality is automatic. On `C`,
-- the indicator has value `0`, so pointwise domination is exactly the condition
-- `⟪x, y⋆⟫ₚ - β ≤ 0`.
/-- The affine profile `x ↦ ⟪x, y⋆⟫ₚ - β`, viewed in `WithBotTop 𝕜`, lies below the indicator of
`C` exactly when it is nonpositive on `C`. -/
private theorem affineFunction_le_indicatorFunction_iff_nonpos_on_set
    [Zero 𝕜] [Sub 𝕜]
    (C : Set X) (yStar : Y) (β : 𝕜) :
    (fun x : X ↦ ⟪x, yStar⟫ₚ - β).toWithBotTop ≤ (δ(· | C) : X → WithBotTop 𝕜) ↔
      ∀ x ∈ C, ⟪x, yStar⟫ₚ - β ≤ 0 := by
  constructor
  · intro h x hx
    have hx' : (((⟪x, yStar⟫ₚ - β : 𝕜) : WithBotTop 𝕜)) ≤ 0 := by
      simpa [hx] using h x
    exact WithBotTop.coe_le_coe_iff.mp hx'
  · intro h x
    by_cases hx : x ∈ C
    · have hx' : ⟪x, yStar⟫ₚ - β ≤ 0 := h x hx
      have hx'' : (((⟪x, yStar⟫ₚ - β : 𝕜) : WithBotTop 𝕜)) ≤ 0 := by
        exact WithBotTop.coe_le_coe_iff.mpr hx'
      simpa [hx] using hx''
    · change (((⟪x, yStar⟫ₚ - β : 𝕜) : WithBotTop 𝕜)) ≤ (δ(x | C) : WithBotTop 𝕜)
      rw [indicator_def, if_neg hx]
      exact le_top

-- Proof sketch: first reduce `h ≤ indicatorFunction C` to the condition `⟪x, y⋆⟫ₚ - β ≤ 0` on
-- points of `C`. Then rewrite `⟪x, y⋆⟫ₚ - β ≤ 0` as `⟪x, y⋆⟫ₚ ≤ β` and use
-- `mem_closedHalfSpaceLE_iff` to identify this with `x ∈ closedHalfSpaceLE yStar β`.
variable [AddGroup 𝕜] [AddRightMono 𝕜]

-- Proof sketch: combine the indicator-majorization/nonpositivity bridge with the canonical
-- half-space membership lemma `mem_closedHalfSpaceLE_iff`.
private theorem affineFunction_le_indicatorFunction_iff_subset_closedHalfSpaceLE
    (C : Set X) (yStar : Y) (β : 𝕜) :
    (fun x : X ↦ ⟪x, yStar⟫ₚ - β).toWithBotTop ≤ (δ(· | C) : X → WithBotTop 𝕜) ↔
      C ⊆ closedHalfSpaceLE yStar β := by
  rw [affineFunction_le_indicatorFunction_iff_nonpos_on_set]
  constructor
  · intro h x hx
    rw [mem_closedHalfSpaceLE_iff]
    exact le_of_sub_nonpos (h x hx)
  · intro h x hx
    exact sub_nonpos.mpr (mem_closedHalfSpaceLE_iff.mp (h hx))

/-- Text 12.1.1: a set `C` lies in the closed half-space `{x | ⟪x, y⋆⟫ₚ ≤ β}` exactly when the
affine profile `x ↦ ⟪x, y⋆⟫ₚ - β`, viewed in `WithBotTop 𝕜`, lies below the indicator of `C`. -/
theorem subset_closedHalfSpaceLE_iff_affineFunction_le_indicatorFunction
    (C : Set X) (yStar : Y) (β : 𝕜) :
    C ⊆ closedHalfSpaceLE yStar β ↔
      (fun x : X ↦ ⟪x, yStar⟫ₚ - β).toWithBotTop ≤ (δ(· | C) : X → WithBotTop 𝕜) := by
  exact (affineFunction_le_indicatorFunction_iff_subset_closedHalfSpaceLE (C := C)
    (yStar := yStar) (β := β)).symm

end

/-! ### Theorem_12_1 (from Chap03) -/
noncomputable section

open scoped Rockafellar

universe u v w

section

variable {𝕜 : Type w} {X : Type u} {Y : Type v}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommGroup X] [Module 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

/-- Pairing-side representation bridge for affine minorants of `f` on a paired module. -/
abbrev AffineMinorant.IsPairingSubConstRepresentable (f : X → WithTopBot 𝕜) : Prop :=
  ∀ h : AffineMinorant f, ∃ y : Y, ∃ μ : 𝕜, h.1 = pairingSubConstAffineMap y μ

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 12.1 says that a closed convex function is recovered as the pointwise
  supremum of all affine functions lying below it.
- `core/canonical`: the chapter owner constructions are `convexConjugate` and the dual biconjugate
  `f⋆⋆`, while convexity and closedness are rendered by
  `Function.IsConvex` and
  `LowerSemicontinuous`.
- `bridge/view`: the family of affine maps `h ≤ f` is organized as the subtype `AffineMinorant f`,
  and the textbook affine-minorant supremum is exposed by the pointwise bridge theorem
  `biconjugate_apply_eq_iSup_affineMinorant`.

Domain-style sampling used here:
- `AffineMinorant` and `affineMinorant_le` from `Text_12_1_2`;
- `Function.IsConvex` from `Theorem_4_2`;
- `convexConjugate`, `convexConjugate_eq_iSup_pairing_sub`, and
  `convexConjugate_convexConjugate_eq_iSup_pairing_sub` from `Defn_12_2`;
- `AffineMinorant.IsPairingSubConstRepresentable` and the source-facing normal-form owner
  `pairingSubConstAffineMap` from
  `Text_12_1_2`;
- the complete-lattice pointwise supremum on `WithTopBot 𝕜`-valued functions.
- Primitive data vs derived API: the primitive input is the function `f : X → WithTopBot 𝕜`; the
  canonical owner is the dual biconjugate `f⋆⋆`, while
  `AffineMinorant f`, the explicit affine-representation hypothesis, and the pointwise
  supremum-over-minorants formula are bridge-level API.
- Layer target: `source-facing`; the theorem keeps the affine-minorant wording of the source, but
  the implementation-facing owner is the canonical biconjugate rather than a parallel local
  supremum function. The bridge layer `AffineMinorant f` itself is stated on the primitive
  scalar/pairing owner ambient already required by `AffineMap 𝕜 X 𝕜`; concrete realizations such
  as finite-dimensional inner-product spaces can be used downstream as bridges to discharge the
  explicit representation hypothesis.
-/

-- Proof sketch: the biconjugate is the supremum of the affine functions
-- `x ↦ ⟪x, x⋆⟫ - convexConjugate f x⋆`. The explicit affine-representation hypothesis below says
-- every affine minorant has this form, and Text 12.1.2 identifies the admissible constants
-- precisely as those dominating `convexConjugate f x⋆`. Therefore the biconjugate is exactly the
-- supremum over all affine minorants.
variable [HasPairing Y X 𝕜] [HasPairingSwap X Y 𝕜]

/-- Evaluating the Fenchel biconjugate `f**` at `x` gives the textbook supremum of the values of
all affine minorants of `f` at `x`. The ambient model layer is exposed through the explicit
representation hypothesis `h_affine`, so this theorem is stated on the pairing owner rather than
on a concrete inner-product model. -/
theorem biconjugate_apply_eq_iSup_affineMinorant
    (f : X → WithTopBot 𝕜) (x : X)
    (h_affine : AffineMinorant.IsPairingSubConstRepresentable f) :
    (f⋆⋆) x =
      ⨆ h : AffineMinorant f, h.toWithBotTop x := by
  apply le_antisymm
  · rw [convexConjugate_convexConjugate_eq_iSup_pairing_sub (f := f) (x := x)]
    refine iSup_le ?_
    intro y
    by_cases hy_top : f⋆ y = (⊤ : WithTopBot 𝕜)
    · have hbot :
        ((⟪y, x⟫ₚ : WithTopBot 𝕜) - f⋆ y) = (⊥ : WithTopBot 𝕜) := by
        rw [hy_top]
        exact WithBotTop.sub_top (⟪y, x⟫ₚ : WithTopBot 𝕜)
      rw [hbot]
      exact bot_le
    · by_cases hy_bot : f⋆ y = (⊥ : WithTopBot 𝕜)
      · have h_all_ge :
          ∀ a : 𝕜, (a : WithTopBot 𝕜) ≤ ⨆ h : AffineMinorant f, h.toWithBotTop x := by
          intro a
          let μ : 𝕜 := (⟪x, y⟫ₚ : 𝕜) - a
          have hμ : f⋆ y ≤ (μ : WithTopBot 𝕜) := by simp [hy_bot]
          let hminor : AffineMinorant f := pairingSubConstAffineMinorant f y μ hμ
          have ha : (a : WithTopBot 𝕜) = hminor.toWithBotTop x := by
            change (a : WithTopBot 𝕜) = ((hminor x : 𝕜) : WithTopBot 𝕜)
            rw [show hminor x = (⟪x, y⟫ₚ : 𝕜) - μ by
              simp [hminor, pairingSubConstAffineMinorant_apply]]
            have h𝕜 : (⟪x, y⟫ₚ : 𝕜) - μ = a := by
              dsimp [μ]
              ring
            rw [h𝕜]
          simpa [ha] using
            (le_iSup_of_le hminor le_rfl :
              hminor.toWithBotTop x ≤ ⨆ h : AffineMinorant f, h.toWithBotTop x)
        have hsup_top : (⨆ h : AffineMinorant f, h.toWithBotTop x) = (⊤ : WithTopBot 𝕜) := by
          refine
            (WithBot.eq_top_iff_forall_ge
              (x := (⨆ h : AffineMinorant f, h.toWithBotTop x))).2 ?_
          intro a
          simpa using h_all_ge a
        have htop :
            ((⟪y, x⟫ₚ : WithTopBot 𝕜) - f⋆ y) = (⊤ : WithTopBot 𝕜) := by
          have hpair_ne_bot : ((⟪y, x⟫ₚ : WithTopBot 𝕜) ≠ (⊥ : WithTopBot 𝕜)) :=
            WithBotTop.coe_ne_bot _
          rw [hy_bot]
          exact WithBotTop.sub_bot (x := (⟪y, x⟫ₚ : WithTopBot 𝕜)) hpair_ne_bot
        rw [htop, hsup_top]
      · rcases WithBot.ne_bot_iff_exists.mp hy_bot with ⟨rTop, hrTop⟩
        have hrTop_ne_top : rTop ≠ (⊤ : WithTop 𝕜) := by
          intro htop
          apply hy_top
          calc
            f⋆ y = ((rTop : WithTop 𝕜) : WithTopBot 𝕜) := hrTop.symm
            _ = ((⊤ : WithTop 𝕜) : WithTopBot 𝕜) := by simp [htop]
            _ = (⊤ : WithTopBot 𝕜) := rfl
        rcases WithTop.ne_top_iff_exists.mp hrTop_ne_top with ⟨μ, hμrTop⟩
        have hfstar_eq : f⋆ y = (μ : WithTopBot 𝕜) := by
          calc
            f⋆ y = ((rTop : WithTop 𝕜) : WithTopBot 𝕜) := hrTop.symm
            _ = ((μ : WithTop 𝕜) : WithTopBot 𝕜) := by simp [hμrTop]
            _ = (μ : WithTopBot 𝕜) := rfl
        have hμ : f⋆ y ≤ (μ : WithTopBot 𝕜) := by simp [hfstar_eq]
        let hminor : AffineMinorant f := pairingSubConstAffineMinorant f y μ hμ
        have hminor_val :
            hminor.toWithBotTop x =
              (((⟪x, y⟫ₚ : 𝕜) : WithTopBot 𝕜) - (μ : WithTopBot 𝕜)) := by
          change ((hminor x : 𝕜) : WithTopBot 𝕜) = _
          rw [show hminor x = (⟪x, y⟫ₚ : 𝕜) - μ by
            simp [hminor, pairingSubConstAffineMinorant_apply]]
          simp [coe_sub]
        have hminor_le :
            hminor.toWithBotTop x ≤ ⨆ h : AffineMinorant f, h.toWithBotTop x :=
          le_iSup_of_le hminor le_rfl
        have hswap :
            (((⟪y, x⟫ₚ : 𝕜) : WithTopBot 𝕜) - (μ : WithTopBot 𝕜)) =
              (((⟪x, y⟫ₚ : 𝕜) : WithTopBot 𝕜) - (μ : WithTopBot 𝕜)) := by
          exact
            congrArg
              (fun t : 𝕜 ↦ ((t : WithTopBot 𝕜) - (μ : WithTopBot 𝕜)))
              (HasPairingSwap.pairing_swap (x := x) (y := y)).symm
        calc
          (((⟪y, x⟫ₚ : 𝕜) : WithTopBot 𝕜) - f⋆ y)
              = (((⟪y, x⟫ₚ : 𝕜) : WithTopBot 𝕜) - (μ : WithTopBot 𝕜)) := by
                simp [hfstar_eq]
          _ = (((⟪x, y⟫ₚ : 𝕜) : WithTopBot 𝕜) - (μ : WithTopBot 𝕜)) := hswap
          _ = hminor.toWithBotTop x := hminor_val.symm
          _ ≤ ⨆ h : AffineMinorant f, h.toWithBotTop x := hminor_le
  · refine iSup_le ?_
    intro h
    rcases h_affine h with ⟨y, μ, hrepr⟩
    have hminorant : (pairingSubConstAffineMap y μ).toWithBotTop ≤ f := by
      simpa [hrepr] using h.property
    have hμ : f⋆ y ≤ (μ : WithTopBot 𝕜) := by
      exact
        (pairingSubConstAffineMap_le_iff_convexConjugate_le (f := f) y μ).1 hminorant
    have hy :
        (((⟪y, x⟫ₚ : 𝕜) : WithTopBot 𝕜) - (μ : WithTopBot 𝕜)) ≤
          (f⋆⋆) x := by
      have hy' :
          (((⟪y, x⟫ₚ : 𝕜) : WithTopBot 𝕜) - (μ : WithTopBot 𝕜)) ≤
            (((⟪y, x⟫ₚ : 𝕜) : WithTopBot 𝕜) - f⋆ y) := by
        exact WithBotTop.sub_le_sub le_rfl hμ
      exact le_trans hy' (le_iSup_of_le y le_rfl)
    have hx :
        h.toWithBotTop x = (((⟪x, y⟫ₚ : 𝕜) : WithTopBot 𝕜) - (μ : WithTopBot 𝕜)) := by
      change ((h x : 𝕜) : WithTopBot 𝕜) = _
      rw [show h x = (⟪x, y⟫ₚ : 𝕜) - μ by simp [hrepr, pairingSubConstAffineMap_apply]]
      simp [coe_sub]
    calc
      h.toWithBotTop x = (((⟪x, y⟫ₚ : 𝕜) : WithTopBot 𝕜) - (μ : WithTopBot 𝕜)) := hx
      _ = (((⟪y, x⟫ₚ : 𝕜) : WithTopBot 𝕜) - (μ : WithTopBot 𝕜)) := by
        exact
          congrArg
            (fun t : 𝕜 ↦ ((t : WithTopBot 𝕜) - (μ : WithTopBot 𝕜)))
            (HasPairingSwap.pairing_swap (x := x) (y := y))
      _ ≤ (f⋆⋆) x := hy

/-- If `f` is recovered pointwise by its biconjugate, then the value at `x` is the supremum of
its affine minorants at `x`. This is the source-facing bridge from the canonical owner equation
`f⋆⋆ = f` to the affine-minorant formula. -/
theorem eq_iSup_affineMinorant_of_eq_biconjugate
    (f : X → WithTopBot 𝕜)
    (hf_biconj : f⋆⋆ = f) (x : X)
    (h_affine : AffineMinorant.IsPairingSubConstRepresentable f) :
    f x = ⨆ h : AffineMinorant f, h.toWithBotTop x := by
  have hf_biconj_x : (f⋆⋆) x = f x := by
    simpa using congrArg (fun g : X → WithTopBot 𝕜 ↦ g x) hf_biconj
  calc
    f x = (f⋆⋆) x := hf_biconj_x.symm
    _ = ⨆ h : AffineMinorant f, h.toWithBotTop x :=
      biconjugate_apply_eq_iSup_affineMinorant
        f x h_affine

end

section

variable {X : Type u} {Y : Type v} {L : Type*}
variable [CompleteLattice L] [AddCommGroup L] [AddRightMono L]
variable [HasPairing X Y L] [HasPairing Y X L] [HasPairingSwap X Y L]

/-- The Fenchel dual biconjugate lies pointwise below `f` on any swap-compatible paired ambient.
-/
-- Proof sketch: for each `y`, the point `x` is one candidate in the supremum defining `f⋆ y`,
-- so `⟪x, y⟫ₚ - f⋆ y ≤ f x`. Symmetry rewrites the biconjugate summands
-- `⟪y, x⟫ₚ - f⋆ y` to the same form, and then taking the supremum over `y` yields `f** x ≤ f x`.
theorem biconjugate_le
    (f : X → L) :
    f⋆⋆ ≤ f := by
  intro x
  change (⨆ y : Y, (((⟪y, x⟫ₚ : L) - (f⋆ y)) : L)) ≤ f x
  refine iSup_le ?_
  intro y
  have hy : (((⟪x, y⟫ₚ : L) - f x) : L) ≤ f⋆ y := by
    exact le_iSup_of_le x le_rfl
  have hy' : (⟪x, y⟫ₚ : L) ≤ f⋆ y + f x := (sub_le_iff_le_add).1 hy
  have hy'' : (((⟪x, y⟫ₚ : L) - (f⋆ y)) : L) ≤ f x := by
    exact (sub_le_iff_le_add).2 (by simpa [add_comm] using hy')
  simpa [HasPairingSwap.pairing_swap (x := y) (y := x)] using hy''

end

section

variable {𝕜 : Type w} {E : Type u}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [TopologicalSpace 𝕜] [NoBotOrder 𝕜] [NoMinOrder 𝕜] [Nonempty 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)]
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
variable [FiniteDimensional 𝕜 E] [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜]

-- Proof sketch: this is the closed-case biconjugacy theorem on the finite-dimensional real
-- pairing layer. The upstream owner theorem gives `f⋆⋆ = cl(f)` under convexity; lower
-- semicontinuity identifies `cl(f) = f`, yielding `f⋆⋆ = f`.
/-- Theorem 12.1 on the canonical owner: on a finite-dimensional scalar-field space with a
continuous linear self-pairing, a closed convex function (expressed by
`LowerSemicontinuous f` and `f.IsConvex`) equals its Fenchel biconjugate `f**`. -/
theorem biconjugate_eq_of_isConvex_of_lowerSemicontinuous
    (f : E → WithTopBot 𝕜) (hf_convex : f.IsConvex 𝕜) (hf_closed : LowerSemicontinuous f) :
    f⋆⋆ = f := by
  simpa [lowerSemicontinuousHull_eq_self hf_closed] using
    (hf_convex.biconjugate_eq_lowerSemicontinuousHull : f⋆⋆ = cl(f))

/-- Theorem 12.1 in the source-facing affine-minorant form: a closed convex function on a
finite-dimensional scalar-field space with a continuous linear self-pairing is the pointwise
supremum of its affine minorants once affine functionals are represented through the pairing. -/
theorem eq_iSup_affineMinorant_of_isConvex_of_lowerSemicontinuous
    [IsStrictOrderedRing 𝕜] [HasPairingSwap E E 𝕜]
    (f : E → WithTopBot 𝕜) (hf_convex : f.IsConvex 𝕜) (hf_closed : LowerSemicontinuous f)
    (h_affine : AffineMinorant.IsPairingSubConstRepresentable f)
    (x : E) :
    f x = ⨆ h : AffineMinorant f, h.toWithBotTop x := by
  exact eq_iSup_affineMinorant_of_eq_biconjugate f
    (biconjugate_eq_of_isConvex_of_lowerSemicontinuous
      f hf_convex hf_closed)
    x h_affine

end

/-! ### Corollary_12_1_2 (from Chap03) -/
noncomputable section

universe u v

open scoped Rockafellar

section

variable {𝕜 : Type*} {X : Type u} {Y : Type v}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommGroup X] [Module 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing X Y 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 12.1.2 states that every proper convex function on `R^n` admits at
  least one affine function `x ↦ ⟪x, b⟫ₚ - β` lying pointwise below it.
- `core/canonical`: the owner abstractions already present upstream are `convexConjugate`,
  `Function.IsProper`, and the properness transfer theorem
  `Function.IsConvex.convexConjugate_isProper_iff`.
- `bridge/view`: the source coordinate form `⟪x, b⟫ₚ - β ≤ f x` is obtained from the canonical
  one-minorant constructor `pairingSubConstAffineMinorant`.

Domain-style sampling used here:
- `Function.IsProper` from `Definition_4_6`;
- `convexConjugate` and `Function.IsConvex.convexConjugate_isProper_iff` from `Theorem_12_2`;
- `pairingSubConstAffineMinorant` and `affineMinorant_le` from `Text_12_1_2`.

Primitive data vs derived API:
- primitive owner input: one dual-side properness witness
  `hf_conj_proper : (f⋆ : Y → WithBotTop 𝕜).IsProper`;
- owner-derived data: one dual point `y` where `f⋆ y` is finite;
- derived API here: the textbook affine lower bound `⟪x, y⟫ₚ - β ≤ f x`.

Layer target:
- the canonical owner theorem below is the primitive statement "proper conjugate gives an affine
  minorant", and it lives on the weaker module/pairing layer;
- the Rockafellar corollary is then a thin source-facing bridge from
  `f.IsConvex 𝕜 ∧ f.IsProper` using Theorem 12.2(3).

Codomain/scalar canonicalization note:
- this local closure uses the canonical codomain layer `WithBotTop 𝕜` directly, matching the
  upstream owners `pairingSubConstAffineMinorant` and
  `Function.IsConvex.convexConjugate_isProper_iff`;
- the finite dual value `f⋆ y` is lifted to a scalar `β : 𝕜` via the canonical
  `WithBotTop` finite-value lift, avoiding `EReal`-specific bridges.

Finite-dimensional / continuity irreducibility note:
- `FiniteDimensional 𝕜 X` and `HasContinuousPairing X Y 𝕜` are not needed for the primitive
  affine-minorant constructor theorem in this file;
- they are only needed in the source-facing bridge through
  `Function.IsConvex.convexConjugate_isProper_iff`, whose current upstream owner statement is at
  that ambient layer.
-/

-- Proof sketch: properness of `f⋆` gives `y` with finite value `f⋆ y`. Taking
-- the scalar lift `β` of `f⋆ y`, Text 12.1.2 yields the corresponding affine-map minorant.
/-- Canonical owner form for Corollary 12.1.2: if the conjugate `f⋆` is proper, then `f` admits
one pairing affine map `pairingSubConstAffineMap y β` below it. -/
theorem exists_pairingSubConstAffineMap_le_of_convexConjugate_isProper
    (f : X → WithBotTop 𝕜) (hf_conj_proper : (f⋆ : Y → WithBotTop 𝕜).IsProper) :
    ∃ y : Y, ∃ β : 𝕜, (pairingSubConstAffineMap y β).toWithBotTop ≤ f := by
  set g : Y → WithBotTop 𝕜 := (f⋆ : Y → WithBotTop 𝕜)
  have hg_proper : g.IsProper := by
    simpa [g] using hf_conj_proper
  obtain ⟨y, hy_dom⟩ := hg_proper.nonempty_dom
  have hy_top : g y < ⊤ := mem_effectiveDomain.mp hy_dom
  have hy_ne_top : g y ≠ ⊤ := ne_of_lt hy_top
  have hy_ne_bot : g y ≠ ⊥ := hg_proper.ne_bot y
  lift g y to 𝕜 using ⟨hy_ne_top, hy_ne_bot⟩ with β hβ
  have hy_le : g y ≤ (β : WithBotTop 𝕜) := by simp [hβ]
  refine ⟨y, β, ?_⟩
  exact
    (pairingSubConstAffineMap_le_iff_convexConjugate_le (f := f) y β).2
      (by simpa [g] using hy_le)

/-- Source-facing bridge: if the conjugate `f⋆` is proper, then `f` admits an affine lower bound
`x ↦ ⟪x, y⟫ₚ - β`. -/
theorem exists_pairing_sub_const_le_of_convexConjugate_isProper
    (f : X → WithBotTop 𝕜) (hf_conj_proper : (f⋆ : Y → WithBotTop 𝕜).IsProper) :
    ∃ y : Y, ∃ β : 𝕜, ∀ x : X, ((⟪x, y⟫ₚ - β : 𝕜) : WithBotTop 𝕜) ≤ f x := by
  obtain ⟨y, β, hminor⟩ :=
    exists_pairingSubConstAffineMap_le_of_convexConjugate_isProper (f := f) hf_conj_proper
  refine ⟨y, β, ?_⟩
  intro x
  simpa [pairingSubConstAffineMap_apply, coe_sub] using hminor x

end

section

variable {𝕜 : Type*} {E : Type u}
variable [ConditionallyCompleteLinearOrder 𝕜] [Field 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)]
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
variable [FiniteDimensional 𝕜 E] [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜]

-- Proof sketch: Theorem 12.2(3) turns `f.IsConvex 𝕜 ∧ f.IsProper` into properness of `f⋆`;
-- then apply the primitive owner theorem above.
namespace Function.IsConvex

/-- Corollary 12.1.2 (source-facing bridge): given a proper convex function `f` on a
finite-dimensional scalar space with a continuous linear self-pairing, there exist `b` and
`β` such that
`f x ≥ ⟪x, b⟫ₚ - β` for every `x`. -/
theorem exists_pairing_sub_const_le_of_isProper
    {f : E → WithBotTop 𝕜} (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper) :
    ∃ b : E, ∃ β : 𝕜, ∀ x : E, ((⟪x, b⟫ₚ - β : 𝕜) : WithBotTop 𝕜) ≤ f x := by
  have hf_conj_proper : (f⋆ : E → WithBotTop 𝕜).IsProper := by
    exact (hf_convex.convexConjugate_isProper_iff).2 hf_proper
  exact exists_pairing_sub_const_le_of_convexConjugate_isProper (f := f) hf_conj_proper

end Function.IsConvex

end

/-! ### Text_12_1_2 (from Chap03) -/
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

/-! ### Text_12_1_3 (from Chap03) -/
noncomputable section

universe u v w

section

open scoped Rockafellar

variable {X : Type u} {Y : Type v} {α : Type w}
variable [Add α] [Neg α] [ConditionallyCompleteLattice α]

section IntrinsicCodomainCore

variable [HasPairing X Y (WithBotTop α)]

-- Proof sketch: if for each `y` there is some `x` with finite pairing value, then that term in
-- the defining supremum is `⊤` because subtracting `⊥` gives `⊤`; hence the whole supremum is
-- `⊤`.
/-- Core codomain-level `⊥ ↦ ⊤` conjugacy identity: if each dual point `y` admits at least one
finite pairing value `⟪x, y⟫ₚ ≠ ⊥`, then the conjugate of the constant `-∞` function is the
constant `+∞` function. -/
theorem convexConjugate_bot_eq_top_of_exists_pairing_ne_bot
    (hfinite : ∀ y : Y, ∃ x : X, (⟪x, y⟫ₚ : WithBotTop α) ≠ ⊥) :
    ((⊥ : X → WithBotTop α)⋆) = (⊤ : Y → WithBotTop α) := by
  ext y
  rcases hfinite y with ⟨x0, hx0⟩
  change (⨆ x : X, ⟪x, y⟫ₚ - (⊥ : WithBotTop α)) = (⊤ : WithBotTop α)
  rw [eq_top_iff]
  refine le_iSup_of_le x0 ?_
  change (⊤ : WithBotTop α) ≤ (⟪x0, y⟫ₚ - (⊥ : WithBotTop α))
  simp [WithBotTop.sub_bot hx0]

-- Proof sketch: use `convexConjugate_eq_iSup_pairing_sub`; every summand is `⊥` because
-- subtracting `⊤` in `WithBotTop α` gives `⊥`, so the supremum is `⊥`.
/-- Core codomain-level `⊤ ↦ ⊥` conjugacy identity for any pairing into `WithBotTop α`. -/
theorem convexConjugate_top_eq_bot_core :
    ((⊤ : X → WithBotTop α)⋆) = (⊥ : Y → WithBotTop α) := by
  ext y
  simp [convexConjugate_eq_iSup_pairing_sub]

end IntrinsicCodomainCore

section FinitePairingLift

variable [HasPairing X Y α]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 12.1.3 states that the constant functions with values `-∞` and `+∞` are
  Fenchel conjugates of one another.
- `core/canonical`: the owner abstraction is the chapter Fenchel conjugate `convexConjugate`.
- `bridge/view`: the scoped postfix notation `f⋆` from `Defn_12_2` is the canonical theorem
  surface for that owner, while the complete-lattice constants `⊥` and `⊤` on
  `X → WithBotTop α` and `Y → WithBotTop α` are the canonical Lean owners for the constant `-∞`
  and `+∞` functions.

Domain-style sampling used here:
- `convexConjugate`;
- `convexConjugate_eq_iSup_pairing_sub`;
- the complete-lattice constants `⊥` and `⊤` on `X → WithBotTop α` and `Y → WithBotTop α`;
- the `WithBotTop` arithmetic simplifications `sub_bot` and `sub_top`.

Primitive data vs derived API:
- primitive codomain-level core for `⊥ ↦ ⊤`: pairing in `WithBotTop α` plus the finite-value
  witness `∀ y, ∃ x, ⟪x, y⟫ₚ ≠ ⊥`;
- source-facing finite-lift bridge for `⊥ ↦ ⊤`: `HasPairing X Y α` gives canonical finite pairing
  values in `WithBotTop α`;
- primitive codomain-level core for `⊤ ↦ ⊥`: `HasPairing X Y (WithBotTop α)`.
- primitive codomain layer: `WithBotTop α`;
- derived API: the two atomic conjugacy identities for the canonical owner
  `convexConjugate`.

Layer target: `source-facing`; the source writes this on `R^n` with `EReal`, while the canonical
owner statement only needs the intrinsic pairing layer together with an extended ordered codomain.
-/

/-- Text 12.1.3 (1): for any nonempty primal pairing domain and any chapter extended codomain
`WithBotTop α`, the Fenchel conjugate of the constant `-∞` function is the constant `+∞`
function, written on the canonical function-lattice surface as
`((⊥ : X → WithBotTop α))⋆ = (⊤ : Y → WithBotTop α)`. -/
@[simp] theorem convexConjugate_bot_eq_top [Nonempty X] :
    ((⊥ : X → WithBotTop α)⋆) = (⊤ : Y → WithBotTop α) := by
  refine convexConjugate_bot_eq_top_of_exists_pairing_ne_bot (X := X) (Y := Y) (α := α) ?_
  intro y
  rcases (inferInstance : Nonempty X) with ⟨x0⟩
  refine ⟨x0, ?_⟩
  exact WithBotTop.coe_ne_bot (⟪x0, y⟫ₚ : α)

end FinitePairingLift

section IntrinsicCodomainPairing

variable [HasPairing X Y (WithBotTop α)]

/-- Text 12.1.3 (2): for any pairing and any chapter extended codomain `WithBotTop α`, the
Fenchel conjugate of the constant `+∞` function is the constant `-∞` function, written on the
canonical function-lattice surface as `((⊤ : X → WithBotTop α))⋆ = (⊥ : Y → WithBotTop α)`. -/
@[simp] theorem convexConjugate_top_eq_bot :
    ((⊤ : X → WithBotTop α)⋆) = (⊥ : Y → WithBotTop α) := by
  exact convexConjugate_top_eq_bot_core (X := X) (Y := Y) (α := α)

end IntrinsicCodomainPairing

end
