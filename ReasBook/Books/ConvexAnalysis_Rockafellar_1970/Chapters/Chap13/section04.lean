import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_13_4_1 (from Chap03) -/
noncomputable section

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

open ConvexERealFunction
open scoped Rockafellar

local notation "IsClosedProperConvex[ℝ]" => Function.IsClosedProperConvex (𝕜 := ℝ)

local instance : HasPairing E E ℝ := instHasPairingOfHasLinearPairing
local instance : HasPairing E E (WithTopBot ℝ) := instHasPairingWithBotTop

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 13.4.1 says that closed proper convex functions related by Fenchel
  conjugation have the same rank.
- `core/canonical`: the owner abstractions already present in the project are
  `Function.rank`, `convexConjugate`, and the Chapter 3 owner predicate
  `Function.IsClosedProperConvex`.
- `bridge/view`: the textbook phrase "conjugate to each other" is rendered canonically by the
  direct comparison between `f` and its Fenchel conjugate `convexConjugate f`.

Domain-style sampling used here:
- `Function.rank` and `Function.rank_eq` from `Definition_8_9_2`;
- `Function.IsClosedProperConvex` from `Text_12_3_6`;
- `lineality_convexConjugate_eq_ambientDim_sub_effectiveDomain_affineDim` from `Theorem_13_4`;
- `effectiveDomain_convexConjugate_affineDim_eq_ambientDim_sub_lineality` from `Theorem_13_4`.

Layer target: `source-facing`, stated directly in the canonical conjugation and rank API without
introducing an auxiliary wrapper for conjugate pairs or a parallel closed/proper/convex hypothesis
bundle.
-/

-- Proof sketch: rewrite both sides using `Function.rank_eq`, then apply the two
-- dimension formulas already exposed by Theorem 13.4 for `dom f⋆` and
-- `lineality[ℝ](f⋆)`. The
-- resulting arithmetic identity is exactly `rank[ℝ](f)`.
/-- Corollary 13.4.1: a closed proper convex function and its Fenchel conjugate have the same
rank. -/
theorem rank_convexConjugate_eq_rank (f : E → WithTopBot ℝ) (hf : IsClosedProperConvex[ℝ] f) :
    rank[ℝ]((f⋆ : E → WithTopBot ℝ)) = rank[ℝ](f) := by
  rw [Function.rank_eq (𝕜 := ℝ) (f := (f⋆ : E → WithTopBot ℝ)),
    Function.rank_eq (𝕜 := ℝ) (f := f)]
  rw [effectiveDomain_convexConjugate_affineDim_eq_ambientDim_sub_lineality f hf]
  rw [lineality_convexConjugate_eq_ambientDim_sub_effectiveDomain_affineDim f hf.convex hf.proper]
  omega

end

/-! ### Corollary_13_4_2 (from Chap03) -/
noncomputable section

section

variable {E : Type*}
variable [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
variable [FiniteDimensional ℝ E]
variable [HasLinearPairing E E ℝ] [HasContinuousPairing E E ℝ]

open ConvexERealFunction
open scoped Rockafellar

local notation "IsClosedProperConvex[ℝ]" => Function.IsClosedProperConvex (𝕜 := ℝ)

/-
Source/core/bridge triage:
- `source-facing`: Corollary 13.4.2 characterizes when the effective domain of the Fenchel
  conjugate `f*` has nonempty interior by excluding affine lines on which `f` stays finite and
  affine.
- `core/canonical`: the owner abstractions are `convexConjugate`, `Function.rank`, the
  function-dimension owner `dim(·)` applied to `f⋆`, the dimension formula for `dom f*`,
  `Function.lineality`, and mathlib's convex-set
  interior criterion
  `Convex.interior_nonempty_iff_affineSpan_eq_top`.
- `bridge/view`: the textbook phrase `dom f*` is rendered directly by the chapter effective-domain
  owner `dom(f⋆)`, so no new local set-builder wrapper is introduced.
- Domain-style sampling used here:
  `Function.lineality_eq_zero_iff_not_exists_affineLine`,
  `effectiveDomain_convexConjugate_affineDim_eq_ambientDim_sub_lineality`, and
  `Convex.interior_nonempty_iff_affineSpan_eq_top`, together with
  `Function.isConvex_convexConjugate`.
- Primitive data vs derived API:
  the primitive input is the function `f : E → WithTopBot ℝ`; the standing closed-proper-convex
  assumptions are bundled by the Chapter 3 owner predicate `IsClosedProperConvex[ℝ]`, while
  the interior-of-`dom f*` condition, its lineality-zero criterion, and the affine-line exclusion
  are all derived theorem-level views.
- Layer target: owner-first plus source-facing bridge. The primary theorem in this file is
  stated directly at the canonical owner level
  `(interior dom(f⋆)).Nonempty ↔ lineality[ℝ](f) = 0`, and the textbook affine-line wording is
  kept as a thin corollary via
  `Function.lineality_eq_zero_iff_not_exists_affineLine`.
- Scalar/codomain/topology checks for this item:
  - codomain: this theorem is stated directly on `WithTopBot ℝ`, matching the Chapter 2
    quantified affine-line exclusion bridge and the Chapter 3 affine-dimension bridge API without
    alias-level coercion noise;
  - scalar: the result remains genuinely `ℝ`-scalar because the reused Chapter 8/13 lineality and
    affine-dimension bridge API is currently real-parameterized;
  - topology: ambient `interior` (not `intrinsicInterior`) is primary here, since the theorem
    characterizes full-dimensionality of `dom(f⋆)` in the ambient space.
-/

-- Proof sketch (owner form): the finite domain of `convexConjugate f` is convex, so
-- `Convex.interior_nonempty_iff_affineSpan_eq_top` identifies nonempty interior with full affine
-- dimension `Module.finrank ℝ E`. The Chapter 3 formula
-- `effectiveDomain_convexConjugate_affineDim_eq_ambientDim_sub_lineality` rewrites that as
-- `lineality[ℝ](f) = 0`.
-- In the backward interior→dimension step, nonemptiness of `affineSpan ℝ (dom f⋆)` is
-- obtained
-- directly from the affine-dimension hypothesis (excluding the `⊥` case), so no extra properness
-- bridge for `f⋆` is needed.
namespace Function.IsClosedProperConvex

/-- Owner form of Corollary 13.4.2: a closed proper convex function has conjugate with finite
domain of nonempty interior exactly when the primal lineality vanishes. -/
theorem interior_dom_convexConjugate_nonempty_iff_lineality_eq_zero
    {f : E → WithTopBot ℝ} (hf : IsClosedProperConvex[ℝ] f) :
    (interior dom(f⋆)).Nonempty ↔
      lineality[ℝ](f) = 0 := by
  have hconv_conjugate : (f⋆).IsConvex ℝ := Function.isConvex_convexConjugate f
  have hconv : Convex ℝ dom(f⋆) := hconv_conjugate.convex_dom
  have hinterior_iff_dim :
      (interior dom(f⋆)).Nonempty ↔
        dim((f⋆ : E → WithTopBot ℝ)) = (Module.finrank ℝ E : ℤ) := by
    rw [hconv.interior_nonempty_iff_affineSpan_eq_top]
    constructor
    · intro htop
      have htop_ne_bot : (⊤ : AffineSubspace ℝ E) ≠ ⊥ :=
        (AffineSubspace.bot_ne_top ℝ E E).symm
      rw [Set.affineDim, htop, AffineSubspace.affineDim, if_neg htop_ne_bot,
        AffineSubspace.direction_top]
      exact_mod_cast (finrank_top ℝ E)
    · intro hdim
      let s : AffineSubspace ℝ E := affineSpan ℝ dom(f⋆)
      have hs_ne_bot : s ≠ ⊥ := by
        intro hs_bot
        have hdim_bot : dim((f⋆ : E → WithTopBot ℝ)) = -1 := by
          simp [Function.dim, s, Set.affineDim, AffineSubspace.affineDim, hs_bot]
        have hfinrank_nonneg : (0 : ℤ) ≤ (Module.finrank ℝ E : ℤ) := by
          exact_mod_cast (Nat.zero_le (Module.finrank ℝ E))
        omega
      have hs_nonempty : (s : Set E).Nonempty :=
        (AffineSubspace.nonempty_iff_ne_bot s).2 hs_ne_bot
      have hs_finrank : Module.finrank ℝ s.direction = Module.finrank ℝ E := by
        have hdim' : (Module.finrank ℝ s.direction : ℤ) = (Module.finrank ℝ E : ℤ) := by
          simpa [Function.dim, s, Set.affineDim, AffineSubspace.affineDim, hs_ne_bot] using hdim
        exact_mod_cast hdim'
      have hs_direction_top : s.direction = ⊤ := Submodule.eq_top_of_finrank_eq hs_finrank
      exact (AffineSubspace.direction_eq_top_iff_of_nonempty hs_nonempty).1 hs_direction_top
  have hdim_formula :
      dim((f⋆ : E → WithTopBot ℝ)) = (Module.finrank ℝ E : ℤ) - lineality[ℝ](f) := by
    simpa using effectiveDomain_convexConjugate_affineDim_eq_ambientDim_sub_lineality f hf
  rw [hinterior_iff_dim, hdim_formula]
  omega

-- Proof sketch (source-facing bridge): rewrite the owner theorem above by the bundled Chapter 2
-- bridge `Function.IsClosedProperConvex.lineality_eq_zero_iff_not_exists_affineLine`.
/-- Corollary 13.4.2: a closed proper convex function has conjugate with finite domain of nonempty
interior if and only if there is no nontrivial affine line on which the function is finite and
affine. -/
theorem interior_dom_convexConjugate_nonempty_iff_not_exists_affineLine
    {f : E → WithTopBot ℝ} (hf : IsClosedProperConvex[ℝ] f) :
    (interior dom(f⋆)).Nonempty ↔
      ¬ ∃ y : E, y ≠ 0 ∧ ∃ x : E, x ∈ dom(f) ∧ ∀ t : ℝ, f (x + t • y) = f x := by
  rw [hf.interior_dom_convexConjugate_nonempty_iff_lineality_eq_zero]
  exact hf.lineality_eq_zero_iff_not_exists_affineLine

end Function.IsClosedProperConvex

end

/-! ### Text_13_4_3 (from Chap03) -/
noncomputable section

universe u v w

section

open scoped Rockafellar

variable {α : Type v} [AddCommGroup α]
variable {X : Type u} {Y : Type w} [HasPairing X Y α]

/-!
Source/core/bridge triage for this item.

- `source-facing`: the item rewrites the support half-space level set
  `{x | h x ≤ β + ⟪x, b⋆⟫ₚ}` as a nonpositive sublevel set and computes the conjugate of the
  corresponding affine perturbation of `h`.
- `core/canonical`: the owner abstractions are the project declaration `convexConjugate` for
  Fenchel conjugation and the chapter affine-change theorem
  `convexConjugate_affineChange`.
- `bridge/view`: the textbook function `x ↦ h x - ⟪x, b⋆⟫ₚ - β` is kept as a direct source-facing
  affine perturbation of `h`. Its conjugate formula is proved directly on the pairing layer,
  while the chapter affine-change theorem remains the stronger linear-equiv companion.

Domain-style sampling used here:
- `convexConjugate` and the chapter notation `f⋆` from `Defn_12_2`;
- `convexConjugate_eq_iSup_pairing_sub` from `Defn_12_2`;
- `convexConjugate_affineChange` from `Theorem_12_3`, as the linear-equivalence affine-change
  companion.

Primitive data vs derived API:
- primitive data: the function `h : X → WithBotTop α`, the dual vector `bStar : Y`, and the scalar
  `β : α`;
- derived API: the level-set equality and the conjugate translation formula.

Layer target: `source-facing`; the item is formalized directly as the displayed set identity and
conjugate formula, without introducing a parallel local wrapper.

Redundant-source-assumption elimination: although the textbook states the result for proper convex
`h`, both displayed formulas are purely algebraic consequences of the Fenchel definition, so the
Lean statements below do not keep those redundant hypotheses.
-/

-- Proof sketch: membership in the left-hand set is exactly the
-- inequality `h x - ⟪x, b⋆⟫ₚ - β ≤ 0` after moving the finite affine term to the left.
/-- Text 13.4.3 (1): the set `{x | h x ≤ β + ⟪x, b⋆⟫ₚ}` is the nonpositive sublevel set of
`x ↦ h x - ⟪x, b⋆⟫ₚ - β`. -/
theorem levelSet_pairing_le_eq_preimage_sub_nonpos
    [LinearOrder α] [IsOrderedAddMonoid α]
    (h : X → WithBotTop α) (bStar : Y) (β : α) :
    {x : X | h x ≤ β + ⟪x, bStar⟫ₚ} =
      (fun x ↦ h x - ⟪x, bStar⟫ₚ - β) ⁻¹' Set.Iic (0 : WithBotTop α) := by
  ext x
  change h x ≤ β + ⟪x, bStar⟫ₚ ↔ h x - ⟪x, bStar⟫ₚ - β ≤ 0
  constructor
  · intro hx
    let pairx : WithBotTop α := ⟪x, bStar⟫ₚ
    have hx_pair : h x ≤ (β : WithBotTop α) + pairx := by
      simpa [pairx] using hx
    have hx' : h x - pairx ≤ β := by
      exact (WithBotTop.sub_le_iff_le_add
        (a := h x) (b := pairx) (c := (β : WithBotTop α))
        (.inr (WithBotTop.coe_ne_top β)) (.inr (WithBotTop.coe_ne_bot β))).2 hx_pair
    exact WithBotTop.sub_nonpos.mpr hx'
  · intro hx
    let pairx : WithBotTop α := ⟪x, bStar⟫ₚ
    have hx' : h x - pairx ≤ β := by
      simpa [pairx] using (WithBotTop.sub_nonpos.mp hx)
    have hx_pair : h x ≤ (β : WithBotTop α) + pairx := by
      exact (WithBotTop.sub_le_iff_le_add
        (a := h x) (b := pairx) (c := (β : WithBotTop α))
        (.inr (WithBotTop.coe_ne_top β)) (.inr (WithBotTop.coe_ne_bot β))).1 hx'
    simpa [pairx] using hx_pair

-- Proof sketch: unfold both conjugates by `convexConjugate_eq_iSup_pairing_sub`, move the finite
-- scalar `β` outside the supremum through the order isomorphism `t ↦ t + β`, and simplify the
-- pointwise affine term using `⟪x, x⋆ + b⋆⟫ₚ = ⟪x, x⋆⟫ₚ + ⟪x, b⋆⟫ₚ`.
/-- Text 13.4.3 (2): the conjugate of `x ↦ h x - ⟪x, b⋆⟫ₚ - β` is
`x⋆ ↦ h*(x⋆ + b⋆) + β`. -/
theorem convexConjugate_sub_pairing_const
    [ConditionallyCompleteLinearOrder α] [IsOrderedAddMonoid α]
    [Add Y]
    [HasPairingAddRight X Y α]
    (h : X → WithBotTop α) (bStar : Y) (β : α) :
    (fun x ↦ h x - ⟪x, bStar⟫ₚ - β)⋆ =
      fun xStar ↦ h⋆ (xStar + bStar) + β := by
  let addRightβ : WithBotTop α ≃o WithBotTop α :=
    { toFun := fun t ↦ t + β
      invFun := fun t ↦ t - β
      left_inv := fun _ ↦ WithBotTop.add_sub_cancel_right
      right_inv := fun _ ↦ WithBotTop.sub_add_cancel
      map_rel_iff' := fun {a b} ↦ (WithBotTop.addLECancellable_coe β).add_le_add_iff_right }
  funext xStar
  calc
    (fun x ↦ h x - ⟪x, bStar⟫ₚ - β)⋆ xStar
      = ⨆ x : X, (⟪x, xStar⟫ₚ - (h x - ⟪x, bStar⟫ₚ - β)) := by
          rw [convexConjugate_eq_iSup_pairing_sub]
    _ = ⨆ x : X, ((⟪x, xStar + bStar⟫ₚ - h x) + β) := by
          apply iSup_congr
          intro x
          have hpair_ne_bot : (⟪x, bStar⟫ₚ : WithBotTop α) ≠ ⊥ := by
            change (((⟪x, bStar⟫ₚ : α) : WithBotTop α) ≠ ⊥)
            exact WithBotTop.coe_ne_bot _
          have hpair_ne_top : (⟪x, bStar⟫ₚ : WithBotTop α) ≠ ⊤ := by
            change (((⟪x, bStar⟫ₚ : α) : WithBotTop α) ≠ ⊤)
            exact WithBotTop.coe_ne_top _
          have hneg_pair :
              -(h x - (⟪x, bStar⟫ₚ : WithBotTop α)) = -h x + ⟪x, bStar⟫ₚ := by
            exact
              (WithBotTop.neg_sub
                (x := h x) (y := (⟪x, bStar⟫ₚ : WithBotTop α))
                (.inr hpair_ne_bot) (.inr hpair_ne_top))
          have hneg_pair' :
              -(h x + -⟪x, bStar⟫ₚ) = -h x + ⟪x, bStar⟫ₚ := by
            simpa [WithBotTop.sub_eq_add_neg] using hneg_pair
          have hpair :
              (⟪x, xStar + bStar⟫ₚ : WithBotTop α) =
                (⟪x, xStar⟫ₚ : WithBotTop α) + (⟪x, bStar⟫ₚ : WithBotTop α) := by
            exact congrArg (fun t : α ↦ (t : WithBotTop α))
              (HasPairingAddRight.pairing_add_right (X := X) (Y := Y) (𝕜 := α) x xStar bStar)
          calc
            ⟪x, xStar⟫ₚ - (h x - ⟪x, bStar⟫ₚ - β)
                = ⟪x, xStar⟫ₚ + (-(h x - ⟪x, bStar⟫ₚ) + β) := by
                    rw [WithBotTop.sub_eq_add_neg]
                    rw [WithBotTop.neg_sub (.inr (WithBotTop.coe_ne_bot β))
                      (.inr (WithBotTop.coe_ne_top β))]
            _ = ⟪x, xStar⟫ₚ + (-h x + ⟪x, bStar⟫ₚ) + β := by
                    rw [show (-(h x - ⟪x, bStar⟫ₚ) : WithBotTop α) = -(h x + -⟪x, bStar⟫ₚ) by
                      simp [WithBotTop.sub_eq_add_neg]]
                    rw [hneg_pair']
                    simp [add_assoc, add_left_comm, add_comm]
            _ = ⟪x, xStar + bStar⟫ₚ + (-h x) + β := by
                    rw [hpair]
                    simp [add_assoc, add_left_comm, add_comm]
            _ = (⟪x, xStar + bStar⟫ₚ - h x) + β := by
                    rfl
    _ = addRightβ (⨆ x : X, (⟪x, xStar + bStar⟫ₚ - h x)) := by
          change (⨆ x : X, addRightβ (⟪x, xStar + bStar⟫ₚ - h x)) =
            addRightβ (⨆ x : X, (⟪x, xStar + bStar⟫ₚ - h x))
          symm
          exact addRightβ.map_iSup _
    _ = addRightβ (h⋆ (xStar + bStar)) := by
          rw [convexConjugate_eq_iSup_pairing_sub]
    _ = h⋆ (xStar + bStar) + β := by
          rfl

end

/-! ### Theorem_13_4 (from Chap03) -/
noncomputable section

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open ConvexERealFunction
open Submodule
open scoped RealInnerProductSpace Rockafellar

local notation "IsClosedProperConvex[ℝ]" => Function.IsClosedProperConvex (𝕜 := ℝ)

local instance : HasPairing E E ℝ := instHasPairingOfHasLinearPairing
local instance : HasPairing E E (WithTopBot ℝ) := instHasPairingWithBotTop

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 13.4 identifies the lineality space of the Fenchel conjugate `f*` with
  the orthogonal complement of the subspace parallel to `aff (dom f)`, gives the dual closed-case
  statement for `dom f*`, and records the corresponding dimension formulas.
- `core/canonical`: the owner abstractions already present in the project are `convexConjugate`,
  `recessionFunction`, `Function.constancySpace`, `Function.lineality`,
  `IsClosedProperConvex[ℝ]`, `AffineSubspace.direction`, `Submodule.orthogonal`, and
  the chapter function-dimension owner `dim(·)`.
- `bridge/view`: Rockafellar's `dom f` and `dom f*` are rendered canonically by the finite-value
  sets `dom(f)` and `dom(convexConjugate f)`.

Domain-style sampling used here:
- `supportFunction_effectiveDomain_eq_recessionFunction_convexConjugate` and
  `supportFunction_effectiveDomain_convexConjugate_eq_recessionFunction` from `Theorem_13_3`;
- `Function.constancySpace` from `Definiton_8_7_0`;
- `Function.lineality` from `Definition_8_9_2`;
- the canonical owner constructions `AffineSubspace.direction` and `Submodule.orthogonal`.

Primitive data vs derived API:
- primitive input: a function `f : E → WithTopBot ℝ`;
- owner hypotheses: `f.IsConvex` and `f.IsProper` for the first clause on the base inner-product
  layer, and `FiniteDimensional ℝ E` together with those hypotheses or `f.IsClosedProperConvex`
  for the later numerical and dual closed-case clauses;
- derived API: the orthogonal-complement identifications and the two numerical formulas expressed
  through `lineality` and `dim(·)`.

Layer target: this item stays `source-facing`, stated directly in the canonical conjugation,
lineality, affine-hull, and orthogonality language without introducing a surrogate wrapper.
-/

variable (f : E → WithTopBot ℝ)

-- Proof sketch: by Theorem 13.3, `recessionFunction (convexConjugate f)` is the support function
-- of `dom f`. A vector lies in `Function.constancySpace` of that support function exactly when the
-- corresponding linear functional is both bounded above and bounded below on `dom f`, equivalently
-- when it vanishes on the direction subspace of `affineSpan ℝ (dom f)`.
/-- Theorem 13.4: for a proper convex function `f` on a real inner-product space, the lineality
space of the Fenchel conjugate `f*` is the orthogonal complement of the subspace parallel to the
affine hull of its effective domain `dom f`. The canonical owner statement only uses the real
inner-product-space structure, so it is formulated at that level and specializes in particular to
`R^n`. -/
theorem constancySpace_convexConjugate_eq_orthogonal_effectiveDomain_direction
    (hf_convex : f.IsConvex ℝ)
    (hf_proper : f.IsProper) :
    Function.constancySpace (((f⋆ : E → WithTopBot ℝ))₀⁺) =
      ((affineSpan ℝ dom(f)).directionᗮ : Set E) := sorry

section

variable [FiniteDimensional ℝ E]

-- Proof sketch: apply the first orthogonal-complement clause to `convexConjugate f`, then use the
-- closed proper convex biconjugacy input to identify `convexConjugate (convexConjugate f)` with
-- `f`. The orthogonal complement of the lineality space is rendered canonically as the
-- orthogonal complement of the direction subspace of its affine hull.
/-- For a closed proper convex function, the subspace parallel to the affine hull of `dom f*`
coincides with the orthogonal complement of the lineality space of `f`. -/
theorem effectiveDomain_convexConjugate_direction_eq_orthogonal_constancySpace_direction
    (hf : IsClosedProperConvex[ℝ] f) :
    (affineSpan ℝ dom((f⋆ : E → WithTopBot ℝ))).direction =
      (((affineSpan ℝ (Function.constancySpace (f0⁺))).direction)ᗮ : Submodule ℝ E) := sorry

-- Proof sketch: combine the first orthogonal-complement identification with the definition of
-- `Function.lineality` as the affine dimension of the lineality space, then use the
-- finite-dimensional identity for the orthogonal complement of a direction subspace.
/-- The lineality of the Fenchel conjugate equals the ambient dimension minus the affine dimension
of the effective domain of the original function, written canonically as `dim(f)`. -/
theorem lineality_convexConjugate_eq_ambientDim_sub_effectiveDomain_affineDim
    (hf_convex : f.IsConvex ℝ)
    (hf_proper : f.IsProper) :
    lineality[ℝ]((f⋆ : E → WithTopBot ℝ)) = (Module.finrank ℝ E : ℤ) - dim(f) := sorry

end

end

section

variable {E : Type*}
variable [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
variable [FiniteDimensional ℝ E]
variable [HasLinearPairing E E ℝ] [HasContinuousPairing E E ℝ]

open ConvexERealFunction
open scoped Rockafellar

local notation "IsClosedProperConvex[ℝ]" => Function.IsClosedProperConvex (𝕜 := ℝ)

variable (f : E → WithTopBot ℝ)

-- Proof sketch: identify `dim(f⋆)` with ambient dimension minus the affine dimension loss coming
-- from lineality, using the Chapter 13.4 orthogonality/dimension bridge in pairing form.
/-- For a closed proper convex function on a finite-dimensional real topological vector space
equipped with a continuous linear self-pairing, the affine dimension of the effective domain of
`f*` equals the ambient dimension minus the lineality of `f`, written canonically as `dim(f⋆)`. -/
theorem effectiveDomain_convexConjugate_affineDim_eq_ambientDim_sub_lineality
    (hf : IsClosedProperConvex[ℝ] f) :
    dim((f⋆ : E → WithTopBot ℝ)) = (Module.finrank ℝ E : ℤ) - lineality[ℝ](f) := sorry

end
