import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_23_6_1 (from Chap05) -/
noncomputable section

open scoped Rockafellar

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Proposition 23.6.1 translates the `ε`-subdifferential at a finite base point
  `x` into a Fenchel-conjugate sublevel condition for the translated defect function
  `h(y) = f (x + y) - f x`, and then reads off the closedness, convexity, monotonicity, and
  zero-tolerance intersection properties of `∂_ε f(x)`.
- `core/canonical`: the owner declarations already present in the project are
  `_root_.subdifferentialAt` and Fenchel conjugation `f⋆`; the approximate subdifferential of
  Definition 23.6 is kept here directly through its canonical supporting-affine inequality.
- `bridge/view`: there is no extra Euclidean bridge here; the source's `x*` naturally belongs to
  the canonical dual `StrongDual ℝ E`.

Domain-style sampling used here:
- `convexConjugate` / `f⋆` from `Chap03/Defn_12_2`;
- `_root_.subdifferentialAt` from `Chap05/Definition_23_0_6`;
- the supporting-affine inequality surface introduced by Definition 23.6;
- the set-theoretic intersection surface `⋂ (ε : ℝ) (_ : 0 < ε), ...`, already used elsewhere in
  the project for exact positive-radius limit statements.

Primitive data vs derived API:
- primitive source data: the base point `x`, the function `f`, and the translated defect
  function `h(y) = f (x + y) - f x`;
- derived API: the conjugate formula for `h⋆`, the `ε`-subdifferential membership criterion, and
  the closed/convex/monotone/intersection properties of the approximate-support set from
  Definition 23.6.

Layer target: `source-facing`, but stated directly on the canonical project owners
`_root_.subdifferentialAt` and `convexConjugate`, with the approximate-subdifferential side kept
in its direct source-facing set form.
-/

/-- The translated defect function at `x` is `y ↦ f (x + y) - f x`. -/
def translatedDefectFunction (f : E → EReal) (x : E) : E → EReal :=
  fun y ↦ f (x + y) - f x

/-- Evaluating the translated defect function at `y` subtracts the base value `f x` from the
translated value `f (x + y)`. -/
-- Proof sketch: unfold `translatedDefectFunction`; the statement is the defining formula.
@[simp] theorem translatedDefectFunction_apply (f : E → EReal) (x y : E) :
    translatedDefectFunction f x y = f (x + y) - f x := sorry

/-- The Fenchel conjugate of the translated defect function is obtained from `f⋆` by adding the
base value `f x` and subtracting the pairing with `x`. -/
-- Proof sketch: unfold `translatedDefectFunction` and `convexConjugate`; change variables
-- `z = x + y` in the defining supremum and pull the constant term `f x - ⟪x, xStar⟫ₚ` outside
-- the supremum. The finiteness hypotheses on `f x` ensure the translation defect is the intended
-- real-valued affine shift rather than a degenerate `⊥`/`⊤` arithmetic branch.
theorem convexConjugate_translatedDefectFunction_eq
    (f : E → EReal) (x : E) (hx : x ∈ dom(f)) (hx_bot : f x ≠ ⊥)
    (xStar : StrongDual ℝ E) :
    (translatedDefectFunction f x)⋆ xStar = f⋆ xStar + f x - ⟪x, xStar⟫ₚ := sorry

/-- Proposition 23.6.1: for the translated defect function `h(y) = f (x + y) - f x` at a finite
base point `x`, a dual vector `xStar` belongs to the `ε`-subdifferential of `f` at `x` exactly
when the Fenchel conjugate `h⋆ xStar` is at most `ε`. -/
-- Proof sketch: rewrite membership in `epsSubdifferentialAt f x ε` by
-- `mem_epsSubdifferentialAt`, then compare the resulting family of affine upper bounds with the
-- supremum formula defining `(translatedDefectFunction f x)⋆ xStar`. This is exactly the same
-- supremum/inequality conversion as Fenchel-Young, specialized to the translated defect function.
theorem mem_epsSubdifferentialAt_iff_convexConjugate_translatedDefectFunction_le
    (f : E → EReal) (x : E) (hx : x ∈ dom(f)) (hx_bot : f x ≠ ⊥)
    (ε : ℝ) (xStar : StrongDual ℝ E) :
    xStar ∈ {yStar : StrongDual ℝ E |
      ∀ z, f z ≥ f x + (((yStar (z - x) - ε : ℝ) : EReal))} ↔
      (translatedDefectFunction f x)⋆ xStar ≤ ε := sorry

/-- Under the finite-base hypotheses of Proposition 23.6.1, each `ε`-subdifferential is closed in
the strong dual. -/
-- Proof sketch: by Proposition 23.6.1, `epsSubdifferentialAt f x ε` is the sublevel set
-- `{xStar | (translatedDefectFunction f x)⋆ xStar ≤ ε}`. Theorem 12.2 gives lower semicontinuity
-- of Fenchel conjugates, and closed sublevel sets of lower-semicontinuous functions are closed.
theorem isClosed_epsSubdifferentialAt
    (f : E → EReal) (x : E) (hx : x ∈ dom(f)) (hx_bot : f x ≠ ⊥) (ε : ℝ) :
    IsClosed {xStar : StrongDual ℝ E |
      ∀ z, f z ≥ f x + (((xStar (z - x) - ε : ℝ) : EReal))} := sorry

/-- Under the finite-base hypotheses of Proposition 23.6.1, each `ε`-subdifferential is convex in
the strong dual. -/
-- Proof sketch: rewrite `epsSubdifferentialAt f x ε` as the same conjugate sublevel set from
-- Proposition 23.6.1. Fenchel conjugates are convex by Theorem 12.2, and sublevel sets of convex
-- functions are convex.
theorem convex_epsSubdifferentialAt
    (f : E → EReal) (x : E) (hx : x ∈ dom(f)) (hx_bot : f x ≠ ⊥) (ε : ℝ) :
    Convex ℝ {xStar : StrongDual ℝ E |
      ∀ z, f z ≥ f x + (((xStar (z - x) - ε : ℝ) : EReal))} := sorry

/-- The `ε`-subdifferential grows with the tolerance parameter: smaller tolerances give smaller
sets. -/
-- Proof sketch: compare the defining inequalities
-- `f z ≥ f x + (xStar (z - x) - εᵢ)` for `ε₁ ≤ ε₂`; any witness for the smaller tolerance is
-- automatically a witness for the larger one.
theorem epsSubdifferentialAt_mono
    (f : E → EReal) (x : E) {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) :
    {xStar : StrongDual ℝ E |
        ∀ z, f z ≥ f x + (((xStar (z - x) - ε₁ : ℝ) : EReal))} ⊆
      {xStar : StrongDual ℝ E |
        ∀ z, f z ≥ f x + (((xStar (z - x) - ε₂ : ℝ) : EReal))} := sorry

/-- Under the finite-base hypotheses of Proposition 23.6.1, intersecting all positive-tolerance
`ε`-subdifferentials recovers the exact subdifferential. -/
-- Proof sketch: by Proposition 23.6.1, the positive-tolerance sets are the positive sublevel sets
-- of `(translatedDefectFunction f x)⋆`. Intersecting over all `ε > 0` therefore gives the zero
-- sublevel set, which is exactly the exact subdifferential at `x`.
theorem iInter_pos_epsSubdifferentialAt_eq_subdifferentialAt
    (f : E → EReal) (x : E) (hx : x ∈ dom(f)) (hx_bot : f x ≠ ⊥) :
    (⋂ (ε : ℝ) (_ : 0 < ε), {xStar : StrongDual ℝ E |
      ∀ z, f z ≥ f x + (((xStar (z - x) - ε : ℝ) : EReal))}) = subdifferentialAt f x := sorry

end

/-! ### Definition_23_6 (from Chap05) -/
noncomputable section

open scoped Rockafellar

universe u v

section

variable {𝕜 : Type v} [NormedField 𝕜] [LinearOrder 𝕜]
variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Definition 23.6 introduces the approximate subdifferential `∂_ε f(x)`,
  namely the set of affine supports allowed an error tolerance `ε` at the base point `x`.
- `core/canonical`: the owner is pairing-intrinsic, with `StrongDual 𝕜 E` only the default
  codomain inherited from `subdifferentialAt`.
- `bridge/view`: in ordered inner-product spaces, the source's vector-valued surface is the
  pullback along `InnerProductSpace.toDualMap 𝕜 E`.

Domain-style sampling used here:
- the exact Chapter 23 owner shape from `Items/Chap05/Definition_23_0_6.lean`;
- `_root_.subdifferentialWithinAt` from `Items/Chap05/Definition_25_1.lean`, which shows the
  chapter pattern of building a new owner in the same dual-valued family and keeping Euclidean
  terms as a thin bridge;
- mathlib's `StrongDual 𝕜 E` and `InnerProductSpace.toDualMap`.

Primitive data vs derived API:
- primitive owner: the set of dual-side elements satisfying the approximate supporting-affine
  inequality on `WithBotTop 𝕜`;
- derived API: the pointwise membership lemma, the zero-tolerance reduction to `∂[Y]f(x)`, and
  the vector-valued inner-product bridge.

Layer target:
- the main labeled entry is `source-facing`, but stated on the pairing-based canonical dual rather
  than on a coordinate model;
- the `Function`-namespace specialization below is `bridge/view`.

Notation evaluation:
- the textbook notation is exposed as `∂[ε]f(x)` for the default dual side and `∂[Y; ε]f(x)` when
  the dual codomain must be explicit, matching the exact notation `∂[Y]f(x)`.
-/

/-- Definition 23.6: the `ε`-subdifferential at `x` is the set of continuous linear functionals
that support `f` at `x` up to the error tolerance `ε`. -/
def epsSubdifferentialAt (f : E → WithBotTop 𝕜) (x : E) (ε : 𝕜)
    (Y := StrongDual 𝕜 E) [HasPairing E Y 𝕜] : Set Y :=
  {xStar | ∀ z, f z ≥ f x + (((⟪z - x, xStar⟫ₚ : 𝕜) - ε : 𝕜) : WithBotTop 𝕜)}

scoped[Rockafellar] notation "∂[" ε "]" f "(" x ")" => epsSubdifferentialAt f x ε
scoped[Rockafellar] notation "∂[" Y "; " ε "]" f "(" x ")" => epsSubdifferentialAt f x ε Y

/-- The `ε`-subdifferential is exactly the set of dual vectors satisfying the approximate
supporting-affine inequality. -/
-- Proof sketch: unfold `epsSubdifferentialAt`; this is the defining set expression.
theorem epsSubdifferentialAt_def (f : E → WithBotTop 𝕜) (x : E) (ε : 𝕜)
    (Y := StrongDual 𝕜 E) [HasPairing E Y 𝕜] :
    epsSubdifferentialAt f x ε Y =
      {xStar : Y |
        ∀ z, f z ≥ f x + (((⟪z - x, xStar⟫ₚ : 𝕜) - ε : 𝕜) : WithBotTop 𝕜)} :=
  rfl

/-- Membership in the approximate subdifferential is exactly the approximate
supporting-affine inequality. -/
-- Proof sketch: unfold `epsSubdifferentialAt`. Membership in the defining set is precisely the
-- displayed supporting-affine inequality, so this is definitional.
@[simp] theorem mem_epsSubdifferentialAt_pairing
    {f : E → WithBotTop 𝕜} {x : E} {ε : 𝕜} {Y} [HasPairing E Y 𝕜]
    {xStar : Y} :
    xStar ∈ (∂[Y; ε]f(x)) ↔
      ∀ z, f z ≥ f x + (((⟪z - x, xStar⟫ₚ : 𝕜) - ε : 𝕜) : WithBotTop 𝕜) :=
  Iff.rfl

/-- Membership in the default-dual approximate subdifferential is exactly the approximate
supporting-affine inequality. -/
@[simp] theorem mem_epsSubdifferentialAt
    {f : E → WithBotTop 𝕜} {x : E} {ε : 𝕜} {xStar : StrongDual 𝕜 E} :
    xStar ∈ (∂[ε]f(x)) ↔
      ∀ z, f z ≥ f x + (((xStar (z - x) : 𝕜) - ε : 𝕜) : WithBotTop 𝕜) :=
  Iff.rfl

/-- The approximate subdifferential at tolerance `0` is the exact supporting-affine
subdifferential set. -/
-- Proof sketch: ext on `xStar`, rewrite membership in `epsSubdifferentialAt f x 0` by the
-- defining characterization, rewrite membership in `∂[Y]f(x)`, and simplify the zero-tolerance
-- scalar term.
@[simp] theorem epsSubdifferentialAt_zero
    {f : E → WithBotTop 𝕜} {x : E} {Y} [HasPairing E Y 𝕜] :
    epsSubdifferentialAt f x 0 Y = ∂[Y]f(x) := by
  ext xStar
  rw [mem_epsSubdifferentialAt_pairing, mem_subdifferentialAt_pairing]
  simp

end

section

variable {𝕜 : Type v} [RCLike 𝕜] [LinearOrder 𝕜]
variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace Function

/-- In an ordered inner-product space, the vector-valued `ε`-subdifferential is the pullback of
`_root_.epsSubdifferentialAt` along `InnerProductSpace.toDualMap`. -/
abbrev epsSubdifferentialAt (f : E → WithBotTop 𝕜) (x : E) (ε : 𝕜) : Set E :=
  (InnerProductSpace.toDualMap 𝕜 E) ⁻¹' (_root_.epsSubdifferentialAt f x ε)

scoped[Rockafellar] notation "∂ᵥ[" ε "]" f "(" x ")" => Function.epsSubdifferentialAt f x ε

/-- Membership in the vector-valued `ε`-subdifferential is the approximate supporting-affine
inequality written with the inner-product pairing. -/
-- Proof sketch: unfold the preimage definition of `Function.epsSubdifferentialAt`, rewrite
-- membership in `_root_.epsSubdifferentialAt` by the dual-valued characterization above, and
-- simplify `InnerProductSpace.toDualMap` to the inner-product pairing.
@[simp] theorem mem_epsSubdifferentialAt {f : E → WithBotTop 𝕜} {x g : E} {ε : 𝕜} :
    g ∈ (∂ᵥ[ε]f(x)) ↔
      ∀ z, f z ≥ f x + (((inner 𝕜 g (z - x) : 𝕜) - ε : 𝕜) : WithBotTop 𝕜) := by
  change InnerProductSpace.toDualMap 𝕜 E g ∈ _root_.epsSubdifferentialAt f x ε ↔
      ∀ z, f z ≥ f x + (((inner 𝕜 g (z - x) : 𝕜) - ε : 𝕜) : WithBotTop 𝕜)
  rw [_root_.mem_epsSubdifferentialAt]
  simp

/-- At tolerance `0`, the vector bridge recovers the exact supporting-affine subdifferential
set. -/
-- Proof sketch: ext on `g`, rewrite membership in `Function.epsSubdifferentialAt f x 0` by the
-- vector-valued characterization lemma, and simplify the zero-tolerance term.
@[simp] theorem epsSubdifferentialAt_zero {f : E → WithBotTop 𝕜} {x : E} :
    epsSubdifferentialAt f x 0 = ∂ᵥf(x) := by
  ext g
  rw [mem_epsSubdifferentialAt, mem_subdifferentialAt]
  simp

end Function

end

/-! ### Theorem_23_6 (from Chap05) -/
noncomputable section

open Filter
open scoped Rockafellar Topology

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace Function.IsClosedProperConvex

variable {f : E → EReal} {x y : E}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 23.6 identifies the directional derivative at a finite point with the
  right limit, as `ε ↓ 0`, of the support functions of the approximate subdifferentials
  `∂_ε f(x)`.
- `core/canonical`: the existing owners are `Function.directionalDerivativeAt`, the dual-valued
  approximate subdifferential `_root_.epsSubdifferentialAt`, the support-function notation
  `δᵛ(· | ·)`, and the closed/proper/convex owner `Function.IsClosedProperConvex`.
- `bridge/view`: no Euclidean self-duality bridge is needed here; the source set `∂_ε f(x)` is
  kept on the canonical dual `StrongDual ℝ E`, and the limit is expressed by the standard
  right-neighborhood filter `𝓝[>] (0 : ℝ)`.

Domain-style sampling used here:
- `Function.directionalDerivativeAt` and Theorem 23.1's finite-point infimum formula from
  `Chap05/Theorem_23_1`;
- `_root_.epsSubdifferentialAt` from `Chap05/Definition_23_6`;
- Proposition 23.6.1's conjugate-sublevel description of `_root_.epsSubdifferentialAt`;
- the support-function owner `δᵛ(· | ·)` from `Chap01/Defintion_4_8_2`.

Primitive data vs derived API:
- primitive inputs: a closed proper convex function `f`, a finite base point `x`, and a
  direction `y`;
- derived surface: the support-function family
  `ε ↦ δᵛ(y | _root_.epsSubdifferentialAt f x ε)` and its right-limit value.

Layer target: `source-facing`, stated directly on the chapter's canonical owners.
-/

-- Proof sketch: rewrite `ε ↦ δᵛ(y | _root_.epsSubdifferentialAt f x ε)` using Proposition 23.6.1
-- as the support function of the conjugate sublevel sets of `translatedDefectFunction f x`.
-- Theorem 13.5 identifies that support function with the positively homogeneous convex function
-- generated by `translatedDefectFunction f x + ε`, and the source formula shows these values
-- decrease to the positive-difference-quotient infimum from Theorem 23.1. Since `hf` gives the
-- closed/proper/convex hypotheses needed for that route, the right limit is
-- `directionalDerivativeAt f x y`.
/-- Theorem 23.6: if `f` is closed proper convex and `x` is a finite point of `f`, then as
`ε ↓ 0` the support function of the approximate subdifferential `∂_ε f(x)` converges to the
directional derivative `f'(x; y)`. -/
theorem tendsto_supportFunction_epsSubdifferentialAt
    (hf : f.IsClosedProperConvex) (hx : x ∈ dom(f)) (hx_bot : f x ≠ ⊥) :
    Tendsto
      (fun ε : ℝ ↦
        δᵛ(y | {xStar : StrongDual ℝ E |
          ∀ z, f z ≥ f x + (((xStar (z - x) - ε : ℝ) : EReal))}))
      (𝓝[>] (0 : ℝ)) (𝓝 (directionalDerivativeAt f x y)) := sorry

end Function.IsClosedProperConvex

end
