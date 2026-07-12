import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_23_0_6

-- Declarations for this item will be appended below by the statement pipeline.

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
