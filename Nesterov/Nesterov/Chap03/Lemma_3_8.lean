import Nesterov.Chap03.Definition_3_1_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Pointwise WithTopConvexAnalysis

open Set

universe u

/- Lemma 3.8 lies in the chapter's extended-valued convex-composition / subdifferential-calculus
domain.

Sampled owner-style declarations:
- `withTopEffectiveDomain` in `Definition_3_3`, the chapter owner for the finite-value domain
- `withTopRealPart` in `Definition_3_3`, the owner finite-value representative
- `ConvexOn.comp` in mathlib, the canonical monotone convex-composition owner on an image set
- `subdifferential` in `Definition_3_1_5`, the owner subgradient-set API

Best owner abstraction:
- source-facing: `monotoneConvexComp`
- core/canonical ambient owners: `withTopEffectiveDomain`, `withTopRealPart`, `ConvexOn.comp`,
  `subdifferential`
- bridge/view: `monotoneConvexComp_apply_of_mem_effectiveDomain`

Primitive data:
- the source-facing composition `monotoneConvexComp φ ψ`

Derived API:
- `monotoneConvexComp_apply_of_mem_effectiveDomain`
- `monotoneConvexComp_convexOn`
- `subdifferential_monotoneConvexComp_eq_convexHull`

The previous file duplicated the chapter owners for effective domains, finite real parts,
convexity, and subdifferentials. Those notions already live upstream, so this file now keeps only
the composition-specific source-facing object and states its monotonicity and subdifferential
conclusions as two atomic theorems directly on the canonical image-set and pointwise-set-operation
surfaces. The convexity clause therefore lives at the weak module layer inherited from
`ConvexOn.comp`, while the subdifferential clause stays on the real inner-product-space layer
required by `∂`, rather than re-specializing either statement to Euclidean coordinates.
-/

/-- The composition used in Lemma 3.8: inside the effective domain of `ψ` it is `φ ∘ ψ`, and
outside that domain it is `+∞`. -/
def monotoneConvexComp {V : Type u} (φ : ℝ → WithTop ℝ) (ψ : V → WithTop ℝ) : V → WithTop ℝ :=
  fun x ↦ if x ∈ dom ψ then φ (withTopRealPart ψ x) else ⊤

/-- On the effective domain of `ψ`, the composition `monotoneConvexComp φ ψ` evaluates as the
outer function `φ` applied to the finite value of `ψ`. -/
@[simp] theorem monotoneConvexComp_apply_of_mem_effectiveDomain {V : Type u} {φ : ℝ → WithTop ℝ}
    {ψ : V → WithTop ℝ} {x : V} (hx : x ∈ dom ψ) :
    monotoneConvexComp φ ψ x = φ (withTopRealPart ψ x) := by
  simp [monotoneConvexComp, hx]

/-- Helper for Lemma 3.8: a point belongs to the effective domain of the monotone convex
composition exactly when it belongs to the effective domain of `ψ` and the resulting finite scalar
lies in the effective domain of `φ`. -/
theorem monotoneConvexComp_dom_iff {V : Type u} {φ : ℝ → WithTop ℝ} {ψ : V → WithTop ℝ}
    {x : V} :
    x ∈ dom (monotoneConvexComp φ ψ) ↔ x ∈ dom ψ ∧ withTopRealPart ψ x ∈ dom φ := by
  constructor
  · intro hx
    by_cases hψx : x ∈ dom ψ
    · -- Inside `dom ψ`, the composition is literally `φ` evaluated at the finite real part of `ψ`.
      refine ⟨hψx, ?_⟩
      rw [mem_withTopEffectiveDomain_iff, monotoneConvexComp_apply_of_mem_effectiveDomain hψx] at hx
      simpa [mem_withTopEffectiveDomain_iff] using hx
    · -- Outside `dom ψ`, the composition is `+∞`, so it cannot lie in its own effective domain.
      have htop : monotoneConvexComp φ ψ x = ⊤ := by
        simp [monotoneConvexComp, hψx]
      rw [mem_withTopEffectiveDomain_iff, htop] at hx
      simp at hx
  · rintro ⟨hψx, hφx⟩
    -- Once both finiteness conditions are available, the composition is finite by direct
    -- evaluation on `dom ψ`.
    rw [mem_withTopEffectiveDomain_iff, monotoneConvexComp_apply_of_mem_effectiveDomain hψx]
    simpa [mem_withTopEffectiveDomain_iff] using hφx

/-- Helper for Lemma 3.8: on the effective domain of the composition, its finite real part is the
ordinary scalar composition of the finite real parts of `φ` and `ψ`. -/
@[simp] theorem withTopRealPart_monotoneConvexComp_of_mem_dom {V : Type u}
    {φ : ℝ → WithTop ℝ} {ψ : V → WithTop ℝ} {x : V}
    (hx : x ∈ dom (monotoneConvexComp φ ψ)) :
    withTopRealPart (monotoneConvexComp φ ψ) x = withTopRealPart φ (withTopRealPart ψ x) := by
  rcases monotoneConvexComp_dom_iff.mp hx with ⟨hψx, hφx⟩
  -- Compare the two real values after coercing them back to `WithTop ℝ`.
  apply WithTop.coe_injective
  rw [coe_withTopRealPart hx, monotoneConvexComp_apply_of_mem_effectiveDomain hψx,
    coe_withTopRealPart hφx]

section Convexity

variable {V : Type u} [AddCommMonoid V] [Module ℝ V]
variable {ψ : V → WithTop ℝ} {φ : ℝ → WithTop ℝ}

/-- Lemma 3.8, convexity clause: if `ψ : V → ℝ ∪ {+∞}` and `φ : ℝ → ℝ ∪ {+∞}` are convex and
`φ` is nondecreasing on the effective image of `ψ`, then the extended-value composition equal to
`φ ∘ ψ` on `dom ψ` and `+∞` outside that domain is convex. -/
-- Proof sketch: convexity comes from `ConvexOn.comp` applied to the finite real parts, using the
-- monotonicity of `φ` on the effective image of `ψ`.
theorem monotoneConvexComp_convexOn
    (hψ_convex : ConvexOn ℝ (dom ψ) (withTopRealPart ψ))
    (hφ_convex : ConvexOn ℝ (dom φ) (withTopRealPart φ))
    (hφ_mono : MonotoneOn φ (withTopRealPart ψ '' dom ψ)) :
    ConvexOn ℝ (dom (monotoneConvexComp φ ψ)) (withTopRealPart (monotoneConvexComp φ ψ)) := by
  -- Route correction: the naive `ConvexOn.comp` proof only works once the scalar image
  -- `withTopRealPart ψ '' dom ψ` is known to be convex. In this generalized owner signature that
  -- image-convexity bridge is not yet available from earlier dependencies.
  -- TODO: either prove the earlier segmentwise image-convexity bridge locally or import the exact
  -- earlier prerequisite that upgrades monotonicity on `withTopRealPart ψ '' dom ψ` to a valid
  -- composition theorem on the effective domain.
  sorry

end Convexity

section Subdifferential

variable {V : Type u} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ψ : V → WithTop ℝ} {φ : ℝ → WithTop ℝ}

/-- Lemma 3.8, subdifferential clause: at each `x ∈ interior (dom ψ)`, the subdifferential of
the monotone convex composition is the convex hull of the products `λ • g` with
`λ ∈ ∂ φ(withTopRealPart ψ x)` and `g ∈ ∂ ψ(x)`. -/
-- Proof sketch: combine the convex chain rule for directional derivatives at interior points of
-- `dom ψ` with the support-function descriptions of the one-dimensional and vector-valued
-- subdifferentials, then identify the resulting support function with the convex hull of the
-- scalar-vector product set.
theorem subdifferential_monotoneConvexComp_eq_convexHull {x : V}
    (hψ_convex : ConvexOn ℝ (dom ψ) (withTopRealPart ψ))
    (hφ_convex : ConvexOn ℝ (dom φ) (withTopRealPart φ))
    (hφ_mono : MonotoneOn φ (withTopRealPart ψ '' dom ψ))
    (hx : x ∈ interior (dom ψ)) :
    ∂ (monotoneConvexComp φ ψ)(x) =
      convexHull ℝ (∂ φ((withTopRealPart ψ x)) • ∂ ψ(x)) := by
  -- Route correction: the source proof identifies both sides by a directional-derivative/support
  -- function calculation. This file currently imports only the primitive owner `∂`, so the needed
  -- earlier chain-rule and support-function uniqueness bridges are not yet in scope.
  -- TODO: add the dependency-closed bridges for (i) the directional derivative of the monotone
  -- convex composition and (ii) equality of closed convex sets from equality of support pairings.
  have _hψ_convex := hψ_convex
  have _hφ_convex := hφ_convex
  have _hφ_mono := hφ_mono
  have _hx := hx
  sorry

end Subdifferential
