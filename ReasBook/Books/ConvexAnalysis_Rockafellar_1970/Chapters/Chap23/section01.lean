

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_23_1 (from Chap05) -/
noncomputable section

universe u v

section

open scoped Rockafellar

variable {E : Type u} [AddCommMonoid E]
variable {𝕜 : Type v}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithTopBot 𝕜)]
variable [SMul 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: this item states that for a convex function finite-valued at `x`, the
  positive directional difference quotient in a fixed direction is monotone on `λ > 0`, hence the
  Chapter 23 directional derivative exists with the source infimum formula; it also records the
  direction-side convexity, positive homogeneity, normalization at `0`, and the inequality
  `-f'(x; -y) ≤ f'(x; y)`.
- `core/canonical`: the owner abstractions are already the Chapter 23 directional-derivative
  owners `Function.directionalDifferenceQuotientAt`, `Function.HasDirectionalDerivativeAt`, and
  `Function.directionalDerivativeAt`, together with the existing function-side owners
  `Function.IsConvex` and `Function.PositivelyHomogeneous`.
- `bridge/view`: no new wrapper owner is introduced; the source theorem is expressed directly on
  these canonical owners, while the later support-function and subdifferential theorems remain in
  their own files.

Domain-style sampling used here:
- `Function.directionalDifferenceQuotientAt`, `Function.HasDirectionalDerivativeAt`, and
  `Function.directionalDerivativeAt` from `Chap05/Lemma_23_0_1`;
- the chapter effective-domain owner `dom(·)` from `Chap01/Definition_4_4`.

Primitive data vs derived API:
- primitive data: a convex function `f`, a base point `x` with `x ∈ dom(f)` and `f x ≠ ⊥`, and a
  direction `y`;
- primitive owner surfaces: monotonicity of the positive difference quotient and the resulting
  `HasDirectionalDerivativeAt` / `directionalDerivativeAt` infimum formula;
- derived API: convexity and positive homogeneity of `y ↦ directionalDerivativeAt f x y`, its
  value at `0`, and the reflected-direction inequality; these remain source-facing finite-point
  consequences here rather than parallel owner declarations.

Layer target: `source-facing`, reusing the canonical Chapter 23 owners directly.

Ambient-assumption minimization:
- the positive-difference-quotient, infimum, convexity, positive-homogeneity, and zero-direction
  clauses use only the additive-monoid scalar-action structure on directions;
- the reflected-direction inequality is separated below into the additive-group layer genuinely
  needed for the argument `-y`.
-/

namespace Function

/- Local bridge so theorem surfaces stay on `WithTopBot` while reusing chapter scalar action. -/
local instance instSMulWithTopBot_reflected : SMul 𝕜 (WithTopBot 𝕜) :=
  (show SMul 𝕜 (WithBotTop 𝕜) from inferInstance)

section FinitePoint

variable {f : E → WithTopBot 𝕜} {x : E}

-- Proof sketch: restrict `f` to the affine line `λ ↦ x + λ • y`. Convexity of that one-variable
-- function implies monotonicity of its secant slopes from `0`, and those secant slopes are
-- exactly `directionalDifferenceQuotientAt f x y` on `λ > 0`.
/-- For a convex function finite-valued at `x`, the positive directional difference quotient in the
fixed direction `y` is nondecreasing as a function of `λ > 0`. -/
theorem directionalDifferenceQuotientAt_monotoneOn_pos
    (hf_convex : f.IsConvex 𝕜) (hx : x ∈ dom(f)) (hx_bot : f x ≠ ⊥)
    (y : E) :
    MonotoneOn (directionalDifferenceQuotientAt f x y) (Set.Ioi (0 : 𝕜)) := sorry

-- Proof sketch: the previous monotonicity theorem gives a one-sided monotone limit as
-- `λ → 0+`, and for a monotone scalar-parameter family this limit is the infimum of the positive
-- values. Package that limit with the Chapter 23 owner `HasDirectionalDerivativeAt`.
/-- The directional derivative at a finite point exists as the infimum of the positive directional
difference quotients. -/
theorem hasDirectionalDerivativeAt_sInf_directionalDifferenceQuotientAt
    (hf_convex : f.IsConvex 𝕜) (hx : x ∈ dom(f)) (hx_bot : f x ≠ ⊥)
    (y : E) :
    HasDirectionalDerivativeAt f x y
      (sInf ((Set.Ioi (0 : 𝕜)).image (directionalDifferenceQuotientAt f x y))) := sorry

-- Proof sketch: evaluate the canonical limit-valued owner `directionalDerivativeAt` at the limit
-- supplied by `hasDirectionalDerivativeAt_sInf_directionalDifferenceQuotientAt`.
/-- Theorem 23.1: for a convex function finite-valued at `x`, the directional derivative
`f'(x; y)` equals the infimum of the positive directional difference quotients
`(f (x + λ • y) - f x) / λ`. -/
theorem directionalDerivativeAt_eq_sInf_directionalDifferenceQuotientAt
    (hf_convex : f.IsConvex 𝕜) (hx : x ∈ dom(f)) (hx_bot : f x ≠ ⊥)
    (y : E) :
    directionalDerivativeAt f x y =
      sInf ((Set.Ioi (0 : 𝕜)).image (directionalDifferenceQuotientAt f x y)) := sorry

-- Proof sketch: apply the source theorem above in two directions, then combine the infimum
-- formula with the convexity of the underlying two-variable secant map in the direction variable.
/-- At a finite point of a convex function, the map `y ↦ directionalDerivativeAt f x y` is
convex. -/
theorem isConvex_directionalDerivativeAt_of_finite_point
    (hf_convex : f.IsConvex 𝕜) (hx : x ∈ dom(f)) (hx_bot : f x ≠ ⊥)
    :
    (directionalDerivativeAt f x).IsConvex 𝕜 := sorry

-- Proof sketch: rewrite the infimum formula after scaling the direction by a positive scalar and
-- reindex the positive parameter `λ` by `c * λ`.
/-- At a finite point of a convex function, the directional derivative is positively homogeneous in
the direction variable. -/
theorem positivelyHomogeneous_directionalDerivativeAt_of_finite_point
    (hf_convex : f.IsConvex 𝕜) (hx : x ∈ dom(f)) (hx_bot : f x ≠ ⊥)
    :
    (directionalDerivativeAt f x).PositivelyHomogeneous 𝕜 := sorry

-- Proof sketch: evaluate positive homogeneity at any positive scalar multiple of the zero
-- direction, or read the quotient formula directly in direction `0`.
/-- At a finite point of a convex function, the directional derivative in the zero direction is
zero. -/
theorem directionalDerivativeAt_zero_of_finite_point
    (hf_convex : f.IsConvex 𝕜) (hx : x ∈ dom(f)) (hx_bot : f x ≠ ⊥)
    :
    directionalDerivativeAt f x 0 = 0 := sorry

end FinitePoint

end Function

end

section

open scoped Rockafellar

variable {E : Type u} [AddCommGroup E]
variable {𝕜 : Type v}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithTopBot 𝕜)]
variable [SMul 𝕜 E]

namespace Function

/- Local bridge so theorem surfaces stay on `WithTopBot` while reusing chapter scalar action. -/
local instance instSMulWithTopBot : SMul 𝕜 (WithTopBot 𝕜) :=
  (show SMul 𝕜 (WithBotTop 𝕜) from inferInstance)

section ReflectedDirection

variable {f : E → WithTopBot 𝕜} {x : E}

-- Proof sketch: combine convexity of `y ↦ directionalDerivativeAt f x y` with its value `0` at
-- the midpoint of `y` and `-y`, equivalently with subadditivity at `y + (-y) = 0`.
/-- At a finite point of a convex function, the reflected directional derivatives satisfy
`-f'(x; -y) ≤ f'(x; y)` for every direction `y`. -/
theorem neg_directionalDerivativeAt_neg_le_of_finite_point
    (hf_convex : f.IsConvex 𝕜) (hx : x ∈ dom(f)) (hx_bot : f x ≠ ⊥)
    (y : E) :
    -directionalDerivativeAt f x (-y) ≤ directionalDerivativeAt f x y := sorry

end ReflectedDirection

end Function

end
