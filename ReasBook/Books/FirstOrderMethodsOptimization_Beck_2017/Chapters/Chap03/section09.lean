

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_9 (from Chap03) -/
universe u

open scoped Topology

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Definition 3.9 is `source-facing` at the Chapter 3 owners `directional_derivative` and
`subdifferential`: the public statement is the textbook maximum formula for the directional
derivative. The Chapter 2 support-function owner is only a downstream bridge reformulation, so it
is not re-exported from this source-facing file. -/
recall directional_derivative
recall subdifferential

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

-- Proof sketch: combine the convex subgradient inequality with the interior-point nonemptiness and
-- compactness properties of the finite-dimensional subdifferential to show that the pairing map
-- `g ↦ g d` attains its maximum on `subdifferential f x`, and that this maximum equals the
-- directional derivative. The interior-point hypothesis already forces `effective_domain f` to be
-- nonempty, so the only extra properness ingredient needed here is that `f` never takes the value
-- `⊥`.
/-- Definition 3.9: for a convex extended-real-valued function that never takes the value `⊥`, the
directional derivative at an interior point of the effective domain is the maximum of the
subgradient pairings `g d` over all `g ∈ ∂ f(x)`. -/
theorem directional_derivative_isGreatest_subgradient_pairings_at_interior_point
    {f : E → EReal} {x d : E} (h_ne_bot : ∀ y, f y ≠ ⊥) (hconvex : is_convex_function f)
    (hx : x ∈ interior (effective_domain f)) :
    IsGreatest ((fun g : Module.Dual ℝ E ↦ (g d : EReal)) '' subdifferential f x)
      (directional_derivative f x d) := sorry

end

/-! ### Proposition_3_9 (from Chap03) -/
universe u

section

open Bornology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Proposition 3.9 is a `bridge/view` statement in the chapter convex-analysis API. Domain
sampling against Definition 3.6, Theorem 3.1, and Theorem 3.3 shows that the relevant owner
surface is already the pair `subdifferential_domain` / `strongDualSubdifferential`, built over the
Chapter 2 owner `effective_domain`; there is no further upstream declaration with the same
conclusion to recall here, so this file should state the proposition directly on that owner API
instead of introducing a parallel wrapper. The literal textbook wording omits the domain condition
`x ∈ subdifferential_domain f`, but that hypothesis is mathematically necessary: if
`x ∉ subdifferential_domain f`, then the subdifferential is empty and hence bounded. The file keeps
that necessary hypothesis explicit in the proposition statement and records the omission only here
in comments. -/
recall effective_domain
recall subdifferential_domain
recall strongDualSubdifferential

-- Proof sketch: translating the affine hull of `effective_domain f` by `-x` does not change its
-- affine dimension, so the geometric hypothesis becomes the strict finrank inequality for the
-- direction space of `affineSpan ℝ (effective_domain f)`. If `x ∈ subdifferential_domain f`, then
-- finite dimensionality upgrades an algebraic-dual subgradient at `x` to the continuous-dual
-- bridge `strongDualSubdifferential f x`. Apply the standard unboundedness argument in codimension
-- at least one on that bridge set.
/-- Proposition 3.9: if the affine hull of the effective domain has direction-space dimension
strictly smaller than the ambient space, equivalently
`Module.finrank ℝ (affineSpan ℝ (effective_domain f)).direction < Module.finrank ℝ E`, then every
point of the owner subdifferential domain `dom(∂ f)` has an unbounded continuous-dual
subdifferential. -/
theorem subdifferential_unbounded_of_affineSpan_effective_domain_direction_finrank_lt
    (f : E → EReal) (x : E)
    (hdim :
      Module.finrank ℝ (affineSpan ℝ (effective_domain f)).direction <
        Module.finrank ℝ E)
    (hx : x ∈ subdifferential_domain f) :
    ¬ IsBounded (strongDualSubdifferential f x) := sorry

end

/-! ### Theorem_3_9 (from Chap03) -/
universe u v

section

variable {E : Type u} {ι : Type v}
variable [AddCommMonoid E] [Module ℝ E]

/- Theorem 3.9 is a `source-facing` item in the chapter directional-derivative API. The owner
notions are `has_directional_derivative_at` and `directional_derivative` from Definition 3.8. The
active-index collection is auxiliary derived data, so this file keeps it inline in the theorem
statement instead of introducing a parallel public wrapper around the subtype
`{i | f i x = ⨆ j, f j x}`. -/
recall has_directional_derivative_at
recall directional_derivative

-- Proof sketch: for sufficiently small positive steps `t`, the indices that are not active at `x`
-- remain strictly below the active ones because each `f i` has a finite directional derivative at
-- `x` along `d`, hence is directionally continuous there. Thus the difference quotient of the
-- pointwise supremum agrees near `0⁺` with the supremum over the active subfamily, and the limit
-- of a finite supremum is the supremum of the individual directional-derivative limits.
/-- Theorem 3.9: for a finite family of extended-real-valued functions, if every directional
derivative at `x` along `d` exists as a finite real value, then the directional derivative of the
pointwise maximum is the maximum of the directional derivatives over the active indices
`I(x) = {i | fᵢ x = max_j fⱼ x}`. -/
theorem directional_derivative_iSup_eq_iSup_active_indices
    [Finite ι] [Nonempty ι]
    (f : ι → E → EReal) (x d : E)
    (hdir : ∀ i : ι, ∃ ℓ : ℝ, has_directional_derivative_at (f i) x d (ℓ : EReal)) :
    directional_derivative (fun y ↦ ⨆ i : ι, f i y) x d =
      iSup fun i : {i : ι // f i x = ⨆ j : ι, f j x} ↦ directional_derivative (f i) x d :=
  sorry

end
