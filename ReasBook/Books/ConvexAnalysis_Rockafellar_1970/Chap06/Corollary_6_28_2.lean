import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators

universe u v w

namespace Function

section

variable {𝕜 : Type v} {E : Type u} {β : Type w} {ι : Type*}
variable [AddCommMonoid β]

/-- Textbook notation for the finite Lagrange combination
`f₀ + ∑ i ∈ s, λ i • f i`. -/
scoped notation "L[" s "](" f₀ ", " f ", " lam ")" =>
  (fun x ↦ f₀ x + ∑ i ∈ s, lam i • f i x)

section Minimizer

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid E] [SMul 𝕜 E]
variable [PartialOrder β] [IsOrderedAddMonoid β]
variable [Module 𝕜 β] [PosSMulMono 𝕜 β]

-- Proof sketch: this is exactly `StrictConvexOn.eq_of_isMinOn` specialized to
-- `fun x ↦ f₀ x + ∑ i ∈ s, lam i • f i x`.
/-- If a Lagrange combination is strictly convex on `C`, then any two minimizers on `C` coincide. -/
theorem eq_of_isMinOn_lagrangeCombination
    {C : Set E} {s : Finset ι} {f₀ : E → β} {f : ι → E → β} {lam : ι → 𝕜}
    (hstrict : StrictConvexOn 𝕜 C (L[s](f₀, f, lam)))
    {x y : E}
    (hx : x ∈ C) (hy : y ∈ C)
    (hminx : IsMinOn (L[s](f₀, f, lam)) C x)
    (hminy : IsMinOn (L[s](f₀, f, lam)) C y) :
    x = y :=
  hstrict.eq_of_isMinOn hminx hminy hx hy

end Minimizer

section Strict

variable [CommSemiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [SMul 𝕜 E]
variable [PartialOrder β] [IsOrderedCancelAddMonoid β]
variable [Module 𝕜 β] [PosSMulMono 𝕜 β]

-- Proof sketch: each summand `fun x ↦ λ i • f i x` is convex on `C` by `ConvexOn.smul` because
-- `λ i ≥ 0`. Finite sums of convex functions are convex on `C`, and adding that convex sum to the
-- strictly convex objective `f₀` yields a strictly convex function via
-- `StrictConvexOn.add_convexOn`.
/-- A Lagrange combination is strictly convex on `C` when its objective term is strictly convex on
`C` and every weighted constraint term has a nonnegative coefficient and a convex underlying
function. -/
theorem strictConvexOn_lagrangeCombination_of_nonneg
    {C : Set E} {s : Finset ι} {f₀ : E → β} {f : ι → E → β} {lam : ι → 𝕜}
    (hf₀ : StrictConvexOn 𝕜 C f₀)
    (hf : ∀ i ∈ s, ConvexOn 𝕜 C (f i))
    (hLam : ∀ i ∈ s, 0 ≤ lam i) :
    StrictConvexOn 𝕜 C (L[s](f₀, f, lam)) := sorry

end Strict

section StrictMinimizer

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid E] [SMul 𝕜 E]
variable [PartialOrder β] [IsOrderedCancelAddMonoid β]
variable [Module 𝕜 β] [PosSMulMono 𝕜 β]

-- Proof sketch: first apply `strictConvexOn_lagrangeCombination_of_nonneg` to obtain strict
-- convexity of `fun x ↦ f₀ x + ∑ i ∈ s, lam i • f i x` on `C`. Then apply
-- `eq_of_isMinOn_lagrangeCombination`.
/-- Corollary 6.28.2: if `f₀` is strictly convex on `C`, then the Lagrange combination
`h = f₀ + ∑ i ∈ s, λ i • f i` with nonnegative coefficients and convex summands is strictly convex
on `C`; consequently, if the infimum of `h` on `C` is attained, the minimizing point is unique. -/
theorem eq_of_isMinOn_lagrangeCombination_of_nonneg
    {C : Set E} {s : Finset ι} {f₀ : E → β} {f : ι → E → β} {lam : ι → 𝕜}
    (hf₀ : StrictConvexOn 𝕜 C f₀)
    (hf : ∀ i ∈ s, ConvexOn 𝕜 C (f i))
    (hLam : ∀ i ∈ s, 0 ≤ lam i)
    {x y : E}
    (hx : x ∈ C) (hy : y ∈ C)
    (hminx : IsMinOn (L[s](f₀, f, lam)) C x)
    (hminy : IsMinOn (L[s](f₀, f, lam)) C y) :
    x = y :=
  let hstrict : StrictConvexOn 𝕜 C (L[s](f₀, f, lam)) :=
    strictConvexOn_lagrangeCombination_of_nonneg
      (C := C) (s := s) (f₀ := f₀) (f := f) (lam := lam) hf₀ hf hLam
  eq_of_isMinOn_lagrangeCombination
    (hstrict := hstrict)
    hx hy hminx hminy

end StrictMinimizer

end

end Function
