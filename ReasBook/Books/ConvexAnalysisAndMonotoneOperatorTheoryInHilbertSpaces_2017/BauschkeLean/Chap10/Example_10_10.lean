import BauschkeLean.Chap08.Example_8_22
import BauschkeLean.Chap08.Proposition_8_17
import BauschkeLean.Chap10.Definition_10_7
import BauschkeLean.Chap11.Definition_11_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open ERealFunction

section Hilbert

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

section RadialIntegral

variable (φ : NNReal → NNReal)

local notation "radialPrimitive" =>
  fun x : H ↦ ∫ t in 0..‖x‖, (φ (Real.toNNReal t) : ℝ)

-- Semantic recall: `UniformConvexOn` is the canonical owner for bounded-set uniform convexity,
-- and the source-facing clause here restores the monotonicity hypothesis from the book.
/-- Example 10.10 (1): if `φ : ℝ≥0 → ℝ≥0` is increasing and `C` is a nonempty bounded
convex subset of `H`, then the radial primitive
`x ↦ ∫ t in 0..‖x‖, (φ (Real.toNNReal t) : ℝ)` is uniformly convex on `C`. -/
theorem exists_uniformConvexOn_radialIntegral_of_monotone
    (C : Set H) (φ : NNReal → NNReal) (hφ_mono : Monotone φ)
    (hC_nonempty : C.Nonempty) (hC_bounded : Bornology.IsBounded C) (hC_convex : Convex ℝ C) :
    ∃ ψ : ℝ → ℝ,
      (∀ ⦃r : ℝ⦄, r ≠ 0 → 0 < ψ r) ∧ UniformConvexOn C ψ radialPrimitive := sorry

end RadialIntegral

section NormRpow

variable (C : Set H) (p : ℝ)

local notation "normRpow" => fun x : H ↦ ‖x‖ ^ p
local notation "normRpowEReal" => Function.toEReal (fun x : H ↦ ‖x‖ ^ p)
local notation "constrainedNormRpow" => pointwiseAdd normRpowEReal (ι[C])

-- Semantic recall: the source-facing constrained function `‖·‖ ^ p + ι_C` naturally uses the
-- `ERealFunction.UniformlyConvex` owner, and the canonical real-valued `UniformConvexOn` view is
-- kept as a thin companion bridge for downstream reuse.
/-- Example 10.10 (2): if `p ∈ ]1,+∞[` and `C` is a nonempty bounded convex subset of `H`, then
the constrained function `‖·‖ ^ p + ι_C` is uniformly convex. -/
theorem exists_uniformlyConvex_norm_rpow_add_indicator_on_nonempty_bounded_convex
    (C : Set H) (hC_nonempty : C.Nonempty) (hC_bounded : Bornology.IsBounded C)
    (hC_convex : Convex ℝ C) (p : ℝ) (hp : 1 < p) :
    ∃ φ : NNReal → EReal, UniformlyConvex constrainedNormRpow φ := sorry

/-- Canonical bridge for clause (2): the constrained uniform-convexity formulation yields the
standard `UniformConvexOn` statement for `x ↦ ‖x‖ ^ p` on bounded convex `C`. -/
theorem exists_uniformConvexOn_norm_rpow_on_bounded_convex
    (C : Set H) (hC_bounded : Bornology.IsBounded C)
    (hC_convex : Convex ℝ C) (p : ℝ) (hp : 1 < p) :
    ∃ ψ : ℝ → ℝ, (∀ ⦃r : ℝ⦄, r ≠ 0 → 0 < ψ r) ∧ UniformConvexOn C ψ normRpow := sorry

end NormRpow

end Hilbert
