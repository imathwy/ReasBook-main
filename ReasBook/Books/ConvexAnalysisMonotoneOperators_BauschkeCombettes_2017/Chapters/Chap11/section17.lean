import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_11_17 (from Chap11) -/
universe u

namespace ERealFunction

section InnerProduct

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A lower-semicontinuous strongly convex function belongs to the canonical class `Γ₀(H)`. -/
theorem mem_gammaZero_of_lowerSemicontinuous_of_stronglyConvex
    {f : H → Set.Ioi (⊥ : EReal)} {β : ℝ} (hlower : LowerSemicontinuous f.asEReal)
    (hstrong : StronglyConvex f β) :
    f ∈ Γ₀(H) :=
  ⟨hlower, hstrong.uniformlyConvex.convexOn⟩

-- Proof sketch: package the primitive hypotheses into the canonical owner input
-- `f ∈ Γ₀(H)` and `UniformlyConvex f _`, then apply Proposition 17.26 (2).
/-- Corollary 11.17 (1): a lower-semicontinuous strongly convex function is supercoercive. -/
theorem supercoercive_of_lowerSemicontinuous_of_stronglyConvex
    {f : H → Set.Ioi (⊥ : EReal)} (hlower : LowerSemicontinuous f.asEReal) {β : ℝ}
    (hstrong : StronglyConvex f β) :
    Supercoercive f.asEReal :=
  supercoercive_of_mem_gammaZero_of_uniformlyConvex
    (mem_gammaZero_of_lowerSemicontinuous_of_stronglyConvex hlower hstrong)
    hstrong.uniformlyConvex

end InnerProduct

section RealHilbert

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: this is the same bridge to the canonical owner layer, followed by
-- Proposition 17.26 (3).
/-- Corollary 11.17 (2): a lower-semicontinuous strongly convex function on a complete real
Hilbert space has exactly one global minimizer over `H`. -/
theorem existsUnique_mem_argmin_of_lowerSemicontinuous_of_stronglyConvex
    {f : H → Set.Ioi (⊥ : EReal)} (hlower : LowerSemicontinuous f.asEReal) {β : ℝ}
    (hstrong : StronglyConvex f β) :
    ∃! x : H, x ∈ Argmin f.asEReal :=
  existsUnique_mem_argmin_of_mem_gammaZero_of_uniformlyConvex
    (mem_gammaZero_of_lowerSemicontinuous_of_stronglyConvex hlower hstrong)
    hstrong.uniformlyConvex

end RealHilbert

end ERealFunction
