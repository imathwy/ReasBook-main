import Mathlib
import StacksProject_2024.Chap31.Definition_31_18_2

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry

universe u

open CategoryTheory
open Scheme.IdealSheafData

-- Semantic recall: `lean_leansearch` recalled `AlgebraicGeometry.Flat.comp`; the Chapter 31 owner
-- for relative effective Cartier divisors in this workspace is
-- `IsRelativeEffectiveCartierDivisor f D` on `X.IdealSheafData`, and Lemma `31.13.8` now supplies
-- the source-facing divisor decomposition through the canonical sum owner
-- `effectiveCartierDivisorSum`.

section

variable {X S : Scheme.{u}}
variable [MonoidalCategory (RingedSpace.Modules X.toRingedSpace)]

/-- Lemma 31.18.4: let `f : X ⟶ S` be a morphism of schemes and let `D₁`, `D₂`, and `D` be
effective Cartier divisors on `X`, with `D₁` and `D₂` relative effective Cartier divisors on
`X/S`. If `D₂ = D₁ + D`, represented here by the canonical sum identity
`D₂ = effectiveCartierDivisorSum D₁ D`, then `D` is a relative
effective Cartier divisor on `X/S`. This is the source-facing form of the divisor supplied by
Lemma `31.13.8`. -/
theorem IsRelativeEffectiveCartierDivisor.of_eq_effectiveCartierDivisorSum
    (f : X ⟶ S) (D₁ D₂ D : X.IdealSheafData)
    [IsRelativeEffectiveCartierDivisor f D₁] [IsRelativeEffectiveCartierDivisor f D₂]
    [D.IsEffectiveCartierDivisor]
    (hsum : D₂ = effectiveCartierDivisorSum D₁ D) :
    IsRelativeEffectiveCartierDivisor f D := sorry

/-- Companion to Lemma 31.18.4: under the same divisor-sum identity, the structural morphism
`D ⟶ S` is flat. This exposes the flatness consequence directly without unpacking
`IsRelativeEffectiveCartierDivisor`. -/
theorem flat_subschemeι_of_eq_effectiveCartierDivisorSum
    (f : X ⟶ S) (D₁ D₂ D : X.IdealSheafData)
    [IsRelativeEffectiveCartierDivisor f D₁] [IsRelativeEffectiveCartierDivisor f D₂]
    [D.IsEffectiveCartierDivisor]
    (hsum : D₂ = effectiveCartierDivisorSum D₁ D) :
    Flat (D.subschemeι ≫ f) := by
  let _ : IsRelativeEffectiveCartierDivisor f D :=
    IsRelativeEffectiveCartierDivisor.of_eq_effectiveCartierDivisorSum f D₁ D₂ D hsum
  infer_instance

end

end AlgebraicGeometry
