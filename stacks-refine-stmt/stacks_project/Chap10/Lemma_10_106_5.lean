import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/- 
Layering for this item:
- `source-facing`: the Stacks hypothesis that `R` is Noetherian local, `M` is finite, `x` is
  `M`-regular, and the quotient `QuotSMulTop x M` is free over `R ⧸ (x)`;
- `core/canonical`: the owner objects `QuotSMulTop x M`, `IsSMulRegular M x`,
  `Module.FinitePresentation R M`, and the local-ring freeness machinery in
  `Mathlib.RingTheory.LocalRing.Module`;
- `bridge/view`: Noetherianity plus `Module.Finite R M` only serve to supply the canonical finite
  presentation instance `Module.finitePresentation_of_finite R M`.
-/

-- Proof sketch: choose lifts in `M` of a basis of `QuotSMulTop x M` over `R ⧸ (x)`,
-- obtaining a surjection
-- `R^n → M` by Nakayama. Any relation among the lifts has coefficients in `xR`; divide by `x` and
-- use that `x` is a nonzerodivisor on `M` to show the kernel `K` satisfies `xK = K`, hence
-- `K = 0` by Nakayama's lemma.
private theorem free_of_isSMulRegular_of_free_quotSMulTop_of_finitePresentation
    [Module.FinitePresentation R M] {x : R} (hx : x ∈ maximalIdeal R) (hreg : IsSMulRegular M x)
    [Module.Free (R ⧸ Ideal.span ({x} : Set R)) (QuotSMulTop x M)] :
    Module.Free R M := sorry

/-- Lemma 10.106.5: if `R` is a Noetherian local ring, `x ∈ maximalIdeal R` is a nonzerodivisor on
a finite `R`-module `M`, and `M / xM`, written as `QuotSMulTop x M`, is free over
`R ⧸ Ideal.span {x}`, then `M` is free over `R`. -/
theorem free_of_isSMulRegular_of_free_quotSMulTop
    {x : R} (hx : x ∈ maximalIdeal R) (hreg : IsSMulRegular M x)
    [Module.Free (R ⧸ Ideal.span ({x} : Set R)) (QuotSMulTop x M)] :
    Module.Free R M := by
  let _ : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  exact free_of_isSMulRegular_of_free_quotSMulTop_of_finitePresentation hx hreg

end
