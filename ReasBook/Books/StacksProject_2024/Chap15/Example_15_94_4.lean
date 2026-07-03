import Mathlib
import stacks_project.Chap15.Definition_15_92_4
import stacks_project.Chap15.PrincipalIdeal

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Polynomial
open scoped PrincipalIdeal BigOperators

section

variable (p : ℕ) [Fact p.Prime]

local notation "Zp" => ℤ_[p]
local notation "ZpPoly" => Polynomial Zp
local notation:max "(p)" => principalIdeal (p : Zp)
local notation "ZpPolyHat" => AdicCompletion (p) ZpPoly

/- Domain-style sampling:
- primary domain: `(p)`-adic completions of `ℤ_[p][X]`, module-category cokernels, and
  derived/adic completeness for the resulting example module;
- sampled owner-side declarations:
  `principalIdeal` together with the owner notation `(f)`,
  `AdicCompletion.map`,
  `cokernel`,
  `ModuleCat.cokernelIsoRangeQuotient`,
  `ModuleCat.IsDerivedCompleteWithRespectTo`;
- best owner abstraction: the chapter owner `principalIdeal` for the ambient ideal `(p)`,
  together with the categorical cokernel of the completed substitution morphism; the
  quotient-by-range description remains only a bridge;
- primitive data: the principal ideal `(p)` in `ℤ_[p]` and the completed substitution linear map
  induced by `X ↦ pX`;
- derived API: the quotient-model bridge, derived completeness, the named geometric-series class in
  the cokernel, and failure of adic completeness.

Layer triage:
- `source-facing`: the completed substitution map and the example module defined as its cokernel;
- `core/canonical`: `AdicCompletion.map`, `cokernel`,
  `ModuleCat.IsDerivedCompleteWithRespectTo`, `IsAdicComplete`, and `principalIdeal`/`(p)`;
- `bridge/view`: `ModuleCat.cokernelIsoRangeQuotient`, identifying the categorical cokernel with
  the explicit quotient by the image. -/

/-- The map on ordinary `p`-adic completions induced by the substitution
`ℤ_[p][X] → ℤ_[p][X]`, `X ↦ pX`. -/
abbrev padicPolynomialCompletionMap :
    ZpPolyHat →ₗ[Zp] ZpPolyHat :=
  (AdicCompletion.map (p)
      ((aeval (C (p : Zp) * X) : ZpPoly →ₐ[Zp] ZpPoly).toLinearMap)).restrictScalars Zp

/-- Example 15.94.4: the example module is the cokernel of the map on ordinary `p`-adic
completions induced by `ℤ_[p][x] → ℤ_[p][y]`, `x ↦ py`; using the common polynomial ring
`ℤ_[p][X]`, Lean takes the categorical cokernel of the completed substitution morphism
`X ↦ pX`. -/
abbrev padicPolynomialCompletionCokernel : ModuleCat Zp :=
  cokernel (ModuleCat.ofHom (padicPolynomialCompletionMap p))

-- Proof sketch: Proposition `15.92.5` gives derived completeness for the completed polynomial
-- modules, and Lemma `15.92.6` shows that the cokernel of a morphism between derived-complete
-- modules is again derived complete.
/-- The cokernel of the completed substitution map `X ↦ pX` is derived complete as a
`ℤ_[p]`-module with respect to `(p)`. -/
theorem padicPolynomialCompletionCokernel_isDerivedComplete :
    (padicPolynomialCompletionCokernel p).IsDerivedCompleteWithRespectTo
      (p) :=
  sorry

private abbrev padicPolynomialCompletionGeometricSeriesTruncation (n : ℕ) : ZpPoly :=
  ∑ i ∈ Finset.range n, C ((p : Zp) ^ i) * X ^ i

private abbrev padicPolynomialCompletionGeometricSeriesToQuotient (n : ℕ) :
    Zp →ₗ[Zp] (ZpPoly ⧸ (((p) ^ n) • (⊤ : Submodule Zp ZpPoly))) :=
  (Submodule.mkQ (((p) ^ n) • (⊤ : Submodule Zp ZpPoly))).comp <|
    LinearMap.smulRight (LinearMap.id : Zp →ₗ[Zp] Zp)
      (padicPolynomialCompletionGeometricSeriesTruncation p n)

private theorem padicPolynomialCompletionGeometricSeriesToQuotient_compatible
    {m n : ℕ} (hmn : m ≤ n) :
    AdicCompletion.transitionMap (p) ZpPoly hmn ∘ₗ
        padicPolynomialCompletionGeometricSeriesToQuotient p n =
      padicPolynomialCompletionGeometricSeriesToQuotient p m := by
  sorry

private noncomputable abbrev padicPolynomialCompletionGeometricSeries : ZpPolyHat :=
  (AdicCompletion.lift (p) (padicPolynomialCompletionGeometricSeriesToQuotient p)
    fun hle ↦ padicPolynomialCompletionGeometricSeriesToQuotient_compatible p hle) 1

-- Proof sketch: represent the formal series `1 + pX + p^2 X^2 + ⋯` by its compatible system of
-- truncations in the completed target polynomial ring. Its class in the cokernel is nonzero, and
-- multiplying by any power `p^n` shifts the series so that the class remains in `p^n M`.
/-- The class of `1 + pX + p^2 X^2 + ⋯` in the cokernel of the completed substitution map
`X ↦ pX`. -/
noncomputable abbrev padicPolynomialCompletionCokernelGeometricSeries :
    padicPolynomialCompletionCokernel p :=
  (cokernel.π (ModuleCat.ofHom (padicPolynomialCompletionMap p))).hom
    (padicPolynomialCompletionGeometricSeries p)

/-- The geometric-series class in the example cokernel is nonzero. -/
theorem padicPolynomialCompletionCokernelGeometricSeries_ne_zero :
    padicPolynomialCompletionCokernelGeometricSeries p ≠ 0 :=
  sorry

/-- The geometric-series class in the example cokernel lies in every submodule `p^n M`. -/
theorem padicPolynomialCompletionCokernelGeometricSeries_mem_p_pow_smul_top (n : ℕ) :
    padicPolynomialCompletionCokernelGeometricSeries p ∈
      ((p) ^ n) • (⊤ : Submodule Zp (padicPolynomialCompletionCokernel p)) :=
  sorry

-- Proof sketch: the geometric-series class is nonzero and lies in `⋂ n, p^n M`, so the module is
-- not Hausdorff for the `(p)`-adic topology. Since `IsAdicComplete` includes Hausdorffness, the
-- cokernel cannot be `p`-adically complete.
/-- The example cokernel is not `p`-adically complete as a `ℤ_[p]`-module. -/
theorem padicPolynomialCompletionCokernel_not_isAdicComplete :
    ¬ IsAdicComplete (p) (padicPolynomialCompletionCokernel p) :=
  sorry

end
