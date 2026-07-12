import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_13_3
import ConvexAnalysis_Rockafellar_1970.Chap03.Lemma_16_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Rockafellar

section

universe u v

variable {E : Type u} {F : Type v}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 16.2.1 characterizes when the image subspace `A(E)` meets the
  relative interior of the effective domain of a proper convex function `g`.
- `core/canonical`: the owner abstractions already present in the project are
  `riDom(·)`, `supportFunction`, `convexConjugate`, `Function.recessionFunction`, and
  the
  subspace criterion
  `submodule_meets_riDom_iff_no_pairingOrthogonal_asymmetric_supportFunction`.
- `bridge/view`: the source equation `A^* y⋆ = 0` is the canonical `LinearMap.adjoint` rendering
  of orthogonality to the range subspace `LinearMap.range A`, while Theorem 13.3 supplies the
  companion support-function rendering of `g⋆0⁺`.

Domain-style sampling used here:
- `submodule_meets_riDom_iff_no_pairingOrthogonal_asymmetric_supportFunction`
  from `Lemma_16_2`;
- `convexConjugate` from `Defn_12_2`;
- `recessionFunction` from `Corollary_8_5_1`;
- `LinearMap.orthogonal_range` from the finite-dimensional adjoint API;
- `riDom(·)` for Rockafellar's `ri (dom ·)`.

Primitive data vs derived API:
- primitive inputs: a linear map `A : E →ₗ[𝕜] F` and a function `g : F → WithBotTop 𝕜`;
- owner hypotheses: `g.IsConvex 𝕜` and `g.IsProper`;
- derived output: the range-relative-interior criterion, first at the pairing-orthogonal owner
  layer and then via the adjoint equation `A.adjoint y⋆ = 0`.

Layer target: owner-first at pairing orthogonality, with an inner-product bridge corollary.
-/

/-- Corollary 16.2.1 at the canonical pairing-owner layer: for a linear map `A` and a proper
convex `g`, the image range meets `ri (dom g)` iff no range-annihilator vector has the asymmetric
recession-sign pattern. -/
theorem exists_image_mem_riDom_iff_no_range_pairingOrthogonal_asymmetric_recession
    {𝕜 : Type*}
    [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsOrderedRing 𝕜]
    [TopologicalSpace 𝕜] [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommMonoid E] [Module 𝕜 E]
    [TopologicalSpace F] [AddCommGroup F] [IsTopologicalAddGroup F]
    [Module 𝕜 F] [ContinuousSMul 𝕜 F] [FiniteDimensional 𝕜 F]
    [HasLinearPairing F F 𝕜] [HasPairingSwap F F 𝕜]
    (A : E →ₗ[𝕜] F) (g : F → WithBotTop 𝕜)
    (hg_convex : g.IsConvex 𝕜) (hg_proper : g.IsProper) :
    (∃ x : E, A x ∈ riDom[𝕜](g)) ↔
      ¬ ∃ yStar : F,
        yStar ∈ A.rangeᗮₚ ∧
          (g⋆)₀⁺ yStar ≤ 0 ∧
            (0 : WithBotTop 𝕜) < (g⋆)₀⁺ (-yStar) := by
  have hrange :=
    submodule_meets_riDom_iff_no_pairingOrthogonal_asymmetric_supportFunction
      (𝕜 := 𝕜) (Y := F) (L := A.range) (f := g)
      hg_convex.convex_dom hg_proper.nonempty_dom
  simpa [LinearMap.mem_range, Set.Nonempty,
    supportFunction_effectiveDomain_eq_recessionFunction_convexConjugate
      (f := g) hg_convex hg_proper]
    using hrange

section

open scoped RealInnerProductSpace

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

-- Proof sketch: apply the pairing-owner theorem above, then rewrite membership in
-- `(LinearMap.range A)ᗮₚ` as `A.adjoint yStar = 0` by identifying `ᗮₚ` with `ᗮ` and using
-- `LinearMap.orthogonal_range`.
/-- Corollary 16.2.1 (adjoint bridge): for a linear map `A : R^n → R^m` and a proper convex
function `g` on `R^m`, there is no vector `y⋆` with `A^* y⋆ = 0`, `(g⋆0⁺)(y⋆) ≤ 0`, and
`(g⋆0⁺)(-y⋆) > 0` iff `Ax ∈ ri (dom g)` for some `x`. -/
theorem exists_image_mem_intrinsicInterior_effectiveDomain_iff_no_adjoint_asymmetric_recession
    (A : E →ₗ[ℝ] F) (g : F → WithBotTop ℝ)
    (hg_convex : g.IsConvex ℝ) (hg_proper : g.IsProper) :
    (∃ x : E, A x ∈ riDom[ℝ](g)) ↔
      ¬ ∃ yStar : F,
        A.adjoint yStar = 0 ∧
          (g⋆)₀⁺ yStar ≤ 0 ∧
            (0 : WithBotTop ℝ) < (g⋆)₀⁺ (-yStar) := by
  have hrange :=
    exists_image_mem_riDom_iff_no_range_pairingOrthogonal_asymmetric_recession
      (A := A) (g := g) hg_convex hg_proper
  have hmem :
      ∀ yStar : F, yStar ∈ A.rangeᗮₚ ↔ A.adjoint yStar = 0 := by
    intro yStar
    have hpairEq : A.rangeᗮₚ = (A.rangeᗮ : Submodule ℝ F) :=
      Submodule.pairingOrthogonal_eq_orthogonal_real (K := A.range)
    constructor
    · intro hyPair
      have hyOrth : yStar ∈ A.rangeᗮ := hpairEq ▸ hyPair
      have hyKer : yStar ∈ A.adjoint.ker := (LinearMap.orthogonal_range (A := A)) ▸ hyOrth
      exact hyKer
    · intro hyAdj
      have hyKer : yStar ∈ A.adjoint.ker := hyAdj
      have hyOrth : yStar ∈ A.rangeᗮ := (LinearMap.orthogonal_range (A := A)).symm ▸ hyKer
      exact hpairEq.symm ▸ hyOrth
  constructor
  · intro hx
    have hnoPair : ¬ ∃ yStar : F,
        yStar ∈ A.rangeᗮₚ ∧
          (g⋆)₀⁺ yStar ≤ 0 ∧
            (0 : WithBotTop ℝ) < (g⋆)₀⁺ (-yStar) := (hrange.mp hx)
    intro hAdj
    apply hnoPair
    rcases hAdj with ⟨yStar, hyAdj, hle, hlt⟩
    exact ⟨yStar, (hmem yStar).2 hyAdj, hle, hlt⟩
  · intro hx
    have hnoPair : ¬ ∃ yStar : F,
        yStar ∈ A.rangeᗮₚ ∧
          (g⋆)₀⁺ yStar ≤ 0 ∧
            (0 : WithBotTop ℝ) < (g⋆)₀⁺ (-yStar) := by
      intro hPair
      apply hx
      rcases hPair with ⟨yStar, hyPair, hle, hlt⟩
      exact ⟨yStar, (hmem yStar).1 hyPair, hle, hlt⟩
    exact hrange.mpr hnoPair

end

end
