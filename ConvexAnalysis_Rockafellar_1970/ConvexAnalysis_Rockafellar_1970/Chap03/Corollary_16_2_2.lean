import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_8_5_1
import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_9_2_1
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Rockafellar

noncomputable section

section

universe u v

variable {ι : Type v} [Fintype ι]
variable {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u}
variable [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]
variable [Module 𝕜 E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E]
variable [HasLinearPairing E E 𝕜] [HasPairingSwap E E 𝕜]
local instance : HasPairing E E (WithBotTop 𝕜) := instHasPairingWithBotTop

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 16.2.2 characterizes nonemptiness of the common relative interior
  `ri (dom f₁) ∩ ··· ∩ ri (dom f_m)` for a finite family of proper convex functions by excluding
  a zero-sum family of dual vectors with one-sided inequalities for the conjugate recession
  functions `fᵢ⋆0⁺`.
- `core/canonical`: the owner abstractions already present in the project are
  `Function.IsConvex`, `Function.IsProper`, `riDom[𝕜](·)`, `f⋆`, `f0⁺`,
  `Function.NoZeroSumAsymmetricRecession`, and the subspace criterion of `Lemma_16_2`.
- `bridge/view`: Rockafellar's vectors `x₁⋆, …, x_m⋆` are encoded as one family
  `xStar : ι → E`; the condition `x₁⋆ + ··· + x_m⋆ = 0` becomes `∑ i, xStar i = 0`, and the
  diagonal-subspace orthogonality condition from `Lemma_16_2` becomes exactly that zero-sum
  equation.

Domain-style sampling used here:
- `submodule_meets_riDom_iff_no_pairingOrthogonal_asymmetric_supportFunction`
  from `Lemma_16_2`;
- `supportFunction_effectiveDomain_eq_recessionFunction_convexConjugate` from `Theorem_13_3`,
  used through the canonical surface `f⋆` and `f⋆0⁺`;
- `riDom[𝕜](·)` from `Definition_4_4`;
- `Function.IsConvex` and `Function.IsProper` for the chapter-owned convexity and properness
  predicates on `WithBotTop 𝕜`-valued functions;
- finite sums over a `Fintype`.

Primitive data vs derived API:
- primitive inputs: the family `f`;
- owner hypotheses: each `f i` is convex and proper in the chapter sense;
- derived output: the equivalence between common relative-interior nonemptiness and the canonical
  family-level owner condition `Function.NoZeroSumAsymmetricRecession` on the conjugate family.

Layer target: `source-facing`, with the public surface on the finite-dimensional topological
pairing-space layer over `𝕜` rather than the inner-product-only model, and without introducing a
product-space wrapper into the public API.
-/

-- Proof sketch: apply Lemma 16.2 to the sum function on the product space `E^ι` and to the
-- diagonal subspace of constant families. The relative interior of the effective domain
-- of that sum is the product of the relative interiors `riDom[𝕜](f i)`, so meeting the diagonal
-- is exactly nonemptiness of `⋂ i, riDom[𝕜](f i)`. The orthogonal
-- complement of the diagonal consists of the families `xStar` with `∑ i, xStar i = 0`, and the
-- recession function of the conjugate of the product-space sum splits as the sum of the
-- individual functions `((f i)⋆)₀⁺`.
/-- Corollary 16.2.2: for a finite family of proper convex functions on a finite-dimensional
topological pairing space over `𝕜`, the common relative interior
`ri (dom f₁) ∩ ··· ∩ ri (dom f_m)` is nonempty if and only if the conjugate family satisfies the
canonical recession-kernel owner
`Function.NoZeroSumAsymmetricRecession`. -/
theorem common_riDom_nonempty_iff_no_zero_sum_asymmetric_conjugate_recession
    (f : ι → E → WithBotTop 𝕜)
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_proper : ∀ i, (f i).IsProper) :
    (⋂ i, riDom[𝕜](f i)).Nonempty ↔
      Function.NoZeroSumAsymmetricRecession (fun i ↦ ((f i)⋆ : E → WithBotTop 𝕜)) := by
  sorry

end
