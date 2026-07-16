import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_9
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_38_2_2

noncomputable section

universe u v w

namespace Bifunction

/-!
Source/core/bridge triage for this item.

- `source-facing`: Proposition 38.2.3 says that if `F` is the convex indicator bifunction of a
  linear transformation `A`, then the positive scalar multiple `F λ` is the convex indicator
  bifunction of the scaled linear transformation `(lam : 𝕜) • A`.
- `core/canonical`: the chapter already owns the two relevant constructions as
  `Bifunction.rightScalarMul` from Definition 38.2.2 and the singleton-graph owner
  `Bifunction.graphIndicator` from Definition 6.29.9.
- `bridge/view`: the proposition is the source-facing slice identity obtained by applying
  `rightScalarMul` to `graphIndicator 𝕜 A`; the slice formula of Definition 6.29.9 is now derived
  API rather than the public owner surface.

Primary mathematical domain:
- convex-analysis bifunctions built from singleton indicators of linear maps and their positive
  scalar rescaling.

Domain-style sampling used here:
- `Bifunction.rightScalarMul` and `Bifunction.rightScalarMul_apply`
  from `Chap08.Definition_38_2_2`;
- `Bifunction.graphIndicator` and `Bifunction.graphIndicator_slice`
  from `Chap06.Definition_6_29_9`;
- the scalar action on linear maps `U →ₗ[𝕜] X` from mathlib.

Primitive data vs derived API:
- primitive source data: a linear map `A : U →ₗ[𝕜] X` and a positive scalar `lam`;
- primitive owners reused directly: `rightScalarMul` and `graphIndicator`;
- derived API: the displayed slice identity for the scaled graph-indicator bifunction.

Layer target: `source-facing`, expressed directly in the existing owner language.
-/

section

variable {𝕜 : Type w} {U : Type u} {X : Type v}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]

-- Proof sketch: evaluate both bifunctions pointwise. `rightScalarMul_apply` rewrites the left-hand
-- side as `(lam : 𝕜) * graphIndicator 𝕜 A u ((lam : 𝕜)⁻¹ • x)`, and `graphIndicator_cases`
-- reduces each side to the `0`/`⊤` singleton-indicator alternatives. The two branches are
-- equivalent because multiplying by `lam` and by `lam⁻¹` are inverse scalar actions.
/-- Proposition 38.2.3: the right scalar multiple of the singleton-graph indicator bifunction of a
linear map `A` is the singleton-graph indicator bifunction of the scaled linear map
`(lam : 𝕜) • A`. -/
theorem rightScalarMul_graphIndicator
    (A : U →ₗ[𝕜] X) (lam : Set.Ioi (0 : 𝕜)) :
    rightScalarMul (graphIndicator 𝕜 A) lam =
      graphIndicator 𝕜 ((lam : 𝕜) • A) := by
  ext u x
  by_cases hx : x = (lam : 𝕜) • A u
  · subst hx
    simp [rightScalarMul_apply, graphIndicator_cases, inv_smul_smul₀, lam.2.ne']
  · have hne : ((lam : 𝕜)⁻¹ • x) ≠ A u := by
      intro h
      apply hx
      calc
        x = (lam : 𝕜) • ((lam : 𝕜)⁻¹ • x) := by
          simpa using (smul_inv_smul₀ lam.2.ne' x).symm
        _ = (lam : 𝕜) • A u := by rw [h]
    simpa [rightScalarMul_apply, graphIndicator_cases, hx, hne] using
      (WithBotTop.coe_mul_top_of_pos lam.2 : (lam : WithBotTop 𝕜) * ⊤ = (⊤ : WithBotTop 𝕜))

/-- Slice form of Proposition 38.2.3. -/
theorem rightScalarMul_graphIndicator_apply
    (A : U →ₗ[𝕜] X) (lam : Set.Ioi (0 : 𝕜)) (u : U) :
    rightScalarMul (graphIndicator 𝕜 A) lam u =
      graphIndicator 𝕜 ((lam : 𝕜) • A) u := by
  simpa using congrFun (rightScalarMul_graphIndicator A lam) u

end

end Bifunction
