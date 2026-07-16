import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_2
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_3
import ConvexAnalysis_Rockafellar_1970.Chap07.Theorem_34_2
import ConvexAnalysis_Rockafellar_1970.Chap07.Text_34_2_5

noncomputable section

universe u v v'

open scoped Rockafellar

namespace SaddleFunction

section

variable {𝕜 : Type*} {U : Type u} {X : Type v} {XStar : Type v'}
variable [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [OrderTopology 𝕜]
variable [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
variable [NormedAddCommGroup U] [NormedSpace 𝕜 U] [FiniteDimensional 𝕜 U]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X] [FiniteDimensional 𝕜 X]
variable [TopologicalSpace XStar] [AddCommMonoid XStar] [SMul 𝕜 XStar]
variable [HasPairing U U 𝕜] [HasPairing X XStar 𝕜]

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 34.2.3 says that the only improper closed concave-convex
  saddle-functions are the constant functions `+∞` and `-∞`, and that these two closed
  saddle-functions are not equivalent.
- `core/canonical`: the owner abstraction behind the corollary is the Chapter 34 generator class
  `Ω(F)` for a closed convex bifunction `F`, together with the saddle owners
  `SaddleFunction.IsConcaveConvex`, `SaddleFunction.IsClosed`, `SaddleFunction.IsProper`, and
  the equivalence owner `∼`.
- `bridge/view`: this file keeps only the source-facing corollary statements on that owner
  layer. The main theorem stays on the scalar-parameterized finite-dimensional primal context
  used by the Chapter 34 generator theorem and the Chapter 2/34 improperness dichotomy, while
  keeping the second coordinate on the intrinsic dual-pairing layer instead of a self-dual model.

Domain-style sampling used here:
- `Bifunction.existsUnique_closedConvex_generator` from `Theorem_34_2`;
- `Bifunction.IsClosedConvex.eq_bot_or_eq_top_of_not_uncurry_isProper` from `Text_34_2_5`;
- `SaddleFunction.IsConcaveConvex`, `SaddleFunction.IsClosed`, and `SaddleFunction.IsProper`
  from the Chapter 34 owner layer.

Primitive data vs derived API:
- primitive source data: the saddle-function `K : U → XStar → WithTopBot 𝕜`;
- primitive owner hypotheses on the source-facing side: `IsConcaveConvex 𝕜 K`, `IsClosed K`,
  `¬ IsProper K`;
- derived API: the endpoint conclusion `K = ⊥ ∨ K = ⊤`, obtained through the canonical
  Chapter 34 generator owner `Ω(F)` rather than by a parallel local wrapper.

Layer target: `source-facing` corollary statements in the Chapter 34 finite-dimensional-primal,
dual-pairing setting at the canonical scalar-parameterized codomain layer `WithTopBot 𝕜`.
-/

/-- Corollary 34.2.3: an improper closed concave-convex saddle-function is one of the two
constant endpoint functions. This rigidity statement is kept in the finite-dimensional
primal dual-pairing context used by the Chapter 34 generator theorem and the Chapter 2/34
improperness
dichotomy at codomain layer `WithTopBot 𝕜`; the broader bare `WithTopBot α` owner layer is too
weak. -/
theorem eq_bot_or_eq_top_of_isConcaveConvex_of_isClosed_of_not_isProper
    {K : U → XStar → WithTopBot 𝕜}
    (hK_shape : IsConcaveConvex 𝕜 K)
    (hK_closed : IsClosed K)
    (hK_improper : ¬ IsProper K) :
    K = ⊥ ∨ K = ⊤ := by
  sorry

end

section

variable {α : Type*}
variable {U : Type u} {X : Type v}
variable [ConditionallyCompleteLattice α] [TopologicalSpace α]
variable [Neg α] [NoBotOrder α]
variable [TopologicalSpace U] [TopologicalSpace X] [Nonempty U] [Nonempty X]

/-- Corollary 34.2.3 companion clause: on a nonempty product, the constant functions `-∞` and
`+∞` are not equivalent. -/
theorem bot_not_equivalent_top :
    ¬ ((⊥ : U → X → WithTopBot α) ∼ (⊤ : U → X → WithTopBot α)) := by
  intro h
  have hEqv :=
    (Bifunction.equivalent_iff
      (⊥ : U → X → WithTopBot α)
      (⊤ : U → X → WithTopBot α)).1 h
  rcases hEqv with
    ⟨_, hcl₂⟩
  have hbot : cl₂ (⊥ : U → X → WithTopBot α) = (⊥ : U → X → WithTopBot α) := by
    ext u x
    exact le_antisymm
      (lowerSemicontinuousHull_le_of_noBot (fun _ : X ↦ (⊥ : WithTopBot α)) x)
      bot_le
  have htop : cl₂ (⊤ : U → X → WithTopBot α) = (⊤ : U → X → WithTopBot α) := by
    ext u x
    simp [Bifunction.closure2_apply, lowerSemicontinuousHull, Function.verticalInfimum,
      Function.verticalHeights, Function.verticalSection, epi]
  have hcl₂_ne :
      cl₂ (⊥ : U → X → WithTopBot α) ≠ cl₂ (⊤ : U → X → WithTopBot α) := by
    simp [hbot, htop]
  exact hcl₂_ne hcl₂

end

end SaddleFunction
