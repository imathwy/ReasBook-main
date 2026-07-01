import ConvexAnalysis_Rockafellar_1970.Chap05.Lemma_23_0_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section

open Filter
open scoped Topology

variable {𝕜 : Type v}
variable [Field 𝕜] [LinearOrder 𝕜]
variable [TopologicalSpace 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]

namespace Function

/-- `HasBilateralDirectionalDerivativeAt f x d L` says that the directional difference quotient of
`f` at `x` along `d` converges to `L` on the punctured neighborhood of `0`. -/
def HasBilateralDirectionalDerivativeAt
    (f : E → WithTopBot 𝕜) (x d : E) (L : WithTopBot 𝕜) : Prop :=
  Tendsto (directionalDifferenceQuotientAt f x d) (𝓝[≠] (0 : 𝕜)) (𝓝 L)

end Function

end

section

open Filter
open scoped Topology

variable {𝕜 : Type v}
variable [Field 𝕜] [LinearOrder 𝕜]
variable {E : Type u} [AddCommGroup E] [DistribSMul 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Lemma 23.0.3 states the left/right symmetry of directional difference
  quotients under the direction change `d ↦ -d`, and reformulates existence of a bilateral
  directional derivative through the two right-hand limits in directions `d` and `-d`.
- `core/canonical`: the only one-sided owner remains
  `Function.HasDirectionalDerivativeAt` from Lemma 23.0.1; the only new owner introduced here is
  the punctured-neighborhood bilateral companion `Function.HasBilateralDirectionalDerivativeAt`.
- `bridge/view`: the source's left directional derivative along `d` is expressed directly as the
  left-limit theorem for `Function.directionalDifferenceQuotientAt`, proved equivalent to the
  reflected right-hand owner along `-d`; no parallel left-sided owner is introduced.

Domain-style sampling used here:
- `Function.directionalDifferenceQuotientAt` from
  `Items/Chap05/Lemma_23_0_1.lean`;
- `Function.HasDirectionalDerivativeAt` from `Items/Chap05/Lemma_23_0_1.lean`,
  which is the chapter's one-sided directional-derivative owner;
- `Function.hasDirectionalDerivativeAt_supportFunction_subdifferentialAt` from
  `Items/Chap05/Lemma_23_0_1.lean`,
  which fixes the right-hand `Tendsto` owner for directional difference quotients in this chapter;
- `Function.tendsto_directionalDifferenceQuotientAt_toWithBotTop_bilateral_of_hasGradientAt` from
  `Items/Chap05/Lemma_23_0_4.lean`,
  which uses the punctured-neighborhood owner shape `Tendsto ... (𝓝[≠] (0 : 𝕜)) ...`;
- mathlib's filter-level owner `Filter.Tendsto` together with
  `punctured_nhds_eq_nhdsWithin_sup_nhdsWithin`.

Primitive data vs derived API:
- primitive data: the function `f`, the base point `x`, and the direction `d`;
- primitive owners reused from upstream: `Function.directionalDifferenceQuotientAt` and
  `Function.HasDirectionalDerivativeAt`;
- derived API: the reflected left-directional view, the bilateral/right owner equivalence, and the
  existential bilateral companion.

Layer target: `source-facing`.

Ambient-assumption minimization:
- the punctured-neighborhood owner `Function.HasBilateralDirectionalDerivativeAt` itself only uses
  the directional-difference quotient owner and is therefore stated at the primitive
  `AddCommMonoid`/`SMul` layer;
- the symmetry theorems below use direction negation `d ↦ -d`, so they are stated at
  `AddCommGroup`/`DistribSMul`, still far below the stronger finite-dimensional inner-product-space
  layer.
- this bridge file still presents the bilateral/left-right filter decomposition over `𝕜`
  (`𝓝[>] (0 : 𝕜)`, `𝓝[<] (0 : 𝕜)`, `𝓝[≠] (0 : 𝕜)`), and adds no stronger ambient structure than
  needed for that directional-negation comparison: the scalar side uses order-topology control on
  left/right neighborhoods around `0`, while the codomain side only asks for continuity of `Neg`
  to express reflected limits.
-/

namespace Function

/-- Changing the direction from `d` to `-d` turns the directional difference quotient at time `t`
into the negative of the quotient in direction `d` at time `-t`. -/
theorem directionalDifferenceQuotientAt_neg_direction
    (f : E → WithTopBot 𝕜) (x d : E) (t : 𝕜) :
    directionalDifferenceQuotientAt f x (-d) t = -directionalDifferenceQuotientAt f x d (-t) := by
  sorry

variable [TopologicalSpace 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)]

-- Proof sketch: substitute `t = -s` in the left quotient. The numerator becomes the same
-- difference quotient evaluated at the reflected direction `-d`, and the denominator changes sign,
-- so the limit value is negated. Bilateral existence is then exactly the conjunction of the right
-- limit in direction `d` with the reflected right limit in direction `-d`.
/-- Lemma 23.0.3, left-limit form: the source left directional derivative along `d` equals `L`
exactly when the chapter's right directional-derivative owner along `-d` equals `-L`. -/
theorem tendsto_directionalDifferenceQuotientAt_left_iff_hasDirectionalDerivativeAt_neg
    [OrderTopology 𝕜] [ContinuousNeg (WithTopBot 𝕜)]
    {f : E → WithTopBot 𝕜} {x d : E} {L : WithTopBot 𝕜} :
    Tendsto (directionalDifferenceQuotientAt f x d) (𝓝[<] (0 : 𝕜)) (𝓝 L) ↔
      HasDirectionalDerivativeAt f x (-d) (-L) := by
  sorry

/-- Lemma 23.0.3, bilateral owner form: bilateral convergence along `d` is equivalent to the two
right directional-derivative owners in directions `d` and `-d`, with reflected limit `-L`. -/
theorem hasBilateralDirectionalDerivativeAt_iff_hasDirectionalDerivativeAt_and_neg
    [OrderTopology 𝕜] [ContinuousNeg (WithTopBot 𝕜)]
    {f : E → WithTopBot 𝕜} {x d : E} {L : WithTopBot 𝕜} :
    HasBilateralDirectionalDerivativeAt f x d L ↔
      HasDirectionalDerivativeAt f x d L ∧
        HasDirectionalDerivativeAt f x (-d) (-L) := by
  rw [HasBilateralDirectionalDerivativeAt, punctured_nhds_eq_nhdsWithin_sup_nhdsWithin, tendsto_sup]
  constructor
  · rintro ⟨hLeft, hRight⟩
    exact ⟨by simpa [HasDirectionalDerivativeAt] using hRight,
      tendsto_directionalDifferenceQuotientAt_left_iff_hasDirectionalDerivativeAt_neg.1 hLeft⟩
  · rintro ⟨hRight, hLeft⟩
    exact ⟨tendsto_directionalDifferenceQuotientAt_left_iff_hasDirectionalDerivativeAt_neg.2 hLeft,
      by simpa [HasDirectionalDerivativeAt] using hRight⟩

/-- Lemma 23.0.3, existential owner companion: a bilateral directional derivative along `d` exists
exactly when the right directional derivatives in directions `d` and `-d` exist with opposite
values. -/
theorem exists_hasBilateralDirectionalDerivativeAt_iff_exists_hasDirectionalDerivativeAt_and_neg
    [OrderTopology 𝕜] [ContinuousNeg (WithTopBot 𝕜)]
    {f : E → WithTopBot 𝕜} {x d : E} :
    (∃ L : WithTopBot 𝕜, HasBilateralDirectionalDerivativeAt f x d L) ↔
      ∃ L : WithTopBot 𝕜,
        HasDirectionalDerivativeAt f x d L ∧
          HasDirectionalDerivativeAt f x (-d) (-L) := by
  constructor
  · rintro ⟨L, hL⟩
    exact ⟨L, (hasBilateralDirectionalDerivativeAt_iff_hasDirectionalDerivativeAt_and_neg.1 hL)⟩
  · rintro ⟨L, hL⟩
    exact ⟨L, (hasBilateralDirectionalDerivativeAt_iff_hasDirectionalDerivativeAt_and_neg.2 hL)⟩

end Function

end
