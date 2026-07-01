import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_10_4
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_1
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_3
import ConvexAnalysis_Rockafellar_1970.Chap07.Text_35_6_4

noncomputable section

universe u v

namespace Bifunction

open scoped Rockafellar

section

variable {𝕜 : Type*}
variable [NontriviallyNormedField 𝕜]
variable [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {U : Type u} {V : Type v}
variable [SeminormedAddCommGroup U] [NormedSpace 𝕜 U]
variable [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 35.8 identifies differentiability of a concave-convex saddle-function at
  a point with uniqueness of its saddle subgradient there.
- `core/canonical`: the theorem surface is stated on the canonical strong-dual bridge owner
  `Bifunction.subdifferentialAtDual`; theorem surfaces use the notation
  `∂ₛ K(u, v)`, with no explicit carrier arguments.
- `bridge/view`: the codomain lift from a finite-valued `K : U → V → 𝕜` to
  `toWithBotTop K : U → V → WithBotTop 𝕜` is the only bridge used for the
  subdifferential owner.

Domain-style sampling used here:

- `Function.differentiableAt_iff_existsUnique_mem_subdifferentialAt` and
  `Function.hasLinearDirectionalDerivativeAt_iff_existsUnique_mem_subdifferentialAt` from
  `Theorem_25_2`;
- `Bifunction.subdifferentialAt` from `Text_35_6_3`
  (with `Text_35_6_4` as the strong-dual bridge);
- `Bifunction.subdifferential1At` and `Bifunction.subdifferential2At` from
  `Text_35_5_1` and `Text_35_5_2`.

Primitive data vs derived API:
- primitive source data: a finite-valued concave-convex saddle-function `K : U → V → 𝕜`;
- primitive owner bridge data: the canonical codomain lift `toWithBotTop K`;
- derived API: product-singleton identification of the lifted saddle subdifferential
  by the canonical
  first and second Fréchet derivatives, and the converse differentiability criterion from
  uniqueness of that owner.
-/

-- Proof sketch: apply the Chapter 25 singleton-subdifferential criterion to the two slices of the
-- finite-valued `K`, then read the saddle subdifferential as the pairing-level product owner
-- specialized to strong duals via `∂ₛ (toWithBotTop K)(u, v)`.
/-- Theorem 35.8 (1): for a concave-convex finite-valued saddle-function `K : U → V → 𝕜`, if
`Function.uncurry K` is differentiable at `(u, v)`, then the saddle subdifferential of its
canonical codomain lift `toWithBotTop K` is the product of
the singleton first and second partial subdifferentials determined by the Fréchet derivatives of
the two slices at `(u, v)`. -/
theorem subdifferentialAt_eq_prod_singleton_fderiv_of_differentiableAt
    {K : U → V → 𝕜} (hK_shape : SaddleFunction.IsConcaveConvex 𝕜 (toWithBotTop K))
    {u : U} {v : V}
    (hdiff : DifferentiableAt 𝕜 (Function.uncurry K) (u, v)) :
    ∂ₛ (toWithBotTop K)(u, v) =
      {fderiv 𝕜 (fun u' ↦ K u' v) u} ×ˢ {fderiv 𝕜 (K u) v} := sorry

variable [FiniteDimensional 𝕜 U] [FiniteDimensional 𝕜 V]

-- Proof sketch: uniqueness of `∂ₛ (toWithBotTop K)(u, v)` means
-- uniqueness of the first and second partial dual subgradients at `(u, v)` for the lifted owner
-- `toWithBotTop K`. Any interior/slice bridge data needed by one-variable Chapter 25 converses are
-- derived internally from the concave-convex hypotheses, and separate differentiability is then
-- upgraded to differentiability on the product.
/-- Theorem 35.8 (2): conversely, if a concave-convex saddle-function has a unique saddle
subgradient at `(u, v)` for the lifted owner `toWithBotTop K`, then `Function.uncurry K` is
differentiable at `(u, v)`. -/
theorem differentiableAt_uncurry_of_existsUnique_mem_subdifferentialAt
    {K : U → V → 𝕜} (hK_shape : SaddleFunction.IsConcaveConvex 𝕜 (toWithBotTop K))
    {u : U} {v : V}
    (hsub : ∃! p, p ∈ ∂ₛ (toWithBotTop K)(u, v)) :
    DifferentiableAt 𝕜 (Function.uncurry K) (u, v) := sorry

-- Proof sketch: combine the forward singleton-product identification with the converse
-- uniqueness-to-differentiability implication to expose the source theorem directly as an iff
-- on the pairing-level owner specialized to strong duals.
/-- Canonical iff form of Theorem 35.8: for a finite-valued concave-convex saddle-function
`K : U → V → 𝕜`, differentiability of `Function.uncurry K` at `(u, v)` is equivalent to
uniqueness of the lifted saddle subgradient owner
`∂ₛ (toWithBotTop K)(u, v)`. -/
theorem differentiableAt_uncurry_iff_existsUnique_mem_subdifferentialAt
    {K : U → V → 𝕜} (hK_shape : SaddleFunction.IsConcaveConvex 𝕜 (toWithBotTop K))
    {u : U} {v : V} :
    DifferentiableAt 𝕜 (Function.uncurry K) (u, v) ↔
      ∃! p, p ∈ ∂ₛ (toWithBotTop K)(u, v) := by
  constructor
  · intro hdiff
    refine ⟨(fderiv 𝕜 (fun u' ↦ K u' v) u, fderiv 𝕜 (K u) v), ?_, ?_⟩
    · have hs :
        ∂ₛ (toWithBotTop K)(u, v) =
          {fderiv 𝕜 (fun u' ↦ K u' v) u} ×ˢ {fderiv 𝕜 (K u) v} :=
        subdifferentialAt_eq_prod_singleton_fderiv_of_differentiableAt
          (K := K) hK_shape hdiff
      rw [hs]
      simp
    · intro p hp
      have hs :
          ∂ₛ (toWithBotTop K)(u, v) =
            {fderiv 𝕜 (fun u' ↦ K u' v) u} ×ˢ {fderiv 𝕜 (K u) v} :=
          subdifferentialAt_eq_prod_singleton_fderiv_of_differentiableAt
            (K := K) hK_shape hdiff
      rw [hs] at hp
      rcases hp with ⟨hp₁, hp₂⟩
      exact Prod.ext (by simpa using hp₁) (by simpa using hp₂)
  · intro hsub
    exact differentiableAt_uncurry_of_existsUnique_mem_subdifferentialAt hK_shape hsub

end

end Bifunction
