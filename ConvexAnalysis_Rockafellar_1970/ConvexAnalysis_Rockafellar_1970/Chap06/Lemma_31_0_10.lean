import ConvexAnalysis_Rockafellar_1970.Chap06.Lemma_31_0_6

noncomputable section

universe u

namespace Bifunction

/-!
Source/core/bridge triage for this item.

- `source-facing`: Lemma 31.0.10 introduces the translated-value function
  `p(u) = inf_x (f x - g (x + u))` and asserts its convexity.
- `core/canonical`: the Chapter 6 owner for this value function is already
  `Bifunction.perturbationFunction`, implemented as the Chapter 1 owner
  `Function.partialInfimum`; the corresponding bifunction is the identity-map specialization of
  `Bifunction.fenchelPerturbation`.
- `bridge/view`: the source formula `p(u) = inf_x (f x - g (x + u))` is exactly the evaluation
  formula for `perturbationFunction (fenchelPerturbation (LinearMap.id : E →ₗ[𝕜] E) f g)`.

Domain-style sampling used here:
- `Bifunction.fenchelPerturbation`;
- `Bifunction.perturbationFunction`;
- `Function.partialInfimum`;
- `Function.IsConvex.partialInfimum`;
- `Function.IsConvex.infimal_convolution`.

Primitive data vs derived API:
- primitive source data: the functions `f` and `g`;
- primitive owner object: the perturbation function of the identity Fenchel perturbation;
- derived API: the source infimum formula and the convexity theorem.

Layer target: `source-facing`, but expressed directly through the existing owner
`perturbationFunction` instead of a parallel local definition of `p`.
-/

section

variable {𝕜 : Type*} [Semiring 𝕜]
variable {E : Type u} [AddCommMonoid E] [Module 𝕜 E]
variable {α : Type*} [Add α] [Neg α] [InfSet (WithTopBot α)]
variable (f g : E → WithTopBot α)

local notation "F" => fenchelPerturbation LinearMap.id f g
local notation "p" => perturbationFunction F

/-- Lemma 31.0.10, source formula: for any additive extended codomain layer with infima, the
perturbation function of the identity-map Fenchel perturbation is exactly
`u ↦ inf_x (f x - g (x + u))`. -/
@[simp] theorem perturbationFunction_fenchelPerturbation_id_apply
    (u : E) : p u = ⨅ x : E, f x - g (x + u) := by
  simpa [fenchelPerturbation, sub_eq_add_neg] using perturbationFunction_apply F u

end

section

variable {𝕜 : Type*} [ConditionallyCompleteLinearOrder 𝕜] [Ring 𝕜]
variable [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜]
variable {E : Type u} [AddCommMonoid E] [Module 𝕜 E]
variable {f g : E → WithTopBot 𝕜}

local notation "F" => fenchelPerturbation LinearMap.id f g
local notation "p" => perturbationFunction F

/-- Primitive convexity owner form for Lemma 31.0.10: on the `WithTopBot` codomain layer,
convexity of `f`, concavity of `g`, and the pointwise non-`⊥` guards required by the additive
convexity bridge imply convexity of the perturbation-value function
`u ↦ inf_x (f x - g (x + u))`. -/
theorem perturbationFunction_fenchelPerturbation_id_isConvex_of_bot_lt
    (hf : f.IsConvex 𝕜) (hf_bot : ∀ x : E, ⊥ < f x)
    (hg_concave : g.IsConcave 𝕜) (hg_neg_bot : ∀ u : E, ⊥ < (-g) u) :
    p.IsConvex 𝕜 := by
  have h_uncurry_convex :
      (Function.uncurry F).IsConvex 𝕜 :=
    uncurry_fenchelPerturbation_isConvex_of_bot_lt
      (A := (LinearMap.id : E →ₗ[𝕜] E)) hf hf_bot hg_concave hg_neg_bot
  simpa [perturbationFunction] using
    h_uncurry_convex.partialInfimum_uncurry

/-- Lemma 31.0.10 source-facing corollary: properness assumptions imply the primitive non-`⊥`
guards, hence convexity of the perturbation-value function
`u ↦ inf_x (f x - g (x + u))`. -/
theorem perturbationFunction_fenchelPerturbation_id_isConvex
    (hf : f.IsConvex 𝕜) (hg_concave : g.IsConcave 𝕜)
    (hf_proper : f.IsProper) (hg_proper : g.IsProperConcave) :
    p.IsConvex 𝕜 := by
  refine perturbationFunction_fenchelPerturbation_id_isConvex_of_bot_lt
      (f := f) (g := g) hf hf_proper.bot_lt hg_concave ?_
  intro u
  exact hg_proper.neg_isProper.bot_lt u

end

end Bifunction
