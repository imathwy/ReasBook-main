import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_4
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_16_4_1
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_12_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Rockafellar

noncomputable section

universe u

section

variable {ι : Type*} [Fintype ι]
variable {E : Type u} {𝕜 : Type*}
variable [ConditionallyCompleteLinearOrder 𝕜] [Field 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)]
variable [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜]
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
  [FiniteDimensional 𝕜 E] [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 16.4.2 states the dual formula
  `(cl f₁ + ··· + cl f_m)^* = cl (f₁^* □ ··· □ f_m^*)` for a finite family of proper convex
  functions.
- `core/canonical`: the project owners already present are `lowerSemicontinuousHull` for the
  closure `cl`, `convexConjugate` for `f*`, `finiteInfimalConvolution` for `□`, and the chapter
  predicates `Function.IsConvex` and `Function.IsProper`.
- `bridge/view`: the textbook sum of closures is rendered directly by the pointwise finite sum
  `∑ i, cl(f i)`, so no surrogate wrapper is introduced.

Domain-style sampling used here:
- `convexConjugate_finiteInfimalConvolution_eq_sum` from Theorem 16.4.1;
- `Function.IsConvex.convexConjugate_isProper_iff` from Theorem 12.2;
- `Function.IsConvex.biconjugate_eq_lowerSemicontinuousHull` from Theorem 12.2;
- `Function.isConvex_finiteInfimalConvolution` from Theorem 5.4.

Primitive data vs derived API:
- primitive input: a finite family `f : ι → E → WithBotTop 𝕜`;
- primitive owner-side hypothesis for the core identity: pointwise exclusion of `⊥` for each
  conjugate summand `f i⋆`, stated directly as `((f i)⋆) x ≠ ⊥`;
- source-facing companion hypothesis: properness of each `f i`, used only to recover the previous
  primitive condition through Theorem 12.2;
- derived API: the duality identity itself.

Layer target: `source-facing`. The source states the theorem on `R^n` for a finite nonempty
family, but the owner declarations it uses already live on arbitrary finite-dimensional scalar
field spaces equipped with a continuous linear self-pairing and arbitrary finite index types, so
this file keeps the theorem on that canonical ambient owner layer.
-/

-- Proof sketch: apply Theorem 16.4.1 to the conjugate family `fun i ↦ convexConjugate (f i)`.
-- Theorem 12.2 identifies the biconjugates `f i⋆⋆` with `lowerSemicontinuousHull (f i)`. This
-- gives that the conjugate of
-- `finiteInfimalConvolution (fun i ↦ convexConjugate (f i))` is the pointwise sum of the closures
-- `cl f_i`. Applying Theorem 12.2 once more to that convex finite infimal convolution identifies
-- its biconjugate with the lower semicontinuous hull on the right-hand side.
/-- Theorem 16.4.2 at the primitive owner layer: for a finite family of convex functions on a
finite-dimensional scalar-field space equipped with a continuous linear self-pairing, if each
conjugate summand is never `⊥`, then the conjugate of the pointwise sum of the closures
`cl f_i` is the closure of the finite infimal convolution of the individual conjugates. -/
theorem
    convexConjugate_sum_cl_eq_cl_finiteInfimalConvolution
    (f : ι → E → WithBotTop 𝕜)
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_conj_ne_bot : ∀ i x, ((f i)⋆ : E → WithBotTop 𝕜) x ≠ ⊥) :
    ((∑ i, cl(f i))⋆ : E → WithBotTop 𝕜) =
      cl(finiteInfimalConvolution (fun i ↦ (f i)⋆)) := by
  have hsum_cl :
      (∑ i, cl(f i)) = (∑ i, ((f i)⋆⋆ : E → WithBotTop 𝕜)) := by
    classical
    refine Finset.sum_congr rfl ?_
    intro i _
    simpa using ((hf_convex i).biconjugate_eq_lowerSemicontinuousHull).symm
  have hsum_conj :
      (∑ i, ((f i)⋆⋆ : E → WithBotTop 𝕜)) =
        ((finiteInfimalConvolution (fun i ↦ ((f i)⋆ : E → WithBotTop 𝕜)))⋆ :
          E → WithBotTop 𝕜) := by
    simpa using
      (convexConjugate_finiteInfimalConvolution_eq_sum
        (f := fun i ↦ ((f i)⋆ : E → WithBotTop 𝕜))
        hf_conj_ne_bot).symm
  have hconvex_finiteInfimalConvolution :
      (finiteInfimalConvolution (fun i ↦ ((f i)⋆ : E → WithBotTop 𝕜))).IsConvex 𝕜 := by
    refine Function.isConvex_finiteInfimalConvolution
      (f := fun i ↦ ((f i)⋆ : E → WithBotTop 𝕜)) ?_
    intro i
    simpa using (Function.isConvex_convexConjugate (f := f i))
  calc
    ((∑ i, cl(f i))⋆ : E → WithBotTop 𝕜) =
        ((((finiteInfimalConvolution (fun i ↦ ((f i)⋆ : E → WithBotTop 𝕜)))⋆)⋆) :
          E → WithBotTop 𝕜) := by
      rw [hsum_cl, hsum_conj]
    _ = cl(finiteInfimalConvolution (fun i ↦ ((f i)⋆ : E → WithBotTop 𝕜))) := by
      simpa using hconvex_finiteInfimalConvolution.biconjugate_eq_lowerSemicontinuousHull

/-- Owner-bridge companion for Theorem 16.4.2: the same identity under the conjugate-side properness
owner hypothesis. This is a direct reformulation of the primitive `⊥`-exclusion hypothesis via
`Function.IsProper.ne_bot`. -/
theorem
    convexConjugate_sum_cl_eq_cl_finiteInfimalConvolution_of_conjugate_proper
    (f : ι → E → WithBotTop 𝕜)
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_conj_proper : ∀ i, ((f i)⋆ : E → WithBotTop 𝕜).IsProper) :
    ((∑ i, cl(f i))⋆ : E → WithBotTop 𝕜) =
      cl(finiteInfimalConvolution (fun i ↦ (f i)⋆)) := by
  have hconj_ne_bot : ∀ i x, ((f i)⋆ : E → WithBotTop 𝕜) x ≠ ⊥ := by
    intro i x
    exact (hf_conj_proper i).ne_bot x
  simpa using
    convexConjugate_sum_cl_eq_cl_finiteInfimalConvolution
      (f := f) hf_convex hconj_ne_bot

/-- Properness-form companion of Theorem 16.4.2. This adds no new mathematics: it only recovers
the primitive conjugate-side `⊥`-exclusion hypothesis from
`Function.IsConvex.convexConjugate_isProper_iff`. -/
theorem
    convexConjugate_sum_cl_eq_cl_finiteInfimalConvolution_of_proper_convex
    (f : ι → E → WithBotTop 𝕜)
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_proper : ∀ i, (f i).IsProper) :
    ((∑ i, cl(f i))⋆ : E → WithBotTop 𝕜) =
      cl(finiteInfimalConvolution (fun i ↦ (f i)⋆)) := by
  have hconj_proper : ∀ i, ((f i)⋆ : E → WithBotTop 𝕜).IsProper := by
    intro i
    exact ((hf_convex i).convexConjugate_isProper_iff).2 (hf_proper i)
  simpa using
    convexConjugate_sum_cl_eq_cl_finiteInfimalConvolution_of_conjugate_proper
      (f := f) hf_convex hconj_proper

end
