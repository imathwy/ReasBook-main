import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_4_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

section

variable {E : Type u} {ι : Type v} {𝕜 : Type w}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [DenselyOrdered 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]

/-!
Source/core/bridge triage for this item.

- Primary domain: finite infimal convolution of extended-real-valued convex functions.
- `source-facing`: Theorem 5.4 states that the infimum of `∑ i, f i (x i)` over all finite
  decompositions `∑ i, x i = x` is convex. In the textbook this is stated for proper convex
  functions, but properness is redundant for the owner-level convexity statement.
- `core/canonical`: the owner abstractions are `finsetInfimalConvolution` /
  `finiteInfimalConvolution` from `Text_5_4_1`, the
  epigraph-based convexity predicate `Function.IsConvex` from `Theorem_4_2`, and the chapter owner
  theorem `Function.isConvex_verticalInfimum` from `Theorem_5_3`.
- `bridge/view`: the proof factors through the support set
  `finsetInfimalConvolutionSupport s f` (or its `Finset.univ` specialization
  `finiteInfimalConvolutionSupport f`) and the owner theorem
  `Function.isConvex_verticalInfimum`.
- Primitive data vs derived API: the family `f` and finite index set `s` are primitive; the owner
  `finsetInfimalConvolution s f` is the primitive finite-operational construction and
  `finiteInfimalConvolution f` is its `Finset.univ` specialization; convexity is derived API.
- Ambient minimization: both the support-set convexity bridge and the owner theorem
  `Function.isConvex_verticalInfimum` live on the ordered-ring layer with only a distributive
  scalar action on `E`, so this file keeps `[Ring 𝕜]` (not a field),
  `[DistribMulAction 𝕜 E]` (not a full `Module`), and does not add a dense-order hypothesis.
- Domain-style sampling used here:
  `finsetInfimalConvolution`,
  `finiteInfimalConvolution`,
  `Function.IsConvex`,
  `Function.isConvex_verticalInfimum`.
- Layer targets:
  - `source-facing`: `Function.isConvex_finsetInfimalConvolution` is the primitive finite
    operational convexity theorem, and `Function.isConvex_finiteInfimalConvolution` is its
    `Finset.univ` specialization;
  - `bridge/view`: the proof factors through the canonical owner theorem
    `Function.isConvex_verticalInfimum` rather than re-exposing a parallel low-level convexity
    construction.
-/

namespace Function

set_option maxHeartbeats 800000 in
/-- Theorem 5.4 at the primitive finite-operational owner layer: if each summand is convex, then
the infimal convolution over a finite index set `s` is convex. Only convexity of indices in `s`
is required. -/
theorem isConvex_finsetInfimalConvolution (s : Finset ι)
    (f : ι → E → WithTopBot 𝕜)
    (hf_convex : ∀ i ∈ s, (f i).IsConvex 𝕜) :
    (finsetInfimalConvolution s f).IsConvex 𝕜 := by
  rw [finsetInfimalConvolution_eq_verticalInfimum]
  exact Function.isConvex_verticalInfimum
    (convex_finsetInfimalConvolutionSupport (s := s) f
      (fun i hi ↦ by
        have hEpi : Convex 𝕜 (epi (f i)) := hf_convex i hi
        exact convexOn_of_convex_finiteHeight_epigraph
          (𝕜 := 𝕜) (s := Set.univ) (f := f i)
          (by simpa only [epi_univ] using hEpi) convex_univ))

section FintypeFamily

variable [Fintype ι]

/-- Theorem 5.4 in `Fintype` form: if each summand is convex, then the finite-family infimal
convolution is convex. This is the `Finset.univ` specialization of
`Function.isConvex_finsetInfimalConvolution`. -/
theorem isConvex_finiteInfimalConvolution
    (f : ι → E → WithTopBot 𝕜)
    (hf_convex : ∀ i, (f i).IsConvex 𝕜) :
    (finiteInfimalConvolution f).IsConvex 𝕜 := by
  simpa [finiteInfimalConvolution] using
    (isConvex_finsetInfimalConvolution (s := (Finset.univ : Finset ι)) f
      (fun i _ ↦ hf_convex i))

end FintypeFamily

end Function

namespace Function.IsConvex

/-- The binary infimal convolution of two convex functions is convex. This is the `Fin 2`
specialization of `Function.isConvex_finiteInfimalConvolution`, exposed on the source-facing pair
surface `![f, g]` and then at the owner `f □ g`. -/
theorem infimal_convolution {f g : E → WithTopBot 𝕜}
    (hf_convex : f.IsConvex 𝕜) (hf_ne_bot : ∀ x, f x ≠ ⊥)
    (hg_convex : g.IsConvex 𝕜) (hg_ne_bot : ∀ x, g x ≠ ⊥) :
    (f □ g).IsConvex 𝕜 := by
  have hEq :
      finiteInfimalConvolution (![f, g] : Fin 2 → E → WithTopBot 𝕜) = f □ g := by
    simpa using finiteInfimalConvolution_pair_eq_infimal_convolution
      (f := f) (g := g) hf_ne_bot hg_ne_bot
  rw [← hEq]
  exact Function.isConvex_finiteInfimalConvolution
    (![f, g] : Fin 2 → E → WithTopBot 𝕜) (Fin.forall_fin_two.2 ⟨hf_convex, hg_convex⟩)

end Function.IsConvex

end
