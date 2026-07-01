import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_4_1
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_4_2
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_6
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_2_10

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

section

variable {E : Type u} {ι : Type v} {𝕜 : Type w}
variable [Semiring 𝕜] [ConditionallyCompleteLattice 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E] [Fintype ι]

open scoped Rockafellar
open Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.6.2 rewrites the convex hull of a finite family of functions as the
  infimum, over simplex coefficients `λ`, of the infimal convolution of the right scalar multiples
  `λᵢ •ʳ fᵢ`.
- `core/canonical`: the owner abstractions already available in the chapter are
  `conv(⨅ i, f i)` from `Theorem_5_6`, `finiteInfimalConvolution` from `Text_5_4_1`,
  `Function.rightScalarMul` from `Text_5_4_2`, and the primitive simplex fields
  `StdSimplex.weights`/`StdSimplex.nonneg`.
- `bridge/view`: for a fixed simplex weight `w : StdSimplex 𝕜 ι`, the canonical bridge term is
  `finiteInfimalConvolution (fun i ↦ (⟨w.weights i, w.nonneg i⟩ : Set.Ici (0 : 𝕜)) •ʳ f i)`.
  The public theorem should
  therefore be
  stated directly with the simplex-indexed `iInf` of these upstream owner expressions, rather than
  through a local wrapper.
- Primitive data vs derived API: the finite family `f` is primitive; the simplex-indexed infimum
  of weighted finite-family infimal convolutions is the derived source-facing specification of its
  convex hull.

Domain-style sampling used here:
- `Function.convexHull_iInf_apply_eq_sInf_convexCombination_values`;
- `finiteInfimalConvolution_eq_sInf_decompositions`;
- `Function.rightScalarMul`;
- `StdSimplex.weights` and `StdSimplex.nonneg`.

Ambient/order layer note:
- both the family convex-hull owner `conv(⨅ i, f i)` and the simplex-side weighted infimal
  convolution owner `finiteInfimalConvolution` live at the conditionally complete lattice layer,
  so this theorem is stated directly at that same abstraction level.

The source states the corollary for proper convex functions. For the displayed equality, convexity
is redundant, but a properness-type nondegeneracy hypothesis is not: at zero weight, Text 5.4.3
distinguishes `0 •ʳ f = δ(· | {0})` from the exceptional case `0 •ʳ ⊤ = ⊤`. The public theorem
therefore keeps the owner-minimal guard `∀ i, dom(f i).Nonempty`, which rules out the identically
`⊤` branch, and omits convexity as redundant for the equality itself.
-/

namespace Function

-- Proof sketch: extensionality reduces the function identity to pointwise equality. Apply
-- `convexHull_iInf_apply_eq_sInf_convexCombination_values` to write `conv(⨅ i, f i) x` as the
-- infimum
-- of the weighted sums `∑ i, λᵢ * fᵢ(xᵢ)` over finite convex combinations of `x`. For a fixed
-- simplex weight `w`, unfold
-- `finiteInfimalConvolution_eq_sInf_decompositions` for the family
-- `fun i ↦ (⟨w.weights i, w.nonneg i⟩ : Set.Ici (0 : 𝕜)) •ʳ f i`;
-- the nonempty-domain guard excludes the exceptional branch `0 •ʳ ⊤ = ⊤` from Text 5.4.3, so the
-- right scalar multiple always matches the expected weighted-value formula. This inner infimum is
-- therefore exactly the weighted finite-family infimal convolution. Taking the outer infimum over
-- all simplex weights and then extensionalizing gives the displayed function equality.
/-- Text 5.6.2: the convex hull of a finite family is the infimum, over simplex weights, of the
corresponding weighted finite-family infimal convolutions. Specializing `ι = Fin m` recovers the
textbook formula for `I = {1, ..., m}`; the direct owner expression
`finiteInfimalConvolution (fun i ↦ (⟨w.weights i, w.nonneg i⟩ : Set.Ici (0 : 𝕜)) •ʳ f i)` is the
canonical finite-family form of the
displayed iterated infimal convolution `f₁ λ₁ □ ··· □ f_m λ_m`. The nonempty-domain hypothesis is
essential to exclude the exceptional zero-scalar case `0 •ʳ ⊤ = ⊤`; convexity remains redundant
for this equality and is omitted. -/
theorem convexHull_iInf_eq_iInf_simplex_finiteInfimalConvolution
    (f : ι → E → WithBotTop 𝕜)
    (hf_dom : ∀ i, dom(f i).Nonempty) :
    conv(⨅ i, f i) =
      ⨅ w : StdSimplex 𝕜 ι,
        finiteInfimalConvolution
          (fun i ↦ (⟨w.weights i, w.nonneg i⟩ : Set.Ici (0 : 𝕜)) •ʳ f i) := sorry

end Function

end
