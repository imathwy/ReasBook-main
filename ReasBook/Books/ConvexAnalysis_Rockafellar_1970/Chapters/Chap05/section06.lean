

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_5_6_1 (from Chap01) -/
noncomputable section

universe u v w

open scoped Rockafellar

attribute [local instance] Classical.propDecidable

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.6.1 specializes the family convex-hull theorem to functions supported at
  single points, with prescribed finite values `α i` at `a i` and `+∞` elsewhere.
- `core/canonical`: the chapter owners already available are the singleton indicator
  `δ(· | {a i})`, the family convex hull `conv(⨅ i, f i)`, the finite-simplex owner
  `StdSimplex 𝕜 s`, and the maximal minorant theorem `Function.isGreatest_conv_iInf_minorant`.
- `bridge/view`: the source family surface is used directly as
  `fun i x ↦ δ(x | ({a i} : Set E)) + α i`. The value formula is exposed directly as a
  finite-simplex set-builder specialization of
  `Function.convexHull_eq_sInf_convexCombination_values`, and the maximality claim is stated on
  the canonical hull `conv(⨅ i, fun x ↦ δ(x | ({a i} : Set E)) + α i)`.

Domain-style sampling used here:
- `indicator`;
- `StdSimplex`;
- `Function.convexHull_iInf_apply_eq_sInf_convexCombination_values`;
- `Function.isGreatest_conv_iInf_minorant`.

Layer target:
- no new owner is introduced, because the textbook surface already matches the canonical indicator
  notation;
- the theorems are `bridge/view` specializations of the existing canonical family convex-hull
  owners stated directly on that surface.
-/

section Formula

variable {E : Type u} {𝕜 : Type w} {I : Type v}
variable [Semiring 𝕜] [ConditionallyCompleteLattice 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

namespace Function

-- Proof sketch: specialize `Function.convexHull_iInf_apply_eq_sInf_convexCombination_values` to
-- the family `fun i x ↦ δ(x | ({a i} : Set E)) + α i`. The singleton-support branch behavior of
-- `δ(x | ({a i} : Set E))` reduces admissible finite combinations to convex combinations of the
-- prescribed points `a i`, and the weighted value sum becomes `∑ λ_i α_i`.
/-- The convex hull of the singleton-indicator family
`f_i(x) = δ(x | ({a i} : Set E)) + α i` is the infimum of the weighted sums
`∑ λ_i α_i` over all finite convex-combination representations of `x` by the points `a i`. -/
theorem convexHull_iInf_indicator_singleton_add_eq_sInf_convexCombination_values
    (a : I → E) (α : I → 𝕜) (x : E) :
    conv(⨅ i, (fun x : E ↦ δ[𝕜](x | ({a i} : Set E)) + (α i : WithBotTop 𝕜))) x =
      sInf
        {r : WithBotTop 𝕜 |
          ∃ (s : Finset I) (w : StdSimplex 𝕜 s),
            x = w.sum (fun i c ↦ c • a i) ∧
              r = (by
                classical
                exact w.sum (fun i c ↦ (c : WithBotTop 𝕜) * (α i : WithBotTop 𝕜))
                  : WithBotTop 𝕜)} := sorry

end Function

end Formula

section GreatestMinorant

variable {E : Type u} {𝕜 : Type w} {I : Sort v}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

namespace Function

-- Proof sketch: apply `Function.isGreatest_conv_iInf_minorant` to the family
-- `fun i x ↦ δ(x | ({a i} : Set E)) + α i`. For these singleton-support functions, the pointwise
-- minorant condition is equivalent to the single value constraint `h (a i) ≤ α i`, because the
-- right-hand side is `⊤` away from `a i`.
/-- Text 5.6.1: the convex hull of the singleton-support family is the greatest convex function
satisfying the pointwise constraints `f(a_i) ≤ α_i`. -/
theorem isGreatest_convexHull_iInf_indicator_singleton_add_minorant
    (a : I → E) (α : I → 𝕜) :
    IsGreatest
      {h : E → WithBotTop 𝕜 | h.IsConvex 𝕜 ∧ ∀ i : I, h (a i) ≤ α i}
      (conv(⨅ i, (fun x : E ↦ δ[𝕜](x | ({a i} : Set E)) + (α i : WithBotTop 𝕜)))) := sorry

end Function

end GreatestMinorant

/-! ### Text_5_6_2 (from Chap01) -/
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

/-! ### Theorem_5_6 (from Chap01) -/
noncomputable section

open scoped BigOperators

universe u v w

section

variable {E : Type u} {𝕜 : Type w}
variable [Semiring 𝕜] [ConditionallyCompleteLattice 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E] {I : Sort v}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 5.6 is a formula for the convex hull of a *family* of proper convex
  functions: at `x`, take the infimum over finite convex-combination representations
  `x = ∑ λ_j x_j` and finite choices of family members `i_j`, of the values
  `∑ λ_j f_{i_j}(x_j)`.
- `core/canonical`: the owner below is a family-indexed convex-hull value function.  It is not the
  single-function owner applied to the pointwise infimum `⨅ i, f i`; that loses the source's
  finite choice of an index for each point in the combination.
- `bridge/view`: the theorem is kept as an explicit set of admissible finite weighted values.
-/

namespace Function

/-- Helper for Theorem 5.6: admissible weighted sums obtained from finite convex combinations of
points, where each point may use a separately chosen member of the family. -/
private def familyConvexCombinationValues
    (f : I → E → WithTopBot 𝕜) (x : E) : Set (WithTopBot 𝕜) :=
  {r : WithTopBot 𝕜 |
    ∃ (ι : Type max u w) (idx : ι → I) (w : StdSimplex 𝕜 ι) (z : ι → E) (μ : ι → 𝕜),
      x = w.sum (fun j a ↦ a • z j) ∧
        (∀ j, f (idx j) (z j) ≤ (μ j : WithTopBot 𝕜)) ∧
        r = ((w.sum (fun j a ↦ a * μ j) : 𝕜) : WithTopBot 𝕜)}

/-- Helper for Theorem 5.6: the family convex-hull value at `x` is the infimum of the finite
family-indexed convex-combination values above `x`. -/
private def familyConvexHullValue (f : I → E → WithTopBot 𝕜) : E → WithTopBot 𝕜 :=
  fun x ↦ sInf (familyConvexCombinationValues f x)

local notation:max "convFamily(" f ")" => familyConvexHullValue f

/-- Theorem 5.6, pointwise owner form: the convex hull of a family is the infimum over all finite
family-indexed convex-combination representations of the point. -/
theorem convexHull_family_apply_eq_sInf_convexCombination_values
    (f : I → E → WithTopBot 𝕜) (x : E) :
    convFamily(f) x = sInf (familyConvexCombinationValues f x) := by
  simp [familyConvexHullValue]

/-- Theorem 5.6, function owner form. -/
theorem convexHull_family_eq_sInf_convexCombination_values
    (f : I → E → WithTopBot 𝕜) :
    convFamily(f) = sInf ∘ familyConvexCombinationValues f := by
  funext x
  simp [familyConvexHullValue, Function.comp_apply]

/-- Set-builder view of the pointwise Theorem 5.6 formula. -/
theorem convexHull_family_apply_eq_sInf_convexCombination_values_set
    (f : I → E → WithTopBot 𝕜) (x : E) :
    convFamily(f) x =
      sInf {r : WithTopBot 𝕜 | r ∈ familyConvexCombinationValues f x} := by
  simp [familyConvexHullValue]

end Function

end
