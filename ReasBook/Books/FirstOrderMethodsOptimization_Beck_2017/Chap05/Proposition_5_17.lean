import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_8
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Theorem_5_26

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Proposition 5.17 is `source-facing` in the infimal-convolution smoothing calculus. The owner
abstractions already present in the project are:
- `IsProperExtendedRealFunction`, `is_convex_function`, and `infimal_convolution` for the primal
  extended-real objects;
- `conjugate_function` for the algebraic-dual Fenchel conjugate appearing in the exact formula;
- `conjugate_function_strongDual` and `is_l_smooth_on` for the normed dual/smoothness bridge.

The item splits naturally into two atomic clauses: the exact conjugacy identity for `f □ ω`, then
the smoothness consequence under strong convexity of the conjugate kernel. The second clause is
stated on the continuous dual, since that is the existing normed owner for strong convexity in the
repo. -/

-- Proof sketch: use the conjugacy formula `(f □ ω)^* = f^* + ω^*`, obtained from the infimal
-- convolution theorem together with the no-`⊥` part of properness, and then apply the closed
-- convex biconjugation theorem to `f □ ω`. The canonical bidual equivalence `Module.evalEquiv ℝ E`
-- identifies the primal space with the bidual, yielding the source formula
-- `f □ ω = (f^* + ω^*)^*`.
/-- Proposition 5.17 (1): if `f` and `ω` are proper closed convex extended-real-valued functions,
then their infimal convolution equals the primal-side conjugate of the sum of the conjugates. This
is the owner-level rendering of the textbook identity
`f \square ω = (f^* + ω^*)^*`, with the bidual conjugate transported back to `E` by the canonical
equivalence `Module.evalEquiv ℝ E`. -/
theorem proper_closed_convex_infimal_convolution_eq_dual_conjugate_sum_conjugates
    (f ω : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hω_proper : IsProperExtendedRealFunction ω) (hf_closed : LowerSemicontinuous f)
    (hω_closed : LowerSemicontinuous ω) (hf_convex : is_convex_function f)
    (hω_convex : is_convex_function ω) :
    infimal_convolution f ω =
      conjugate_function (conjugate_function f + conjugate_function ω) ∘ Module.evalEquiv ℝ E :=
  sorry

-- Proof sketch: the strong-convexity hypothesis on `ω^*`, expressed in the repo's normed-dual API
-- via `conjugate_function_strongDual`, makes `f^* + ω^*` strongly convex after adding the proper
-- closed convex conjugate `f^*`. Apply the conjugate smoothness correspondence to that summed dual
-- function and then transport the resulting smoothness statement back to the primal infimal
-- convolution using clause (1).
/-- Proposition 5.17 (2): if `f` and `ω` are proper closed convex extended-real-valued functions
and the continuous-dual Fenchel conjugate `ω^*` is `(1 / L)`-strongly convex, then the real-valued
infimal convolution `x ↦ ((f \square ω) x).toReal` is globally `L`-smooth. This is the canonical
continuous-dual formulation of the textbook clause that `ω^*` being `(1 / L)`-strongly convex,
equivalently `ω` being `L`-smooth, implies `f \square ω` is `L`-smooth. -/
theorem infimal_convolution_toReal_is_l_smooth_of_conjugate_strongConvex
    (f ω : E → EReal) (L : NNReal) (hL_pos : 0 < L) (hf_proper : IsProperExtendedRealFunction f)
    (hω_proper : IsProperExtendedRealFunction ω) (hf_closed : LowerSemicontinuous f)
    (hω_closed : LowerSemicontinuous ω) (hf_convex : is_convex_function f)
    (hω_convex : is_convex_function ω)
    (hω_star_strong :
      StrongConvexOn
        ({y : StrongDual ℝ E | conjugate_function_strongDual ω y < ⊤} : Set (StrongDual ℝ E))
        (1 / (L : ℝ))
        (fun y : StrongDual ℝ E ↦ (conjugate_function_strongDual ω y).toReal)) :
    is_l_smooth_on (fun x ↦ (infimal_convolution f ω x).toReal) Set.univ L := sorry

end
