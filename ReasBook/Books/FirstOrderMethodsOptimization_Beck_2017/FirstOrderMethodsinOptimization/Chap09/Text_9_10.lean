import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap09.Definition_9_2
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap09.Definition_9_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Gradient

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Text 9.10 is a `bridge/view` item in the Chapter 9 Mirror-C/Bregman domain.
Domain sampling points to these existing owners:
- `mirror_c_update_objective` from Definition 9.6 for the source-facing one-step Mirror-C update;
- `mirror_c_problem_functional` from Definition 9.6 for the linear perturbation term;
- Chapter 9's canonical Bregman owner `extendedRealBregmanDistance` / `B[ω]` from Definition 9.2;
- the defining equations `mirror_c_update_objective_apply` and `bregmanDistance_def`, which already
  encode the gradient term through the canonical owners.

The layer split is therefore:
- `source-facing`: `mirror_c_update_objective`;
- `core/canonical`: `B[ω]`;
- `bridge/view`: the equation-(9.33) rewrite showing that adding an `x`-independent constant turns
  the source-facing owner into the Bregman-form objective.

The primitive data are only the canonical Mirror-C owner from Definition 9.6 and the canonical
Bregman owner from Definition 9.2. This file is a purely algebraic rewrite of those definitions,
so the regularity package `IsBregmanPotentialOn ω Set.univ σ` and the base-point condition
`xk ∈ subdifferential_domain ω` belong to later analytic results, not to this bridge itself. The
Bregman-form objective is derived API and should appear directly on theorem surfaces through
`B[ω]`, not via a second local objective wrapper. -/

-- Proof sketch: expand `mirror_c_update_objective`, rewrite the derivative term at `xk` as the
-- gradient pairing `⟪∇ω(xk), x⟫`, expand `B[ω] x xk`, and cancel the `x`-independent constant
-- `ω(xk) - ⟪∇ω(xk), xk⟫`. This is a direct definitional calculation using
-- `mirror_c_update_objective_apply`, `mirror_c_problem_functional_apply`, and
-- `bregmanDistance_def`.
/-- Adding the constant `⟪∇ω(x^k), x^k⟫ - ω(x^k)` rewrites the canonical Mirror-C owner from
equation `(9.32)` into the equation `(9.33)` Bregman form
`x ↦ ⟪t s, x⟫ + t g(x) + B_ω(x, x^k)`. -/
theorem mirror_c_update_objective_add_constant_eq_bregman_form
    (g ω : E → EReal) (xk : E) (s : StrongDual ℝ E) (t : ℝ) :
    (fun x ↦
      mirror_c_update_objective g ω xk s t x +
        (((inner ℝ (∇ (fun y ↦ (ω y).toReal) xk) xk : ℝ) : EReal) -
          ((ω xk).toReal : EReal))) =
      fun x ↦
        (((t * s x : ℝ) : EReal) + (t : EReal) * g x) +
          ((B[ω] x xk : ℝ) : EReal) := sorry

-- Proof sketch: rewrite the equation-(9.33) objective using
-- `mirror_c_update_objective_add_constant_eq_bregman_form`; the two functions differ by the
-- `x`-independent constant `⟪∇ω(x^k), x^k⟫ - ω(x^k)`, so they have the same minimizers on
-- `Set.univ`. No Bregman-potential or extendedRealSubdifferential-domain hypotheses are needed because the
-- claim is only about the totalized definitions already present upstream.
/-- Text 9.10: the Mirror-C update formula can be rewritten from the linearized objective
in equation `(9.32)` to the Bregman-distance objective in equation `(9.33)` without changing the
set of minimizers. -/
theorem isMinOn_mirror_c_update_objective_iff_isMinOn_bregman_update_objective
    (g ω : E → EReal) (xk xNext : E) (s : StrongDual ℝ E) (t : ℝ) :
    IsMinOn (mirror_c_update_objective g ω xk s t) Set.univ xNext ↔
      IsMinOn
        (fun x ↦ (((t * s x : ℝ) : EReal) + (t : EReal) * g x) + ((B[ω] x xk : ℝ) : EReal))
        Set.univ xNext := sorry

end
