import Mathlib
import FirstOrderMethodsinOptimization.Chap09.Lemma_9_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {g ω : E → EReal} {σ : ℝ}

/- Domain sampling for Theorem 9.24:
- `source-facing`: the textbook Mirror-C auxiliary problem with linear perturbation `x ↦ a x`;
- `core/canonical`: Chapter 9's owner theorem `existsUnique_composite_minimizer_mem_domains`
  applied to `ψ x = ((a x : ℝ) : EReal) + g x`;
- `bridge/view`: no separate owner is needed here, because the linear perturbation is primitive
  data and the displayed objective is just the direct specialization of the composite owner.

The primitive data are therefore exactly `a`, `g`, and the Bregman-potential hypothesis on `ω`
over `effective_domain g`. A standalone local objective wrapper would duplicate the chapter owner
surface without adding mathematical content, so the public theorem below keeps the objective in its
canonical specialized form. -/

-- Proof sketch: apply Lemma 9.7 to the perturbed function
-- `ψ(x) = ((a x : ℝ) : EReal) + g(x)`. A continuous linear functional is finite, proper, closed,
-- and convex, so adding it to `g` preserves the hypotheses required by Lemma 9.7 and leaves the
-- effective domain equal to `effective_domain g`.
/-- Theorem 9.24: if `g` is proper, closed, and convex, and `ω` is a Bregman potential on
`dom(g)`, then the Mirror-C auxiliary problem
`min_x {⟨a, x⟩ + g(x) + ω(x)}` has a unique minimizer in
`dom(g) ∩ dom(∂ ω)`. -/
theorem existsUnique_mirror_c_problem_minimizer_mem_domains
    (a : StrongDual ℝ E) (hω : IsBregmanPotentialOn ω (effective_domain g) σ)
    (hg_proper : IsProperExtendedRealFunction g) (hg_closed : LowerSemicontinuous g)
    (hg_convex : is_convex_function g) :
    ∃! xStar : E,
      IsMinOn (fun x ↦ ((a x : ℝ) : EReal) + g x + ω x) Set.univ xStar ∧
        xStar ∈ effective_domain g ∩ subdifferential_domain ω := sorry

end
