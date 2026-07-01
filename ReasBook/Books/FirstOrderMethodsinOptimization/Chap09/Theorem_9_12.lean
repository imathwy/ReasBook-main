import Mathlib
import FirstOrderMethodsinOptimization.Chap09.Definition_9_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Gradient

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {ψ ω : E → EReal} {σ : ℝ} {a b : E}

/- Theorem 9.12 is `source-facing` in the Chapter 9 Bregman-prox API. The owner abstractions are
Chapter 3's `subdifferential_domain`, the Chapter 9 Bregman-distance owner `B[ω]`, and the
Bregman-potential owner `IsBregmanPotentialOn`. The textbook hypothesis is the argmin condition for
the second-prox objective `x ↦ ψ x + B[ω] x b`, while the later Mirror-C `(s, t) = (0, 1)`
specialization is only a bridge/view of this source-facing objective and does not belong on the
main theorem surface. -/

-- Proof sketch: first use the minimizer condition for the second-prox objective
-- `x ↦ ψ x + B[ω] x b` together with properness of `ψ` to show that the minimizing point `a`
-- lies in `effective_domain ψ`. Then apply Fermat's condition to the convex perturbation
-- `x ↦ ψ x - ⟪∇ ωᵣ b, x⟫ + ω x`, using the Bregman-potential hypotheses and the domain condition
-- on `b`, to upgrade this minimizer to a point of `subdifferential_domain ω`.
/-- The minimizer of the equation-(9.17) non-Euclidean second-prox objective lies in the effective
domain of `ψ` and in `dom(∂ ω)`. -/
theorem non_euclidean_second_prox_minimizer_mem_domains
    (hω : IsBregmanPotentialOn ω (effective_domain ψ) σ)
    (hψ_proper : IsProperExtendedRealFunction ψ) (hψ_convex : is_convex_function ψ)
    (hb : b ∈ subdifferential_domain ω)
    (ha : IsMinOn (fun x ↦ ψ x + B[ω] x b) Set.univ a) :
    a ∈ effective_domain ψ ∧ a ∈ subdifferential_domain ω := sorry

-- Proof sketch: rewrite the minimization problem through
-- `x ↦ ψ x + B[ω] x b`, use the companion domain theorem to obtain `a ∈ dom(∂ ω)`, and then
-- apply Fermat's condition to the convex function
-- `x ↦ ψ x + ω x - ⟪∇ ωᵣ b, x⟫`. This yields a subgradient of `ψ` at `a` equal to
-- `∇ ωᵣ b - ∇ ωᵣ a`, and the displayed inequality is exactly the subgradient inequality for `ψ`.
/-- Theorem 9.12: non-Euclidean second prox theorem. If `b ∈ dom(∂ ω)` and `a` minimizes
`x ↦ ψ(x) + B[ω] x b`, then for every `u ∈ dom(ψ)` one has the optimality inequality
`⟪∇ω(b) - ∇ω(a), u - a⟫ ≤ ψ(u) - ψ(a)` in extended-real form. -/
theorem non_euclidean_second_prox_optimality_ineq
    (hω : IsBregmanPotentialOn ω (effective_domain ψ) σ)
    (hψ_proper : IsProperExtendedRealFunction ψ) (hψ_convex : is_convex_function ψ)
    (hb : b ∈ subdifferential_domain ω)
    (ha : IsMinOn (fun x ↦ ψ x + B[ω] x b) Set.univ a)
    (u : E) (hu : u ∈ effective_domain ψ) :
    (inner ℝ
        ((∇ (fun x ↦ (ω x).toReal) b) - (∇ (fun x ↦ (ω x).toReal) a)) (u - a) :
      EReal) ≤ ψ u - ψ a := sorry

end
