import Mathlib
import FirstOrderMethodsinOptimization.Chap09.Definition_9_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {ψ ω : E → EReal} {σ : ℝ}

/- Lemma 9.7 is `source-facing` in the Chapter 9 mirror-descent setup. The owner abstraction for
the mirror-map assumptions is already the project class `IsBregmanPotentialOn`, instantiated on the
constraint set `dom(ψ) = effective_domain ψ`; the conclusion itself is the textbook minimizer
statement, expressed directly through mathlib's `IsMinOn` and the Chapter 3 owner
`subdifferential_domain`. -/

-- Proof sketch: use `hω.strongConvexOn_add_indicator` to view `x ↦ ψ x + ω x` as a proper closed
-- `σ`-strongly convex extended-real-valued function on `effective_domain ψ`, then apply the
-- Chapter 5 unique-minimizer theorem to obtain a unique global minimizer. For domain membership,
-- properness gives `xStar ∈ effective_domain ψ`, and Fermat's optimality condition together with
-- the convex sum rule for `ψ + ω` yields a nonempty subdifferential of `ω` at `xStar`.
/-- Lemma 9.7: if `ω` is a Bregman potential on `dom(ψ)` and `ψ` is proper, closed, and convex,
then the composite problem `min_x {ψ(x) + ω(x)}` has a unique minimizer, and that minimizer lies
in `dom(ψ) ∩ dom(∂ ω)`. -/
theorem existsUnique_composite_minimizer_mem_domains
    (hω : IsBregmanPotentialOn ω (effective_domain ψ) σ)
    (hψ_proper : IsProperExtendedRealFunction ψ) (hψ_closed : LowerSemicontinuous ψ)
    (hψ_convex : is_convex_function ψ) :
    ∃! xStar : E,
      IsMinOn (fun x ↦ ψ x + ω x) Set.univ xStar ∧
        xStar ∈ effective_domain ψ ∩ subdifferential_domain ω := sorry

end
