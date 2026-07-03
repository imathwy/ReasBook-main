import FirstOrderMethodsinOptimization.Chap03.Definition_3_6
import FirstOrderMethodsinOptimization.Chap03.Theorem_3_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open Bornology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Proposition 3.9 is a `bridge/view` statement in the chapter convex-analysis API. Domain
sampling against Definition 3.6, Theorem 3.1, and Theorem 3.3 shows that the relevant owner
surface is already the pair `subdifferential_domain` / `strongDualSubdifferential`, built over the
Chapter 2 owner `effective_domain`; there is no further upstream declaration with the same
conclusion to recall here, so this file should state the proposition directly on that owner API
instead of introducing a parallel wrapper. The literal textbook wording omits the domain condition
`x ∈ subdifferential_domain f`, but that hypothesis is mathematically necessary: if
`x ∉ subdifferential_domain f`, then the subdifferential is empty and hence bounded. The file keeps
that necessary hypothesis explicit in the proposition statement and records the omission only here
in comments. -/
recall effective_domain
recall subdifferential_domain
recall strongDualSubdifferential

-- Proof sketch: translating the affine hull of `effective_domain f` by `-x` does not change its
-- affine dimension, so the geometric hypothesis becomes the strict finrank inequality for the
-- direction space of `affineSpan ℝ (effective_domain f)`. If `x ∈ subdifferential_domain f`, then
-- finite dimensionality upgrades an algebraic-dual subgradient at `x` to the continuous-dual
-- bridge `strongDualSubdifferential f x`. Apply the standard unboundedness argument in codimension
-- at least one on that bridge set.
/-- Proposition 3.9: if the affine hull of the effective domain has direction-space dimension
strictly smaller than the ambient space, equivalently
`Module.finrank ℝ (affineSpan ℝ (effective_domain f)).direction < Module.finrank ℝ E`, then every
point of the owner subdifferential domain `dom(∂ f)` has an unbounded continuous-dual
subdifferential. -/
theorem subdifferential_unbounded_of_affineSpan_effective_domain_direction_finrank_lt
    (f : E → EReal) (x : E)
    (hdim :
      Module.finrank ℝ (affineSpan ℝ (effective_domain f)).direction <
        Module.finrank ℝ E)
    (hx : x ∈ subdifferential_domain f) :
    ¬ IsBounded (strongDualSubdifferential f x) := sorry

end
