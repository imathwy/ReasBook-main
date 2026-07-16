import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap06.Proposition_6_27_6

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 6.27.7 has two clauses. A local minimum point of a convex
  extended-valued function in the effective domain is globally minimizing, hence has zero
  subgradient.
- `core/canonical`: theorem surfaces here use the canonical convexity owner
  `ConvexOn 𝕜 (Set.univ : Set E)`, minimum-set owner `minimumSet`, and intrinsic subdifferential
  owner `_root_.subdifferentialAt`.
- `bridge/view`: the Euclidean vector form is kept as a corollary via
  `mem_minimumSet_iff_zero_mem_subdifferentialAt_vector`.

Canonicalization pass note:
- The codomain layer is normalized to `WithTopBot 𝕜`, and Proposition 6.27.7 now keeps the public
  convexity surface at `ConvexOn` rather than the chapter epigraph alias `Function.IsConvex`.
- Assumption stacks are split by theorem surface so each statement only carries the ambient
  structure needed by its owner/notation layer.
-/

universe u v

open scoped Rockafellar Topology

section

variable {𝕜 : Type v} [Field 𝕜] [LinearOrder 𝕜]
variable [SMul 𝕜 (WithTopBot 𝕜)]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]

/-- Proposition 6.27.7 (1): if `f` is convex and `x` is a local minimum point in `dom(f)`, then
`x` belongs to the minimum set of `f`. -/
theorem mem_minimumSet_of_isLocalMin_of_convexOn_univ
    {f : E → WithTopBot 𝕜} {x : E}
    (hf_convex : ConvexOn 𝕜 (Set.univ : Set E) f)
    (hx : x ∈ dom(f)) (hlocal : IsLocalMin f x) :
    x ∈ minimumSet f := by
  sorry

/-- Pairing-level clause of Proposition 6.27.7 (2): in any pairing model where pairing with `0`
vanishes, a local minimizer in `dom(f)` has `0` in its subdifferential. -/
theorem zero_mem_subdifferentialAt_pairing_of_isLocalMin_of_convexOn_univ
    {Y : Type (max u v)} [Zero Y] [HasPairing E Y 𝕜] [HasPairingZeroRight E Y 𝕜]
    {f : E → WithTopBot 𝕜} {x : E}
    (hf_convex : ConvexOn 𝕜 (Set.univ : Set E) f)
    (hx : x ∈ dom(f)) (hlocal : IsLocalMin f x) :
    (0 : Y) ∈ (∂[Y]f(x)) := by
  exact
    (mem_minimumSet_iff_zero_mem_subdifferentialAt_pairing
      (𝕜 := 𝕜) (E := E) (Y := Y) (f := f) (x := x)).1
      (mem_minimumSet_of_isLocalMin_of_convexOn_univ
        (𝕜 := 𝕜) (E := E) hf_convex hx hlocal)

/-- Proposition 6.27.7 (2): a local minimizer in `dom(f)` has zero continuous-dual subgradient.
-/
theorem zero_mem_subdifferentialAt_of_isLocalMin_of_convexOn_univ
    [TopologicalSpace 𝕜]
    [HasPairing E (StrongDual 𝕜 E) 𝕜] [HasPairingZeroRight E (StrongDual 𝕜 E) 𝕜]
    {f : E → WithTopBot 𝕜} {x : E}
    (hf_convex : ConvexOn 𝕜 (Set.univ : Set E) f)
    (hx : x ∈ dom(f)) (hlocal : IsLocalMin f x) :
    (0 : StrongDual 𝕜 E) ∈ (∂ f at x) := by
  simpa using
    (zero_mem_subdifferentialAt_pairing_of_isLocalMin_of_convexOn_univ
      (𝕜 := 𝕜) (E := E) (Y := StrongDual 𝕜 E) hf_convex hx hlocal)

end

section

variable {𝕜 : Type v} [RCLike 𝕜] [LinearOrder 𝕜]
variable [SMul 𝕜 (WithTopBot 𝕜)]
variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Euclidean bridge form of Proposition 6.27.7 (2): a local minimizer in `dom(f)` has zero vector
subgradient. -/
theorem zero_mem_subdifferentialAt_vector_of_isLocalMin_of_convexOn_univ
    {f : E → WithTopBot 𝕜} {x : E}
    (hf_convex : ConvexOn 𝕜 (Set.univ : Set E) f)
    (hx : x ∈ dom(f)) (hlocal : IsLocalMin f x) :
    (0 : E) ∈ (∂ᵥf(x)) := by
  exact
    (mem_minimumSet_iff_zero_mem_subdifferentialAt_vector
      (𝕜 := 𝕜) (E := E) (f := f) (x := x)).1
      (mem_minimumSet_of_isLocalMin_of_convexOn_univ
        (𝕜 := 𝕜) (E := E) hf_convex hx hlocal)

end
