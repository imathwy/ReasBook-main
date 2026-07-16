import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_5_2
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_6
import ConvexAnalysis_Rockafellar_1970.Chap04.Definition_17_0_1

open Convexity
open scoped Function Rockafellar

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u v

variable {E : Type u} {I : Type v} {R : Type*}
variable [Field R] [ConditionallyCompleteLinearOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup E] [Module R E] [FiniteDimensional R E]

local instance : ConvexSpace R E := ConvexSpace.ofModule
local instance : IsModuleConvexSpace R E := IsModuleConvexSpace.ofModule
local instance : SMul R (WithTopBot R) where
  smul c z := (c : WithTopBot R) * z

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 17.1.3 refines the family convex-hull value formula by showing that
  the infimum may be taken only over convex-combination representations using at most
  `dim E + 1` nonzero coefficients, with the participating points affinely independent.
- `core/canonical`: the owner abstraction already present in the project is the family convex hull
  `conv(⨅ i, f i)` from `Theorem_5_6`, together with the canonical convexity owner
  `ConvexOn R Set.univ`; the needed height-side exclusion is the owner-side pointwise condition
  `∀ i x, ⊥ < f i x`.
- `bridge/view`: Corollary 17.1.1 is the finite-dimensional Carathéodory theorem for a union of
  convex sets. Applying it to the family of epigraphs `epi (f i)` yields the stated restricted
  infimum formula for the family convex hull.

Domain-style sampling used here:
- `Function.convexHull_iInf_eq_sInf_convexCombination_values`;
- `exists_affineIndependent_convexCombination_of_mem_convexHull_iUnion`;
- `StdSimplex.sum`;
- `ConvexOn`;
- `Function.IsProper.bot_lt`.

Primitive data vs derived API:
- primitive inputs: the family `f` of convex functions on a finite-dimensional `R`-vector space,
  together with the pointwise exclusion `∀ i x, ⊥ < f i x`, where `R` is an ordered field with
  enough order completeness to form the `sInf` appearing in the convex-hull owner theorem;
- derived output: the Carathéodory-restricted `sInf` formula for `conv(⨅ i, f i)`.

Redundant-source-assumption audit:
- convexity is essential because the proof passes through convexity of each epigraph `epi (f i)`;
- the needed exclusion is only that epigraph fibers contain no full vertical line, and in the
  owner language this is exactly the pointwise condition `∀ i x, ⊥ < f i x`;
- the nonempty-domain half of `Function.IsProper` does not change the value formula, so a
  properness-form restatement belongs only as a thin companion.

Layer target: `source-facing`, stated directly as a refinement of the family convex-hull value
formula rather than by introducing a new wrapper for admissible coefficient packages.
-/

namespace Function

-- Proof sketch: start from the family convex-hull value theorem
-- `convexHull_iInf_eq_sInf_convexCombination_values`, which identifies `conv(⨅ i, f i) x` with
-- the vertical infimum over convex combinations of epigraph points. Apply Corollary 17.1.1 to the
-- family of convex epigraphs `epi (f i)` in `E × R` to reduce each admissible epigraph point to a
-- simplex with at most `Module.finrank R E + 1` vertices coming from pairwise distinct indices.
-- The pointwise exclusion `∀ i x, ⊥ < f i x` removes vertical-line degeneracies, so one may
-- lower the height within the same simplex to a minimal value and thereby arrange that all
-- participating coefficients are positive and the corresponding points in `E` are affinely
-- independent.
/-- Corollary 17.1.3: if `fᵢ`, `i ∈ I`, are convex `[-∞, +∞]`-valued functions on a
finite-dimensional vector space over an ordered field `R` with conditionally complete order, and
never take the value `⊥`, then `conv(⨅ i, f i)` is their convex hull and
`conv(⨅ i, f i) x` is the infimum of the weighted sums `∑ λⱼ f_{iⱼ}(xⱼ)` over all convex
combinations of `x` with at most `Module.finrank R E + 1` positive coefficients, taken from
pairwise distinct family indices, whose support points are affinely independent. The distinct
index condition is recorded canonically by a finite support `s : Finset I`, so the theorem uses
the same owner surface as Corollary 17.1.1 instead of a separate embedding `Fin m ↪ I`.
Specializing to `R = ℝ` and `E = EuclideanSpace ℝ (Fin n)` recovers the textbook `R^n` statement
with `n + 1` or fewer nonzero coefficients. -/
theorem convexHull_iInf_eq_sInf_affineIndependent_convexCombination_values
    (f : I → E → WithTopBot R)
    (hf_convex : ∀ i : I, ConvexOn R Set.univ (f i))
    (hf_bot : ∀ i x, ⊥ < f i x)
    (x : E) :
    conv(⨅ i, f i) x =
      sInf
        {r : WithTopBot R |
          ∃ s : Finset I, s.card ≤ Module.finrank R E + 1 ∧
            ∃ z : (i : s) → E,
              AffineIndependent R z ∧
                ∃ w : StdSimplex R s,
                  (∀ i : s, 0 < w.weights i) ∧
                    x = (w.map z).convexCombination ∧
                      r = w.sum (fun i a ↦ (a : WithTopBot R) * f i (z i))} := sorry

/-- Properness-form restatement of Corollary 17.1.3. This companion adds no new mathematics: its
only use of `Function.IsProper (f i)` is to recover the pointwise exclusion `∀ i x, ⊥ < f i x`
required by the main theorem. -/
theorem convexHull_iInf_eq_sInf_affineIndependent_convexCombination_values_of_proper
    (f : I → E → WithTopBot R)
    (hf_convex : ∀ i : I, ConvexOn R Set.univ (f i))
    (hf_proper : ∀ i : I, (f i).IsProper)
    (x : E) :
    conv(⨅ i, f i) x =
      sInf
        {r : WithTopBot R |
          ∃ s : Finset I, s.card ≤ Module.finrank R E + 1 ∧
            ∃ z : (i : s) → E,
              AffineIndependent R z ∧
                ∃ w : StdSimplex R s,
                  (∀ i : s, 0 < w.weights i) ∧
                    x = (w.map z).convexCombination ∧
                      r = w.sum (fun i a ↦ (a : WithTopBot R) * f i (z i))} := by
  exact
    convexHull_iInf_eq_sInf_affineIndependent_convexCombination_values
      f hf_convex (fun i x ↦ (hf_proper i).bot_lt_withTopBot x) x

end Function

end
