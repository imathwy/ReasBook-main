import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_21_4 (from Chap04) -/
open scoped RealInnerProductSpace Rockafellar
open Set

noncomputable section

universe u v

section

variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [FiniteDimensional ℝ E]
variable {I : Type v}

local notation "weakRelation" => fun _ : I ↦ ConvexInequalityRelation.le
local notation "weakBounds" => fun _ : I ↦ (0 : EReal)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 21.4 replaces the recession-direction hypothesis in Theorem 21.3, and
  therefore also in Corollary 21.3.1, when the ambient constraint set is the whole space.
- `core/canonical`: the existing owner abstractions are
  `Function.IsClosedProperConvex`, `convexInequalitySolutionSet`, the Chapter 2 recession
  notation `(·)₀⁺`, `Function.recessionCone`, `Function.lineal`, `Finsupp`, and the
  exclusive alternative `Xor'` from Theorem 21.3.
- `bridge/view`: the new source content is the weaker whole-space hypothesis: a finite subfamily
  is affine, and every common recession direction is a direction of constancy for the remaining
  functions.

Domain-style sampling used here:
- `Function.IsClosedProperConvex`, `convexInequalitySolutionSet`, and
  `nonpositive_convexInequalitySolutionSet_nonempty_iff` from
  [Theorem_21_3](/volume/math/AI4M/users/zcwang/bookrepo/ConvexAnalysis_Rockafellar_1970/ConvexAnalysis_Rockafellar_1970/Chap04/Theorem_21_3.lean);
- `Finsupp.IsNonnegativeMultiplierCertificateOn` from
  [Theorem_21_3](/volume/math/AI4M/users/zcwang/bookrepo/ConvexAnalysis_Rockafellar_1970/ConvexAnalysis_Rockafellar_1970/Chap04/Theorem_21_3.lean);
- `Function.recessionCone` from
  [Definiton_8_5_0](/volume/math/AI4M/users/zcwang/bookrepo/ConvexAnalysis_Rockafellar_1970/ConvexAnalysis_Rockafellar_1970/Chap02/Definiton_8_5_0.lean);
- `Function.lineal` from
  [Definition_8_9_0](/volume/math/AI4M/users/zcwang/bookrepo/ConvexAnalysis_Rockafellar_1970/ConvexAnalysis_Rockafellar_1970/Chap02/Definition_8_9_0.lean);
- the Chapter 2 recession-function notation `(·)₀⁺`;
- the affine-map codomain lift `AffineMap.toEReal`.

Primitive data vs derived API:
- primitive source-facing inputs: the family `f` and the weaker whole-space hypothesis consisting
  of a finite affine core, closed/proper/convex regularity on the non-affine remainder, and the
  corresponding recession-lineality conclusion on that remainder;
- derived owner output: the same weak-feasible-set alternative as in Theorem 21.3, specialized to
  `C = univ`;
- derived source-facing output: the pointwise existence alternative and the corresponding
  small-subsystem solvability consequence.

Layer target: the finite-affine-core hypothesis stays `source-facing`, while the main alternative
theorem is refined to the `core/canonical` owner `convexInequalitySolutionSet weakRelation f
weakBounds`. The pointwise `∃ x, ∀ i, f i x ≤ 0` form is kept only as a thin companion bridge.
The recession clause itself is stated in the existing function-facing owner language of Chapter 8:
`y ∈ Function.recessionCone ((f i)₀⁺)` for common recession directions and
`y ∈ Function.lineal (f i)` for the constancy conclusion. Since this weaker recession
hypothesis is source-facing content rather than a reusable owner object, it is kept directly on the
theorem surface instead of as a public wrapper `def`.
-/

-- Proof sketch: modify the proof of Theorem 21.3 using the finite affine core `I₀`. The affine
-- members make the auxiliary function `k₀` polyhedral, while the constancy conclusion on common
-- recession directions gives the separation argument needed to show that the convolution term at
-- `0` is already closed. The rest of the original alternative proof is unchanged.
/-- Theorem 21.4, in canonical owner form: under the weaker whole-space recession hypothesis, the
whole-space weak feasible set `convexInequalitySolutionSet weakRelation f weakBounds` is nonempty
or there is a finitely supported nonnegative multiplier certificate on `univ`. Specializing
`E = EuclideanSpace ℝ (Fin n)` recovers the textbook `R^n` statement. -/
theorem
    xor_nonpositive_convexInequalitySolutionSet_nonempty_or_finitely_supported_nonnegative_multiplier_certificate_of_finite_affine_core
    (f : I → E → EReal)
    (hfinite_affine_core :
      ∃ I₀ : Set I, I₀.Finite ∧
        (∀ i ∈ I₀, ∃ a : E →ᵃ[ℝ] ℝ, f i = a.toEReal) ∧
          (∀ i ∉ I₀, Function.IsClosedProperConvex (𝕜 := ℝ) (f i)) ∧
          ∀ y : E,
            (∀ i : I, y ∈ Function.recessionCone ((f i)₀⁺)) →
            ∀ i ∉ I₀, y ∈ Function.lineal (f i))
    :
    Xor'
      (convexInequalitySolutionSet weakRelation f weakBounds).Nonempty
      (∃ weights : I →₀ ℝ, ∃ epsilon : ℝ,
        weights.IsNonnegativeMultiplierCertificateOn Set.univ f epsilon) := sorry

/-- Source-facing pointwise restatement of Theorem 21.4: the owner weak-feasible-set alternative
for `C = univ` is equivalent to existence of `x` with `f i x ≤ 0` for every `i`. -/
theorem xor_exists_nonpositive_point_or_finitely_supported_nonnegative_multiplier_certificate_of_finite_affine_core
    (f : I → E → EReal)
    (hfinite_affine_core :
      ∃ I₀ : Set I, I₀.Finite ∧
        (∀ i ∈ I₀, ∃ a : E →ᵃ[ℝ] ℝ, f i = a.toEReal) ∧
          (∀ i ∉ I₀, Function.IsClosedProperConvex (𝕜 := ℝ) (f i)) ∧
          ∀ y : E,
            (∀ i : I, y ∈ Function.recessionCone ((f i)₀⁺)) →
            ∀ i ∉ I₀, y ∈ Function.lineal (f i))
    :
    Xor'
      (∃ x : E, ∀ i : I, f i x ≤ 0)
      (∃ weights : I →₀ ℝ, ∃ epsilon : ℝ,
        weights.IsNonnegativeMultiplierCertificateOn Set.univ f epsilon) := by
  simpa [Set.Nonempty, mem_convexInequalitySolutionSet] using
    xor_nonpositive_convexInequalitySolutionSet_nonempty_or_finitely_supported_nonnegative_multiplier_certificate_of_finite_affine_core
      f hfinite_affine_core

-- Proof sketch: argue exactly as in Corollary 21.3.1, but use Theorem 21.4 in place of Theorem
-- 21.3. If the multiplier alternative held, the support bound `Module.finrank ℝ E + 1` would
-- contradict the assumed strict feasibility of every subsystem of size at most
-- `Module.finrank ℝ E + 1`, so the feasible-point alternative must occur.
/-- Under the weaker whole-space recession hypothesis, strict feasibility of every subsystem of at
most `Module.finrank ℝ E + 1` inequalities implies the existence of a global nonpositive point.
Specializing `E = EuclideanSpace ℝ (Fin n)` recovers the textbook bound `n + 1`. -/
theorem exists_point_of_small_subsystems_strictly_feasible_of_finite_affine_core
    (f : I → E → EReal)
    (hfinite_affine_core :
      ∃ I₀ : Set I, I₀.Finite ∧
        (∀ i ∈ I₀, ∃ a : E →ᵃ[ℝ] ℝ, f i = a.toEReal) ∧
          (∀ i ∉ I₀, Function.IsClosedProperConvex (𝕜 := ℝ) (f i)) ∧
          ∀ y : E,
            (∀ i : I, y ∈ Function.recessionCone ((f i)₀⁺)) →
            ∀ i ∉ I₀, y ∈ Function.lineal (f i))
    (h_small_feasible :
      ∀ J : Finset I, J.card ≤ Module.finrank ℝ E + 1 → ∀ ε > (0 : ℝ),
        ∃ x : E, ∀ i ∈ J, f i x < ε) :
    ∃ x : E, ∀ i : I, f i x ≤ 0 := sorry

end
