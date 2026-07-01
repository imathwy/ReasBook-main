import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Prop_4_4_1
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_8_9_4
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_13_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

variable {E : Type*}
variable [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
variable [FiniteDimensional ℝ E]
variable [HasLinearPairing E E ℝ] [HasContinuousPairing E E ℝ]

open ConvexERealFunction
open scoped Rockafellar

local notation "IsClosedProperConvex[ℝ]" => Function.IsClosedProperConvex (𝕜 := ℝ)

/-
Source/core/bridge triage:
- `source-facing`: Corollary 13.4.2 characterizes when the effective domain of the Fenchel
  conjugate `f*` has nonempty interior by excluding affine lines on which `f` stays finite and
  affine.
- `core/canonical`: the owner abstractions are `convexConjugate`, `Function.rank`, the
  function-dimension owner `dim(·)` applied to `f⋆`, the dimension formula for `dom f*`,
  `Function.lineality`, and mathlib's convex-set
  interior criterion
  `Convex.interior_nonempty_iff_affineSpan_eq_top`.
- `bridge/view`: the textbook phrase `dom f*` is rendered directly by the chapter effective-domain
  owner `dom(f⋆)`, so no new local set-builder wrapper is introduced.
- Domain-style sampling used here:
  `Function.lineality_eq_zero_iff_not_exists_affineLine`,
  `effectiveDomain_convexConjugate_affineDim_eq_ambientDim_sub_lineality`, and
  `Convex.interior_nonempty_iff_affineSpan_eq_top`, together with
  `Function.isConvex_convexConjugate`.
- Primitive data vs derived API:
  the primitive input is the function `f : E → WithTopBot ℝ`; the standing closed-proper-convex
  assumptions are bundled by the Chapter 3 owner predicate `IsClosedProperConvex[ℝ]`, while
  the interior-of-`dom f*` condition, its lineality-zero criterion, and the affine-line exclusion
  are all derived theorem-level views.
- Layer target: owner-first plus source-facing bridge. The primary theorem in this file is
  stated directly at the canonical owner level
  `(interior dom(f⋆)).Nonempty ↔ lineality[ℝ](f) = 0`, and the textbook affine-line wording is
  kept as a thin corollary via
  `Function.lineality_eq_zero_iff_not_exists_affineLine`.
- Scalar/codomain/topology checks for this item:
  - codomain: this theorem is stated directly on `WithTopBot ℝ`, matching the Chapter 2
    quantified affine-line exclusion bridge and the Chapter 3 affine-dimension bridge API without
    alias-level coercion noise;
  - scalar: the result remains genuinely `ℝ`-scalar because the reused Chapter 8/13 lineality and
    affine-dimension bridge API is currently real-parameterized;
  - topology: ambient `interior` (not `intrinsicInterior`) is primary here, since the theorem
    characterizes full-dimensionality of `dom(f⋆)` in the ambient space.
-/

-- Proof sketch (owner form): the finite domain of `convexConjugate f` is convex, so
-- `Convex.interior_nonempty_iff_affineSpan_eq_top` identifies nonempty interior with full affine
-- dimension `Module.finrank ℝ E`. The Chapter 3 formula
-- `effectiveDomain_convexConjugate_affineDim_eq_ambientDim_sub_lineality` rewrites that as
-- `lineality[ℝ](f) = 0`.
-- In the backward interior→dimension step, nonemptiness of `affineSpan ℝ (dom f⋆)` is
-- obtained
-- directly from the affine-dimension hypothesis (excluding the `⊥` case), so no extra properness
-- bridge for `f⋆` is needed.
namespace Function.IsClosedProperConvex

/-- Owner form of Corollary 13.4.2: a closed proper convex function has conjugate with finite
domain of nonempty interior exactly when the primal lineality vanishes. -/
theorem interior_dom_convexConjugate_nonempty_iff_lineality_eq_zero
    {f : E → WithTopBot ℝ} (hf : IsClosedProperConvex[ℝ] f) :
    (interior dom(f⋆)).Nonempty ↔
      lineality[ℝ](f) = 0 := by
  have hconv_conjugate : (f⋆).IsConvex ℝ := Function.isConvex_convexConjugate f
  have hconv : Convex ℝ dom(f⋆) := hconv_conjugate.convex_dom
  have hinterior_iff_dim :
      (interior dom(f⋆)).Nonempty ↔
        dim((f⋆ : E → WithTopBot ℝ)) = (Module.finrank ℝ E : ℤ) := by
    rw [hconv.interior_nonempty_iff_affineSpan_eq_top]
    constructor
    · intro htop
      have htop_ne_bot : (⊤ : AffineSubspace ℝ E) ≠ ⊥ :=
        (AffineSubspace.bot_ne_top ℝ E E).symm
      rw [Set.affineDim, htop, AffineSubspace.affineDim, if_neg htop_ne_bot,
        AffineSubspace.direction_top]
      exact_mod_cast (finrank_top ℝ E)
    · intro hdim
      let s : AffineSubspace ℝ E := affineSpan ℝ dom(f⋆)
      have hs_ne_bot : s ≠ ⊥ := by
        intro hs_bot
        have hdim_bot : dim((f⋆ : E → WithTopBot ℝ)) = -1 := by
          simp [Function.dim, s, Set.affineDim, AffineSubspace.affineDim, hs_bot]
        have hfinrank_nonneg : (0 : ℤ) ≤ (Module.finrank ℝ E : ℤ) := by
          exact_mod_cast (Nat.zero_le (Module.finrank ℝ E))
        omega
      have hs_nonempty : (s : Set E).Nonempty :=
        (AffineSubspace.nonempty_iff_ne_bot s).2 hs_ne_bot
      have hs_finrank : Module.finrank ℝ s.direction = Module.finrank ℝ E := by
        have hdim' : (Module.finrank ℝ s.direction : ℤ) = (Module.finrank ℝ E : ℤ) := by
          simpa [Function.dim, s, Set.affineDim, AffineSubspace.affineDim, hs_ne_bot] using hdim
        exact_mod_cast hdim'
      have hs_direction_top : s.direction = ⊤ := Submodule.eq_top_of_finrank_eq hs_finrank
      exact (AffineSubspace.direction_eq_top_iff_of_nonempty hs_nonempty).1 hs_direction_top
  have hdim_formula :
      dim((f⋆ : E → WithTopBot ℝ)) = (Module.finrank ℝ E : ℤ) - lineality[ℝ](f) := by
    simpa using effectiveDomain_convexConjugate_affineDim_eq_ambientDim_sub_lineality f hf
  rw [hinterior_iff_dim, hdim_formula]
  omega

-- Proof sketch (source-facing bridge): rewrite the owner theorem above by the bundled Chapter 2
-- bridge `Function.IsClosedProperConvex.lineality_eq_zero_iff_not_exists_affineLine`.
/-- Corollary 13.4.2: a closed proper convex function has conjugate with finite domain of nonempty
interior if and only if there is no nontrivial affine line on which the function is finite and
affine. -/
theorem interior_dom_convexConjugate_nonempty_iff_not_exists_affineLine
    {f : E → WithTopBot ℝ} (hf : IsClosedProperConvex[ℝ] f) :
    (interior dom(f⋆)).Nonempty ↔
      ¬ ∃ y : E, y ≠ 0 ∧ ∃ x : E, x ∈ dom(f) ∧ ∀ t : ℝ, f (x + t • y) = f x := by
  rw [hf.interior_dom_convexConjugate_nonempty_iff_lineality_eq_zero]
  exact hf.lineality_eq_zero_iff_not_exists_affineLine

end Function.IsClosedProperConvex

end
