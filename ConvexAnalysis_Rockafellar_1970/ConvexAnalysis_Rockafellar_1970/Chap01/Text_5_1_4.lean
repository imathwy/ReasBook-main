import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {𝕜 : Type v} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: the example states that the reciprocal of a concave scalar-valued function is
  convex on the region where the function is positive.
- `core/canonical`: the natural owner layer is mathlib's set-based pair `ConcaveOn` / `ConvexOn`;
  no project-local wrapper is needed.
- `bridge/view`: the reciprocal map is the scalar convex outer function on `(0, +∞)`, and the
  source domain `C = {x ∈ s | g(x) > 0}` is recorded literally as the positive locus of `g`
  inside the ambient set `s`.

Domain-style sampling used here:
- `ConcaveOn` and `ConvexOn` from mathlib's convex-function API;
- `convexOn_zpow (-1)` for convexity of the reciprocal on `(0, +∞)`;
- `one_div_strictAntiOn` for monotonicity of the reciprocal on positive scalars.
-/

-- Proof sketch: on `(0, +∞)` the reciprocal map is convex and antitone. On
-- `{x ∈ s | 0 < g x}`, concavity of `g` gives
-- `a • g x + b • g y ≤ g (a • x + b • y)`, so antitonicity gives the first reciprocal inequality,
-- and convexity of the reciprocal gives the second inequality.
namespace ConcaveOn

/-- Text 5.1.4 (set-parametric form): if `g` is concave on `s`, then `x ↦ 1 / g x` is convex on
the positive locus `s ∩ {x | 0 < g x}`. -/
theorem one_div {s : Set E} {g : E → 𝕜} (hg : ConcaveOn 𝕜 s g) :
    ConvexOn 𝕜 (s ∩ {x | 0 < g x}) (fun x ↦ 1 / g x) := by
  let t : Set E := s ∩ {x | 0 < g x}
  have hconv_one_div : ConvexOn 𝕜 (Set.Ioi (0 : 𝕜)) (fun t : 𝕜 ↦ 1 / t) := by
    simpa [one_div, zpow_neg_one] using
      (convexOn_zpow (-1 : ℤ) :
        ConvexOn 𝕜 (Set.Ioi (0 : 𝕜)) (fun t : 𝕜 ↦ t ^ (-1 : ℤ)))
  have hanti_one_div : AntitoneOn (fun t : 𝕜 ↦ 1 / t) (Set.Ioi (0 : 𝕜)) :=
    one_div_strictAntiOn.antitoneOn
  have ht_subset : t ⊆ s := by
    intro x hx
    exact hx.1
  have ht_convex : Convex 𝕜 t := by
    intro x hx y hy a b ha hb hab
    refine ⟨hg.1 hx.1 hy.1 ha hb hab, ?_⟩
    have hcombo_pos : 0 < a • g x + b • g y := by
      exact (convex_Ioi (0 : 𝕜)) hx.2 hy.2 ha hb hab
    have hconc : a • g x + b • g y ≤ g (a • x + b • y) := hg.2 hx.1 hy.1 ha hb hab
    exact lt_of_lt_of_le hcombo_pos hconc
  have hg_t : ConcaveOn 𝕜 t g := hg.subset ht_subset ht_convex
  refine ⟨ht_convex, ?_⟩
  intro x hx y hy a b ha hb hab
  have hx_pos : 0 < g x := hx.2
  have hy_pos : 0 < g y := hy.2
  have hcombo_pos : 0 < a • g x + b • g y :=
    (convex_Ioi (0 : 𝕜)) hx_pos hy_pos ha hb hab
  have hz_pos : 0 < g (a • x + b • y) := (ht_convex hx hy ha hb hab).2
  have hconc : a • g x + b • g y ≤ g (a • x + b • y) := hg_t.2 hx hy ha hb hab
  have hrecip_le :
      1 / g (a • x + b • y) ≤ 1 / (a • g x + b • g y) :=
    hanti_one_div hcombo_pos hz_pos hconc
  calc
    1 / g (a • x + b • y) ≤ 1 / (a • g x + b • g y) := hrecip_le
    _ ≤ a • (1 / g x) + b • (1 / g y) := hconv_one_div.2 hx_pos hy_pos ha hb hab

end ConcaveOn

end
