import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u}
variable [AddCommMonoid E] [SMul ℝ E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.1.2 says that the pointwise power `h(x) = f(x)^p` is convex when `f` is
  convex, nonnegative, and `p > 1`.
- `core/canonical`: the owner abstraction for finite real-valued convex functions is mathlib's
  `ConvexOn ℝ s f`; at this owner layer the primitive exponent bound is `1 ≤ p`, and the proof
  uses the Jensen field of `ConvexOn` together with the canonical outer-map owners
  `convexOn_rpow` and `Real.monotoneOn_rpow_Ici_of_exponent_nonneg`.
- `bridge/view`: the companion theorem `ConvexOn.rpow_of_one_lt` recovers the source wording
  `p > 1` from the canonical owner theorem `ConvexOn.rpow`.

Domain-style sampling used here:
- `ConvexOn` from `Mathlib/Analysis/Convex/Function.lean`;
- `convexOn_rpow` from `Mathlib/Analysis/Convex/SpecificFunctions/Basic.lean`;
- `Real.monotoneOn_rpow_Ici_of_exponent_nonneg` from
  `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean`.

Primitive data vs derived API:
- primitive inputs: a convex real-valued branch `f : E → ℝ` on `s`, pointwise nonnegativity on
  `s` as `∀ x ∈ s, 0 ≤ f x`, and an exponent `p`;
- derived output: convexity of the pointwise power `fun x ↦ f x ^ p`.

Layer target: `core/canonical`, with the owner theorem stated directly on `ConvexOn` at the
primitive exponent threshold `1 ≤ p`; the strict source inequality `p > 1` is kept as a thin
companion bridge.
-/

namespace ConvexOn

-- Proof sketch: use the outer map `x ↦ x ^ p` on `Ici 0`. For `p ≥ 1`, mathlib gives convexity
-- of this outer map on `Ici 0`, and it is monotone there for every nonnegative exponent.
-- Convexity of `f` gives
-- `f (a • x + b • y) ≤ a * f x + b * f y`; monotonicity of `x ↦ x ^ p` on `Ici 0` transports
-- this inequality, and convexity of `x ↦ x ^ p` yields the final Jensen inequality.
/-- Canonical owner form behind Text 5.1.2: on `ConvexOn`, the same argument extends to the
endpoint `p = 1`, so nonnegative convex functions remain convex after taking the pointwise
`p`-power for every exponent `p ≥ 1`. -/
theorem rpow {s : Set E} {f : E → ℝ} {p : ℝ}
    (hf : ConvexOn ℝ s f) (hfs : Set.MapsTo f s (Set.Ici 0)) (hp : 1 ≤ p) :
    ConvexOn ℝ s (fun x ↦ f x ^ p) := by
  have hp_nonneg : 0 ≤ p := le_trans (by norm_num : (0 : ℝ) ≤ 1) hp
  have hpow : ConvexOn ℝ (Set.Ici 0) (fun t : ℝ ↦ t ^ p) := convexOn_rpow hp
  have hmono : MonotoneOn (fun t : ℝ ↦ t ^ p) (Set.Ici 0) :=
    Real.monotoneOn_rpow_Ici_of_exponent_nonneg hp_nonneg
  refine ⟨hf.1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hx_nonneg : 0 ≤ f x := hfs hx
  have hy_nonneg : 0 ≤ f y := hfs hy
  have hxy_nonneg : 0 ≤ f (a • x + b • y) := hfs (hf.1 hx hy ha hb hab)
  have hcomb_nonneg : 0 ≤ a * f x + b * f y :=
    add_nonneg (mul_nonneg ha hx_nonneg) (mul_nonneg hb hy_nonneg)
  have hxy_le : f (a • x + b • y) ≤ a * f x + b * f y := by
    simpa [smul_eq_mul] using hf.2 hx hy ha hb hab
  calc
    f (a • x + b • y) ^ p ≤ (a * f x + b * f y) ^ p :=
      hmono hxy_nonneg hcomb_nonneg hxy_le
    _ ≤ a * (f x ^ p) + b * (f y ^ p) := by
      simpa [smul_eq_mul] using hpow.2 hx_nonneg hy_nonneg ha hb hab

/-- Text 5.1.2: if a real-valued function is convex and nonnegative on a convex set, then its
pointwise `p`-power is convex for every exponent `p > 1`. -/
theorem rpow_of_one_lt {s : Set E} {f : E → ℝ} {p : ℝ}
    (hf : ConvexOn ℝ s f) (hf₀ : ∀ x ∈ s, 0 ≤ f x) (hp : 1 < p) :
    ConvexOn ℝ s (fun x ↦ f x ^ p) :=
  hf.rpow (fun x hx ↦ hf₀ x hx) hp.le

end ConvexOn

end
