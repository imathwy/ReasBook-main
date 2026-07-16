import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap05.Text_26_0_1

noncomputable section

open scoped Rockafellar

universe u v

section

variable {𝕜 : Type v}
variable [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {C : Set E} {f : E → 𝕜}
local notation "fExt" => Function.toWithTopBotOn f C
local notation "riC" => ri[𝕜](C)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 26.4.0.2 says that, after extending a convex scalar-valued function on an
  open convex set `C` by `+∞` outside `C`, the Legendre-side values are obtained from the ordinary
  Fenchel conjugate of that canonical extension.
- `core/canonical`: the live owner abstractions already present upstream are the Chapter 3 Fenchel
  conjugate `convexConjugate`, the Chapter 1 effective-domain owner `dom(·)`, and the
  derivative value formulas
  `Function.convexConjugate_toWithTopBotOn_fderiv_eq_apply_sub` and
  `Function.convexConjugate_toWithTopBotOn_fderivWithin_eq_apply_sub`.
- `bridge/view`: this file does not introduce a second Legendre-transform owner. It records the
  intrinsic-interior (`ri[𝕜](C)`) and open-set (`C`) image-factorization/domain consequences on
  the canonical `WithTopBot` owner, together with their `Set.MapsTo`/image reformulations.

Domain-style sampling used here:
- `convexConjugate` from Chapter 3;
- `Function.convexConjugate_toWithTopBotOn_fderiv_eq_apply_sub`;
- `Function.convexConjugate_toWithTopBotOn_fderivWithin_eq_apply_sub`;
- `dom(·)` and `mem_effectiveDomain` from `Chap01.Definition_4_4`.

Primitive data vs derived API:
- primitive data: the open convex set `C`, the convex branch `f`, and its canonical extension
  `Function.toWithTopBotOn f C`;
- primitive owner surface: the Fenchel conjugate `(Function.toWithTopBotOn f C)⋆`;
- derived API: the image-factorization `WithTopBot`-valued derivative formula and the
  pointwise/map/image finiteness theorems on `dom((Function.toWithTopBotOn f C)⋆)`.

Layer target: `bridge/view`. The text is about derivative-image/value and finiteness views of the
existing Fenchel-conjugate owner, not about introducing a second root owner.
-/

/- Text 26.4.0.2 uses the ambient Fenchel conjugate of the canonical extension. -/
#check convexConjugate

/- Text 26.0.1 already provides the derivative-value formulas used below. -/

namespace Function

/-- Canonical `toWithTopBotOn`-spelled intrinsic-interior image-factorization corollary. -/
theorem convexConjugate_toWithTopBotOn_imageFactorization_intrinsicInterior_eq_apply_sub
    (hf_convex : ConvexOn 𝕜 C f) (x : riC) (hfdx : DifferentiableAt 𝕜 f x) :
    (fExt⋆) (↑(riC.imageFactorization (fderiv 𝕜 f) x) : StrongDual 𝕜 E) =
      (((fderiv 𝕜 f x) x - f x : 𝕜) : WithTopBot 𝕜) := by
  simpa [Set.imageFactorization] using
    (convexConjugate_toWithTopBotOn_fderiv_eq_apply_sub
      (hf_convex := hf_convex) (x := x) (hx := x.2) (hfdx := hfdx))

/-- Canonical `toWithTopBotOn`-spelled open-set image-factorization corollary. -/
theorem convexConjugate_toWithTopBotOn_imageFactorization_eq_apply_sub
    (hC_open : IsOpen C) (hf_convex : ConvexOn 𝕜 C f)
    (x : C) (hfdx : DifferentiableAt 𝕜 f x) :
    (fExt⋆) (↑(C.imageFactorization (fderivWithin 𝕜 f C) x) : StrongDual 𝕜 E) =
      (((fderivWithin 𝕜 f C x) x - f x : 𝕜) : WithTopBot 𝕜) := by
  simpa [Set.imageFactorization] using
    (convexConjugate_toWithTopBotOn_fderivWithin_eq_apply_sub
      (hC_open := hC_open) (hf_convex := hf_convex) (hx := x.2) (hfdx := hfdx))

/-- Canonical `toWithTopBotOn`-spelled intrinsic-interior pointwise domain consequence. -/
theorem mem_dom_convexConjugate_toWithTopBotOn_fderiv
    (hf_convex : ConvexOn 𝕜 C f)
    {x : E} (hx : x ∈ riC) (hfdx : DifferentiableAt 𝕜 f x) :
    fderiv 𝕜 f x ∈ dom(fExt⋆) := by
  rw [mem_effectiveDomain]
  rw [convexConjugate_toWithTopBotOn_fderiv_eq_apply_sub
      (hf_convex := hf_convex) (hx := hx) (hfdx := hfdx)]
  exact WithTopBot.coe_lt_top _

/-- Canonical `toWithTopBotOn`-spelled open-set pointwise domain consequence. -/
theorem mem_dom_convexConjugate_toWithTopBotOn_fderivWithin
    (hC_open : IsOpen C) (hf_convex : ConvexOn 𝕜 C f)
    {x : E} (hx : x ∈ C) (hfdx : DifferentiableAt 𝕜 f x) :
    fderivWithin 𝕜 f C x ∈ dom(fExt⋆) := by
  have hxri : x ∈ riC := by
    exact interior_subset_intrinsicInterior (𝕜 := 𝕜)
      (mem_interior_iff_mem_nhds.2 (hC_open.mem_nhds hx))
  have hmem : fderiv 𝕜 f x ∈ dom(fExt⋆) :=
    mem_dom_convexConjugate_toWithTopBotOn_fderiv
      (hf_convex := hf_convex) (hx := hxri) (hfdx := hfdx)
  simpa [fderivWithin_of_isOpen hC_open hx] using hmem

/-- Canonical `toWithTopBotOn`-spelled intrinsic-interior map-owner reformulation. -/
theorem mapsTo_fderiv_dom_convexConjugate_toWithTopBotOn_intrinsicInterior
    (hf_convex : ConvexOn 𝕜 C f)
    (hfd : ∀ x ∈ riC, DifferentiableAt 𝕜 f x) :
    Set.MapsTo (fderiv 𝕜 f) riC (dom(fExt⋆)) := by
  intro x hx
  exact mem_dom_convexConjugate_toWithTopBotOn_fderiv
    (hf_convex := hf_convex) (hx := hx) (hfdx := hfd x hx)

/-- Canonical `toWithTopBotOn`-spelled open-set map-owner reformulation. -/
theorem mapsTo_fderivWithin_dom_convexConjugate_toWithTopBotOn
    (hC_open : IsOpen C) (hf_convex : ConvexOn 𝕜 C f) (hfd : DifferentiableOn 𝕜 f C) :
    Set.MapsTo (fderivWithin 𝕜 f C) C (dom(fExt⋆)) := by
  intro x hx
  exact mem_dom_convexConjugate_toWithTopBotOn_fderivWithin
    (hC_open := hC_open) (hf_convex := hf_convex) (hx := hx)
    (hfdx := (hfd x hx).differentiableAt (hC_open.mem_nhds hx))

/-- Canonical `toWithTopBotOn`-spelled intrinsic-interior image-subset corollary. -/
theorem image_fderiv_subset_dom_convexConjugate_toWithTopBotOn_intrinsicInterior
    (hf_convex : ConvexOn 𝕜 C f)
    (hfd : ∀ x ∈ riC, DifferentiableAt 𝕜 f x) :
    (fderiv 𝕜 f) '' riC ⊆ dom(fExt⋆) := by
  intro xStar hxStar
  rcases hxStar with ⟨x, hx, rfl⟩
  exact mapsTo_fderiv_dom_convexConjugate_toWithTopBotOn_intrinsicInterior
    (hf_convex := hf_convex) (hfd := hfd) hx

/-- Canonical `toWithTopBotOn`-spelled open-set image-subset corollary. -/
theorem image_fderivWithin_subset_dom_convexConjugate_toWithTopBotOn
    (hC_open : IsOpen C) (hf_convex : ConvexOn 𝕜 C f) (hfd : DifferentiableOn 𝕜 f C) :
    (fderivWithin 𝕜 f C) '' C ⊆ dom(fExt⋆) := by
  intro xStar hxStar
  rcases hxStar with ⟨x, hx, rfl⟩
  exact mapsTo_fderivWithin_dom_convexConjugate_toWithTopBotOn
    (hC_open := hC_open) (hf_convex := hf_convex) (hfd := hfd) hx

end Function

end
