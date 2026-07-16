import Mathlib.Analysis.Calculus.Gradient.Basic
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap01.TopologicalAffineSpan
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_12
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_10_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Filter
open scoped Rockafellar
open scoped Gradient

namespace Function

universe u v

/-!
Source/core/bridge triage:

- `source-facing`: Definition 26.1.1 introduces essential smoothness of a proper convex
  `WithTopBot ℝ`-valued function, with the source set `C = interior dom(f)`.
- `core/canonical`: the owner declarations already present upstream are `dom(·)`,
  `Function.IsProper`, `Function.IsConvex`, `DifferentiableOn`, and the Fréchet-derivative owner
  `fderivWithin`, together with the filter statement
  `Tendsto _ (nhdsWithin x C) atTop`.
- `bridge/view`: the repeated `(a)(b)(c)` data over a set is factored as
  `Function.IsEssentiallySmoothOn C f₀` for an arbitrary scalar branch `f₀`; the textbook
  `f.IsEssentiallySmooth` keeps the textbook clause `(a)` (`interior dom(f)` nonempty) but stores
  the differential clauses on the intrinsic owner `C = riDom(f)` with `f₀ = f.realBranch`, while
  the ambient-gradient surface remains a bridge theorem under inner-product assumptions.

Domain-style sampling used here:
- `dom(·)` and `Function.IsProper` from Chapter 1;
- `Function.IsConvex` from Chapter 1;
- mathlib's `DifferentiableOn` and `fderivWithin`.

Primitive data vs derived API:
- primitive source-facing data: the proper convex function `f`, the interior nonemptiness clause,
  and the finite branch map used for differentiation on `riDom(f)`;
- primitive reusable owner data: nonemptiness, differentiability on the set, and boundary
  blow-up of the within-set Fréchet-derivative norm for a scalar-valued function on a set;
- derived API: the interior-nonempty, differentiability, and boundary-limit projections for the
  source owner `f.IsEssentiallySmooth`, together with the bridge to `interior dom(f)` and then to
  the ordinary gradient on `interior dom(f)`.

Layer target: `source-facing` for `Function.IsEssentiallySmooth`, with the canonical reusable owner
`Function.IsEssentiallySmoothOn` supplying the abstraction layer used by later Chapter 26
Legendre-type statements.
-/

section Core

variable {E : Type u} [SeminormedAddCommGroup E]

/-- The common `(a)(b)(c)` data from Definition 26.1.1 on a specified set `C`: nonemptiness,
differentiability on `C`, and divergence of the within-set Fréchet-derivative norm along `C`
toward each boundary point. -/
@[mk_iff]
class IsEssentiallySmoothOn {𝕜 : Type v} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
    (C : Set E) (f : E → 𝕜) : Prop where
  nonempty : C.Nonempty
  differentiableOn : DifferentiableOn 𝕜 f C
  boundaryFDerivWithinNorm_tendstoTop {x : E} (hx : x ∈ frontier C) :
      Tendsto (fun y : E ↦ ‖fderivWithin 𝕜 f C y‖) (nhdsWithin x C) atTop

/-- Definition 26.1.1 source-facing specialization:
a proper convex `WithTopBot ℝ`-valued function is essentially smooth when the canonical finite real
branch `f.realBranch` satisfies the intrinsic `riDom(f)` differentiability and boundary blow-up
conditions, together with nonempty `interior (dom(f))`. -/
@[mk_iff]
class IsEssentiallySmooth [NormedSpace ℝ E] (f : E → WithTopBot ℝ) :
    Prop extends IsEssentiallySmoothOn (riDom(f)) f.realBranch where
  interior_nonempty : (interior (dom(f))).Nonempty
  convex : f.IsConvex ℝ
  proper : f.IsProper

end Core

namespace IsEssentiallySmooth

section IntrinsicOwner

variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- Intrinsic-domain owner data carried by `f.IsEssentiallySmooth`. -/
theorem toIsEssentiallySmoothOn_riDom {f : E → WithTopBot ℝ}
    (hf : f.IsEssentiallySmooth) :
    IsEssentiallySmoothOn (riDom(f)) f.realBranch :=
  hf.toIsEssentiallySmoothOn

/-- Intrinsic-domain differentiability clause for Definition 26.1.1. -/
theorem differentiableOn_realBranch_riDom {f : E → WithTopBot ℝ}
    (hf : f.IsEssentiallySmooth) :
    DifferentiableOn ℝ f.realBranch (riDom(f)) :=
  hf.toIsEssentiallySmoothOn_riDom.differentiableOn

/-- Intrinsic restatement of condition (a): `riDom(f)` is nonempty. -/
theorem riDom_nonempty {f : E → WithTopBot ℝ} (hf : f.IsEssentiallySmooth) :
    (riDom(f)).Nonempty :=
  (hf.toIsEssentiallySmoothOn_riDom).nonempty

/-- Intrinsic restatement of condition (c): the within-`riDom(f)` Fréchet derivative norm blows up
at each boundary point of `riDom(f)`. -/
theorem boundaryFDerivWithinNorm_tendstoTop_riDom
    {f : E → WithTopBot ℝ} (hf : f.IsEssentiallySmooth)
    {x : E} (hx : x ∈ frontier (riDom(f))) :
    Tendsto (fun y : E ↦ ‖fderivWithin ℝ f.realBranch (riDom(f)) y‖)
      (nhdsWithin x (riDom(f))) atTop :=
  (hf.toIsEssentiallySmoothOn_riDom).boundaryFDerivWithinNorm_tendstoTop hx

end IntrinsicOwner

section InteriorBridge

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- For an essentially smooth convex function, the intrinsic domain owner `riDom(f)` coincides
with `interior (dom(f))`. -/
theorem riDom_eq_interior_dom {f : E → WithTopBot ℝ}
    (hf : f.IsEssentiallySmooth) :
    riDom(f) = interior (dom(f)) := by
  have hspan_int : affineSpan ℝ (interior (dom(f)) : Set E) = ⊤ :=
    IsOpen.affineSpan_eq_top_of_nontriviallyNormedField
      (𝕜 := ℝ) (V := E) (P := E) isOpen_interior hf.interior_nonempty
  have hmono :
      affineSpan ℝ (interior (dom(f)) : Set E) ≤ affineSpan ℝ dom(f) :=
    affineSpan_mono (k := ℝ) (V := E) (P := E)
      (s₁ := interior (dom(f))) (s₂ := dom(f)) interior_subset
  have hspan_dom : affineSpan ℝ dom(f) = ⊤ := by
    apply top_unique
    simpa [hspan_int] using hmono
  rw [riDom_real_eq_intrinsicInterior_dom,
    intrinsicInterior_eq_interior_of_affineSpan_eq_top hspan_dom]

/-- Source-owner bridge back to `interior (dom(f))`. -/
theorem toIsEssentiallySmoothOn_interior_dom {f : E → WithTopBot ℝ}
    (hf : f.IsEssentiallySmooth) :
    IsEssentiallySmoothOn (interior (dom(f))) f.realBranch := by
  simpa [hf.riDom_eq_interior_dom] using hf.toIsEssentiallySmoothOn

/-- Condition (b) of Definition 26.1.1. -/
theorem differentiableOn_realBranch {f : E → WithTopBot ℝ}
    (hf : f.IsEssentiallySmooth) :
    DifferentiableOn ℝ f.realBranch (interior (dom(f))) :=
  hf.toIsEssentiallySmoothOn_interior_dom.differentiableOn

end InteriorBridge

end IsEssentiallySmooth

namespace IsEssentiallySmoothOn

section InnerProductBridge

variable {𝕜 : Type v} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- On an open set, the within-set boundary blow-up clause is equivalent to the ambient-gradient
formulation used in Definition 26.1.1. -/
theorem boundaryGradientNorm_tendstoTop
    {C : Set E} {f : E → 𝕜} (hf : IsEssentiallySmoothOn C f) (hC : IsOpen C)
    {x : E} (hx : x ∈ frontier C) :
    Tendsto (fun y : E ↦ ‖∇ f y‖) (nhdsWithin x C) atTop := by
  have hgrad :
      (fun y : E ↦ ‖fderivWithin 𝕜 f C y‖) =ᶠ[nhdsWithin x C] (fun y : E ↦ ‖∇ f y‖) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hCy : C ∈ nhds y := hC.mem_nhds hy
    rw [fderivWithin_of_mem_nhds hCy, gradient]
    exact ((InnerProductSpace.toDual 𝕜 E).symm.norm_map (fderiv 𝕜 f y)).symm
  exact (hf.boundaryFDerivWithinNorm_tendstoTop hx).congr' hgrad

end InnerProductBridge

end IsEssentiallySmoothOn

namespace IsEssentiallySmooth

section InnerProductBridge

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Condition (c) in intrinsic form: the ambient-gradient norm blows up along `riDom(f)` at each
boundary point of the intrinsic domain owner. -/
theorem boundaryGradientNorm_tendstoTop_riDom {f : E → WithTopBot ℝ}
    (hf : f.IsEssentiallySmooth)
    {x : E} (hx : x ∈ frontier (riDom(f))) :
    Tendsto (fun y : E ↦ ‖∇ f.realBranch y‖)
      (nhdsWithin x (riDom(f))) atTop := by
  let hs : IsEssentiallySmoothOn (riDom(f)) f.realBranch := hf.toIsEssentiallySmoothOn_riDom
  have hri_open : IsOpen (riDom(f)) := by
    rw [hf.riDom_eq_interior_dom]
    exact isOpen_interior
  exact hs.boundaryGradientNorm_tendstoTop hri_open hx

/-- Condition (c) of Definition 26.1.1, in the source-facing ambient-gradient form on the open
set `interior (dom(f))`. -/
theorem boundaryGradientNorm_tendstoTop {f : E → WithTopBot ℝ} (hf : f.IsEssentiallySmooth)
    {x : E} (hx : x ∈ frontier (interior (dom(f)))) :
    Tendsto (fun y : E ↦ ‖∇ f.realBranch y‖)
      (nhdsWithin x (interior (dom(f)))) atTop := by
  let hs : IsEssentiallySmoothOn (interior (dom(f))) f.realBranch :=
    hf.toIsEssentiallySmoothOn_interior_dom
  exact hs.boundaryGradientNorm_tendstoTop isOpen_interior hx

end InnerProductBridge

end IsEssentiallySmooth

end Function
