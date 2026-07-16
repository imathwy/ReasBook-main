import Mathlib.Analysis.Calculus.Gradient.Basic
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6
import ConvexAnalysis_Rockafellar_1970.Chap05.Corollary_23_5_1
import ConvexAnalysis_Rockafellar_1970.Chap05.Corollary_25_1_2
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_25_1
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_26_0_3
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_5_24_3
import ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_23_5

noncomputable section

open scoped Gradient RealInnerProductSpace Rockafellar SetRel

universe u

section

variable {𝕜 : Type*}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {f : E → WithTopBot 𝕜}

local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)
local notation "fStarDual" => (f⋆ : StrongDual 𝕜 E → WithTopBot 𝕜)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 26.0.1 motivates the Legendre transformation for convex functions by
  pointing to two existing mathematical correspondences: Fenchel conjugacy `f ↦ f⋆` and the
  subdifferential multifunction `∂f`.
- `core/canonical`: the owner abstractions already present in the project are `convexConjugate`,
  `_root_.subdifferentialGraph`, the relation inverse `SetRel.inv`, the Chapter 26 one-to-one
  owner `SetRel.BiUnique`, and the Chapter 23 Fenchel-Young conjugacy owner theorem.
- `bridge/view`: the Euclidean self-dual graph view `Function.subdifferentialGraph` remains a
  Fréchet-Riesz bridge obtained after the intrinsic graph-inverse owner theorem below.

Domain-style sampling used here:
- `convexConjugate`;
- `_root_.subdifferentialGraph`;
- `Function.subdifferentialGraph`;
- `SetRel.inv`;
- `SetRel.BiUnique`;
- `Function.subdifferentialAt_tfae_isMaxOn_fenchelYoung_and_
  conjugate_subdifferentialAt_of_closure_eq`.

Primitive data vs derived API:
- primitive data: a closed proper convex function `f`, its intrinsic subdifferential graph
  relation, and relation inversion;
- derived bridge API: the Euclidean same-carrier graph view
  `Function.subdifferentialGraph`, and the differentiable value identity
  `f⋆(∇f(x)) = ⟪x, ∇f(x)⟫ - f(x)` for the canonical extension off an open convex domain.

Layer target:
- `core/canonical`: the intrinsic graph-inverse theorem on `_root_.subdifferentialGraph`;
- `bridge/view`: the Euclidean same-carrier graph theorem used by the later Chapter 26
  one-to-one bridge.
-/

/-- Text 26.0.1, intrinsic graph-owner form: for a closed proper convex function, the
subdifferential graph of the Fenchel conjugate is the inverse relation of the original
subdifferential graph. This is the canonical pairing-owner statement behind Legendre
correspondence. -/
theorem subdifferentialGraph_convexConjugate_eq_inv
    (hf : IsClosedProperConvex[𝕜] f) :
    gph∂[E](fStarDual) = (gph∂(f)).inv := by
  ext p
  rcases p with ⟨xStar, x⟩
  constructor
  · intro hp
    have hsub : x ∈ ∂[E]fStarDual(xStar) :=
      _root_.mem_subdifferentialGraph.mp hp
    have hsub' : xStar ∈ ∂ f at x :=
      (Function.IsClosedProperConvex.mem_subdifferentialAt_convexConjugate_iff
        (f := f) (x := x) (xStar := xStar) hf).1 hsub
    exact
      (SetRel.mem_inv (R := gph∂(f)) (a := x) (b := xStar)).2
        (_root_.mem_subdifferentialGraph.mpr hsub')
  · intro hp
    have hgraph : (x, xStar) ∈ gph∂(f) :=
      (SetRel.mem_inv (R := gph∂(f)) (a := x) (b := xStar)).1 hp
    have hsub : xStar ∈ ∂ f at x :=
      _root_.mem_subdifferentialGraph.mp hgraph
    have hsub' : x ∈ ∂[E]fStarDual(xStar) :=
      (Function.IsClosedProperConvex.mem_subdifferentialAt_convexConjugate_iff
        (f := f) (x := x) (xStar := xStar) hf).2 hsub
    exact _root_.mem_subdifferentialGraph.mpr hsub'

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 26.0.1 motivates the Legendre transformation for convex functions by
  pointing to two existing mathematical correspondences: Fenchel conjugacy `f ↦ f⋆` and the
  subdifferential multifunction `∂f`.
- `core/canonical`: the owner abstractions already present in the project are `convexConjugate`,
  `_root_.subdifferentialGraph`, `Function.subdifferentialGraph`, the relation inverse
  `SetRel.inv`, the Chapter 26 one-to-one owner `SetRel.BiUnique`, and the Chapter 23
  Fenchel-Young conjugacy owner theorem.
- `bridge/view`: the declaration below records the Euclidean graph-inverse identity underlying the
  classical Legendre correspondence; projection-injectivity and one-to-one consequences are then
  derived from the existing `SetRel` owner API rather than introduced as a parallel root theorem.

Domain-style sampling used here:
- `convexConjugate`;
- `_root_.subdifferentialGraph`;
- `Function.subdifferentialGraph`;
- `SetRel.inv`;
- `SetRel.BiUnique`;
- `Function.subdifferentialAt_tfae_isMaxOn_fenchelYoung_and_
  conjugate_subdifferentialAt_of_closure_eq`.

Primitive data vs derived API:
- primitive data: a closed proper convex function `f`, its intrinsic subdifferential graph
  relation, its Euclidean graph view `Function.subdifferentialGraph f`, and the inverse relation
  on that Euclidean graph;
- derived API: the one-to-one and projection-uniqueness consequences obtained from the graph
  inverse identity, and the differentiable value identity
  `f⋆(∇f(x)) = ⟪x, ∇f(x)⟫ - f(x)` for the canonical extension off an open convex domain.

Layer target: `bridge/view`. This introductory text does not own a new construction; it reuses the
chapter owners for conjugacy, subdifferentials, relation inversion, and multivalued-map
uniqueness.

Ambient refinement:
- the conjugacy side uses `f⋆` with the chapter's inner-product self-pairing on `E`, but the
  owner statement below is expressed on the same-carrier Euclidean graph view
  `Function.subdifferentialGraph`, where relation inversion has the correct type.
-/

/- Text 26.0.1 is organized around the chapter's Fenchel-conjugacy owner. -/
#check convexConjugate

/- Text 26.0.1 treats multivalued mappings through the canonical relation inverse. -/
#check SetRel.inv

/- Text 26.0.1 treats one-to-one multivalued mappings through the canonical relation owner. -/
#check SetRel.BiUnique

/- Text 26.0.1 treats subdifferential mappings through the intrinsic graph owner. -/
#check _root_.subdifferentialGraph

/- Text 26.0.1 treats the Euclidean self-dual graph view through `Function.subdifferentialGraph`. -/
#check Function.subdifferentialGraph
namespace Function

/-- Text 26.0.1, Euclidean graph-owner bridge: for a closed proper convex function, the
vector-valued subdifferential graph of the Fenchel conjugate is the inverse relation of the
vector-valued subdifferential graph of `f`. This is the same-carrier bridge statement from which
the chapter's projection-injectivity and one-to-one formulations are derived. -/
theorem subdifferentialGraph_convexConjugate_eq_inv
    {f : E → WithTopBot ℝ} (hf : f.IsClosedProperConvex) :
    subdifferentialGraph (f⋆ : E → WithTopBot ℝ) = (subdifferentialGraph f).inv := by
  ext p
  rcases p with ⟨x, xStar⟩
  have hcl : cl(f) xStar = f xStar := by
    simpa using congrFun (lowerSemicontinuousHull_eq_self hf.closed) xStar
  have hiff :
      xStar ∈ ∂ᵥ(f⋆ : E → WithTopBot ℝ)(x) ↔ x ∈ ∂ᵥf(xStar) :=
    (subdifferentialAt_tfae_isMaxOn_fenchelYoung_and_conjugate_subdifferentialAt_of_closure_eq
      (f := f) (x := xStar) (xStar := x) hf.convex hf.proper hcl).out 4 0
  constructor
  · intro hx
    have hsub : x ∈ ∂ᵥf(xStar) := hiff.1 (Function.mem_subdifferentialGraph.mp hx)
    have hgraph : xStar ~[subdifferentialGraph f] x :=
      Function.mem_subdifferentialGraph.mpr hsub
    change (xStar, x) ∈ subdifferentialGraph f
    exact hgraph
  · intro hx
    have hgraph : xStar ~[subdifferentialGraph f] x := by
      change (xStar, x) ∈ subdifferentialGraph f at hx
      exact hx
    have hsub : x ∈ ∂ᵥf(xStar) :=
      Function.mem_subdifferentialGraph.mp hgraph
    exact Function.mem_subdifferentialGraph.mpr (hiff.2 hsub)

end Function

end

section

variable {𝕜 : Type*}
variable [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace Function

variable {U : Set E} {f : E → 𝕜}

local notation "fExt" => Function.toWithTopBotOn f U

/-- Text 26.0.1, intrinsic owner-level differentiable value formula: at a relative-interior point
`x ∈ ri[𝕜](U)` of a convex branch, the Fenchel conjugate of the canonical extension
`Function.toWithTopBotOn f U`, evaluated at the Fréchet derivative owner `fderiv 𝕜 f x`, is the
affine defect `(fderiv 𝕜 f x) x - f x`. -/
theorem convexConjugate_toWithTopBotOn_fderiv_eq_apply_sub
    (hf_convex : ConvexOn 𝕜 U f)
    {x : E} (hx : x ∈ ri[𝕜](U)) (hfdx : DifferentiableAt 𝕜 f x) :
    fExt⋆ (fderiv 𝕜 f x) = (((fderiv 𝕜 f x) x - f x : 𝕜) : WithTopBot 𝕜) := by
  have hsub : ∂ᵣf(x | U) = {fderiv 𝕜 f x} :=
    subdifferentialWithinAt_eq_singleton_fderiv
      (hf_convex := hf_convex) (x := x) (hx := hx)
      (hfdx := hfdx.hasFDerivAt)
  have hmem : fderiv 𝕜 f x ∈ ∂ᵣf(x | U) := by
    simp [hsub]
  have hvalue :=
    convexConjugate_eq_apply_sub_of_mem_subdifferentialWithinAt
      (f := f) (U := U) (x := x)
      (xStar := fderiv 𝕜 f x) (intrinsicInterior_subset hx) hmem
  have hpair : (⟪x, fderiv 𝕜 f x⟫ₚ : 𝕜) = (fderiv 𝕜 f x) x := rfl
  calc
    fExt⋆ (fderiv 𝕜 f x) = (((⟪x, fderiv 𝕜 f x⟫ₚ - f x : 𝕜)) : WithTopBot 𝕜) :=
      hvalue
    _ = (((fderiv 𝕜 f x) x - f x : 𝕜) : WithTopBot 𝕜) := by rw [hpair]

/-- Text 26.0.1, open-set bridge form: on an open convex set `U`, the same value identity as
`convexConjugate_toWithTopBotOn_fderiv_eq_apply_sub` can be stated using `fderivWithin 𝕜 f U x`. -/
theorem convexConjugate_toWithTopBotOn_fderivWithin_eq_apply_sub
    (hU_open : IsOpen U) (hf_convex : ConvexOn 𝕜 U f)
    {x : E} (hx : x ∈ U) (hfdx : DifferentiableAt 𝕜 f x) :
    fExt⋆ (fderivWithin 𝕜 f U x) = (((fderivWithin 𝕜 f U x) x - f x : 𝕜) : WithTopBot 𝕜) := by
  have hx_int : x ∈ interior U := mem_interior_iff_mem_nhds.2 (hU_open.mem_nhds hx)
  have hx_ri : x ∈ ri[𝕜](U) := interior_subset_intrinsicInterior (𝕜 := 𝕜) hx_int
  have hfd_within : fderivWithin 𝕜 f U x = fderiv 𝕜 f x :=
    fderivWithin_of_isOpen hU_open hx
  simpa [hfd_within] using
    (convexConjugate_toWithTopBotOn_fderiv_eq_apply_sub
      (hf_convex := hf_convex) (x := x) (hx := hx_ri) (hfdx := hfdx))

end Function

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace Function

variable {U : Set E} {f : E → ℝ}

local notation "fExt" => Function.toWithTopBotOn f U

/-- Text 26.0.1, differentiable Legendre-value formula: on the differentiability locus of the
canonical extension `Function.toWithTopBotOn f U`, the Fenchel conjugate evaluated at the
gradient is the classical affine defect `⟪x, ∇ f x⟫ - f x`. This is the single-valued branch
of the subdifferential correspondence used in the Legendre transformation discussion, obtained by
the Fréchet-Riesz bridge from the derivative-owner theorem above. -/
theorem convexConjugate_toWithTopBotOn_gradient_eq_inner_sub
    (hf_convex : ConvexOn ℝ U f)
    {x : E} (hx : x ∈ ri[ℝ](U)) (hfdx : DifferentiableAt ℝ f x) :
    fExt⋆ (∇ f x) = ((⟪x, ∇ f x⟫ - f x : ℝ) : WithTopBot ℝ) := by
  have hgrad_mem_vec : ∇ f x ∈ ∂ᵥᵣf(x | U) := by
    have hsub : ∂ᵥᵣf(x | U) = {∇ f x} :=
      Function.subdifferentialWithinAt_eq_singleton_gradient
        (hf_convex := hf_convex) (x := x)
        (hx := hx) (hfdx := hfdx)
    simp [hsub]
  have hgrad_mem : ∇ f x ∈ ∂ᵣ[E]f(x | U) := by
    rw [_root_.mem_subdifferentialWithinAt_pairing]
    intro z
    change
      Function.toWithTopBotOn f U z ≥
        Function.toWithTopBotOn f U x + ((⟪z - x, ∇ f x⟫ₚ : ℝ) : WithTopBot ℝ)
    have hz :
        Function.toWithTopBotOn f U z ≥
          Function.toWithTopBotOn f U x + ((inner ℝ (∇ f x) (z - x) : ℝ) : WithTopBot ℝ) :=
      (Function.mem_subdifferentialWithinAt
        (f := f) (U := U) (x := x) (g := ∇ f x)).1 hgrad_mem_vec z
    have hswap_pair : (⟪∇ f x, z - x⟫ : ℝ) = (⟪z - x, ∇ f x⟫ₚ : ℝ) := by
      change inner ℝ (∇ f x) (z - x) = inner ℝ (z - x) (∇ f x)
      simp [real_inner_comm]
    simpa [hswap_pair] using hz
  simpa using
    (convexConjugate_eq_apply_sub_of_mem_subdifferentialWithinAt
      (f := f) (U := U) (x := x) (xStar := ∇ f x)
      (intrinsicInterior_subset hx) hgrad_mem)

end Function

end
