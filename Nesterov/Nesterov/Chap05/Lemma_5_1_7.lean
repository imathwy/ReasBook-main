import Mathlib
import Nesterov.Chap03.Definition_3_3
import Nesterov.Chap05.Definition_5_0_13
import Nesterov.Chap05.Definition_5_0_20
import Nesterov.Chap05.Theorem_5_1_17

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open scoped ConvexAnalysis DikinEllipsoidNotation Gradient MatrixOrder WithTopConvexAnalysis

noncomputable section

universe u

/- Lemma 5.1.7 lies in the Chapter 5 Fenchel-conjugacy / self-concordant Hessian-comparison
domain.

Sampled owner-style declarations in this domain:
* `HessianDualLocalNorm.ofPosDefMem` in `Definition_5_0_20`, the chapter owner for the dual local
  norm `‖·‖*` attached to a positive-definite Hessian on a domain;
* `HessianDualLocalNorm.ofSelfConcordantMem` in `Definition_5_0_20`, the owner-layer bridge/view
  that reads the same owner
  under the standing primal self-concordant hypotheses of Section 5.1.5;
* `HasPositiveDefiniteHessianOn` in `Definition_5_0_23`, the canonical owner for positive-definite
  primal Hessians on a domain;
* `fenchelPrimalExtension` together with `F⋆`, `dom (F⋆)`, and
  `extendedRealRealPart (F⋆)` from `FenchelPrimalExtension` / `Theorem_5_1_17`, the canonical
  owner surface for the primal/dual pair;
* `IsSelfConcordantOnWith.hessian_loewner_bounds_of_mem_openDikinEllipsoid` in
  `Proposition_5_0_15`, the owner-level Hessian comparison theorem on a self-concordant domain.

Best owner abstraction:
* source-facing: the conjugate-induced primal Hessian comparison under the standing primal
  self-concordant hypotheses, with primitive smallness datum
  `d = ‖∇ f x - ∇ f y‖*[f; x]`;
* core/canonical: `F := fenchelPrimalExtension domain f`, the dual owner
  `extendedRealRealPart (F⋆)` on `dom (F⋆)`, the positive-definite-Hessian owner
  `HasPositiveDefiniteHessianOn domain f`, the dual local norm
  `HessianDualLocalNorm.ofPosDefMem f hx`, and the intrinsic Hessian owner `hessian f`;
* bridge/view: `HessianDualLocalNorm.ofSelfConcordantMem`, the owner-layer dual-local-norm bridge,
  the dual self-concordance owner on
  `extendedRealRealPart (F⋆)`, the dual open-Dikin condition, and the Euclidean matrix
  realization `∇² f`.

Primitive data:
* a domain `domain`, a real-valued primal function `f`, and points `x y ∈ domain`;
* self-concordance of `f` on `domain` with parameter `M_f`;
* closedness of the constrained epigraph of `f` over `domain`;
* the no-affine-line hypothesis on `domain`;
* the source-defined quantity
  `d = ‖∇ f x - ∇ f y‖*[f; x]` together with the smallness hypothesis `d < 1 / M_f`.

Derived API:
* `HessianDualLocalNorm.ofSelfConcordantMem`, which packages the derived dual local norm from the
  standing primal hypotheses;
* dual self-concordance of `extendedRealRealPart (F⋆)` and gradient-domain membership
  `∇ f x, ∇ f y ∈ dom (F⋆)` obtained from `Theorem_5_1_17` and `Lemma_5_1_6`;
* the dual open-Dikin reformulation of the `d`-smallness condition;
* the Loewner-order comparison of `hessian f x` and `hessian f y`;
* the Euclidean matrix comparison as a thin view theorem.

Source/core/bridge triage:
* source-facing: the conjugate-induced Hessian comparison stated with the dual local norm `d` and
  the standing primal hypotheses of Section 5.1.5;
* core/canonical: `fenchelPrimalExtension domain f`, `extendedRealRealPart (F⋆)`,
  `HasPositiveDefiniteHessianOn domain f`, `HessianDualLocalNorm.ofPosDefMem`, and `hessian`;
* bridge/view: `HessianDualLocalNorm.ofSelfConcordantMem`, the dual-owner comparison theorem,
  the dual open-Dikin reformulation, and the Euclidean matrix theorem.

The previous version made a dual-owner bridge theorem the main public entry and thereby dropped
nonredundant primal assumptions still needed by the inverse-Hessian conjugacy bridge in this
project. This refinement restores the source-facing main theorem on the standing primal
self-concordant hypotheses, keeps the source quantity `d` on the theorem surface via the
owner-layer bridge `HessianDualLocalNorm.ofSelfConcordantMem`, and keeps the dual-owner
comparison only as internal bridge data. -/

section OwnerLevel

variable {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
variable [FiniteDimensional ℝ X]

variable {domain : Set X} {Mf : NNReal} {f : X → ℝ} {x y : X}

local notation "F" => fenchelPrimalExtension domain f

local instance finiteDimensionalComplete : CompleteSpace X := FiniteDimensional.complete ℝ X

-- Proof sketch: let
-- `d := HessianDualLocalNorm.ofPosDefMem f hx ((toDual ℝ X) (∇ f x - ∇ f y))`. The identity
-- `∇² (extendedRealRealPart (F⋆)) (∇ f x) = (hessian f x)⁻¹` from Fenchel conjugacy identifies
-- `d` with the local norm of the dual displacement `∇ f x - ∇ f y` for the dual objective
-- `extendedRealRealPart (F⋆)` at `∇ f x`, provided `∇ f x ∈ dom (F⋆)`. The smallness hypothesis
-- `d < 1 / M_f` is therefore exactly the dual Dikin condition needed to apply the canonical
-- Hessian comparison theorem on the self-concordant dual owner `extendedRealRealPart (F⋆)`.
-- The extra bridge hypothesis `∇ f y ∈ dom (F⋆)` is then what lets the inverse-Hessian transfer
-- identify the dual Hessian at the endpoint `∇ f y` with `(hessian f y)⁻¹`. Transporting that
-- dual comparison back across inversion yields the displayed primal Loewner-order bounds.
private theorem dualRealPart_hessian_loewner_bounds
    [HasPositiveDefiniteHessianOn domain f]
    (hdual : IsSelfConcordantOnWith (dom (F⋆)) Mf (extendedRealRealPart (F⋆)))
    (hx : x ∈ domain) (hy : y ∈ domain)
    (hgradx : ∇ f x ∈ dom (F⋆)) (hgrady : ∇ f y ∈ dom (F⋆))
    (d : ℝ)
    (hd : d = HessianDualLocalNorm.ofPosDefMem f hx ((toDual ℝ X) (∇ f x - ∇ f y)))
    (hd_lt : d < 1 / (Mf : ℝ)) :
    ((1 - (Mf : ℝ) * d) ^ (2 : ℕ)) • hessian f x ≤ hessian f y ∧
      hessian f y ≤ ((1 - (Mf : ℝ) * d) ^ (2 : ℕ))⁻¹ • hessian f x := by
  let _ := hdual
  sorry

-- Proof sketch: derive the positive-definite-Hessian owner on `domain` from the standing primal
-- assumptions via `IsSelfConcordantOn.hasPositiveDefiniteHessianOn_of_no_affine_line`, derive dual
-- self-concordance of `extendedRealRealPart (F⋆)` via
-- `fenchelPrimalExtension_dualRealPart_isSelfConcordantOnWith`, and derive
-- `∇ f x, ∇ f y ∈ dom (F⋆)` from the chapter owner bridge
-- `image_gradient_subset_dom_fenchelDual_of_selfConcordant`. Then apply the internal bridge
-- theorem `dualRealPart_hessian_loewner_bounds`. The dual-open-Dikin hypothesis and the
-- dual-owner theorem are both bridge/view forms; the main public entry keeps the source-defined
-- quantity `d` and the standing primal hypotheses on the theorem surface, using the canonical
-- self-concordant/vector bridge notation `‖u‖*[f; x]` for the dual local norm of a displacement.
section SelfConcordantSurface

variable [IsSelfConcordantOnWith domain Mf f]
variable
    (hclosed :
      IsClosed (constrainedEpigraph domain (fun z ↦ (f z : WithTop ℝ))))
    (hnoAffineLine : ∀ ⦃z h : X⦄, h ≠ 0 → ¬ ∀ τ : ℝ, z + τ • h ∈ domain)
    {x : X} (hx : x ∈ domain)

local notation:max "‖" u "‖*[" f "; " x "]" =>
  HessianDualLocalNorm.ofSelfConcordantMemVec Mf f hclosed hnoAffineLine x hx u

/-- Lemma 5.1.7, source-facing form: let `F := fenchelPrimalExtension domain f`. Assume `f` is
self-concordant on `domain` with parameter `M_f`, the constrained epigraph of `f` over `domain`
is closed, and `domain` contains no affine line. For `x, y ∈ domain`, let
`d := ‖∇ f x - ∇ f y‖*[f; x]`. If `d < 1 / M_f`, then the primal Hessians at `x` and `y`
satisfy the standard Loewner-order
comparison with factor `(1 - M_f d)^2`. -/
theorem hessian_loewner_bounds_of_fenchelDual_selfConcordant
    (hclosed :
      IsClosed (constrainedEpigraph domain (fun z ↦ (f z : WithTop ℝ))))
    (hnoAffineLine : ∀ ⦃z h : X⦄, h ≠ 0 → ¬ ∀ τ : ℝ, z + τ • h ∈ domain)
    (hx : x ∈ domain) (hy : y ∈ domain)
    (hd_lt : ‖∇ f x - ∇ f y‖*[f; x] < 1 / (Mf : ℝ)) :
    let d := ‖∇ f x - ∇ f y‖*[f; x]
    ((1 - (Mf : ℝ) * d) ^ (2 : ℕ)) • hessian f x ≤ hessian f y ∧
      hessian f y ≤ ((1 - (Mf : ℝ) * d) ^ (2 : ℕ))⁻¹ • hessian f x := by
  sorry

-- Proof sketch: the dual-open-Dikin hypothesis is exactly the bridge/view reformulation of the
-- source quantity `d` in the main theorem. After deriving the standing dual-owner data from the
-- primal hypotheses as above, apply the same internal bridge theorem
-- `dualRealPart_hessian_loewner_bounds`.
/-- Bridge/view corollary to Lemma 5.1.7: under the same standing primal self-concordant
hypotheses, if `∇ f y` lies in the dual open Dikin ellipsoid of `extendedRealRealPart (F⋆)`
centered at `∇ f x` with radius `r < 1 / M_f`, then the same Hessian comparison follows. -/
theorem hessian_loewner_bounds_of_fenchelDual_selfConcordant_of_mem_dualOpenDikinEllipsoid
    (hclosed :
      IsClosed (constrainedEpigraph domain (fun z ↦ (f z : WithTop ℝ))))
    (hnoAffineLine : ∀ ⦃z h : X⦄, h ≠ 0 → ¬ ∀ τ : ℝ, z + τ • h ∈ domain)
    {r : ℝ} (hx : x ∈ domain) (hy : y ∈ domain) (hr : r < 1 / (Mf : ℝ))
    (hgrad : ∇ f y ∈ W⁰[extendedRealRealPart (F⋆); ∇ f x](r)) :
    ((1 - (Mf : ℝ) * r) ^ (2 : ℕ)) • hessian f x ≤ hessian f y ∧
      hessian f y ≤ ((1 - (Mf : ℝ) * r) ^ (2 : ℕ))⁻¹ • hessian f x := by
  sorry

end SelfConcordantSurface

end OwnerLevel

section EuclideanBridge

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

variable {domain : Set E} {Mf : NNReal} {f : E → ℝ} {x y : E}

local notation "F" => fenchelPrimalExtension domain f

section SelfConcordantSurface

variable [IsSelfConcordantOnWith domain Mf f]
variable
    (hclosed :
      IsClosed (constrainedEpigraph domain (fun z ↦ (f z : WithTop ℝ))))
    (hnoAffineLine : ∀ ⦃z h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, z + τ • h ∈ domain)
    {x : E} (hx : x ∈ domain)

local notation:max "‖" u "‖*[" f "; " x "]" =>
  HessianDualLocalNorm.ofSelfConcordantMemVec Mf f hclosed hnoAffineLine x hx u

-- Proof sketch: apply the source-facing owner theorem
-- `hessian_loewner_bounds_of_fenchelDual_selfConcordant` and then transport the intrinsic
-- operator inequalities through the Euclidean identification `hessianMatrix_toEuclideanLin`.
/-- Euclidean matrix view of Lemma 5.1.7: under the same standing primal self-concordant
hypotheses, let
`d := ‖∇ f x - ∇ f y‖*[f; x]`. If `d < 1 / M_f`, the
conjugate-induced Hessian comparison becomes the
standard matrix Loewner comparison between `∇² f x` and `∇² f y`. -/
theorem conjugate_selfConcordant_hessianMatrix_comparison
    (hclosed :
      IsClosed (constrainedEpigraph domain (fun z ↦ (f z : WithTop ℝ))))
    (hnoAffineLine : ∀ ⦃z h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, z + τ • h ∈ domain)
    (hx : x ∈ domain) (hy : y ∈ domain)
    (hd_lt : ‖∇ f x - ∇ f y‖*[f; x] < 1 / (Mf : ℝ)) :
    let d := ‖∇ f x - ∇ f y‖*[f; x]
    (((1 - (Mf : ℝ) * d) ^ (2 : ℕ)) • ∇² f x ≤ ∇² f y) ∧
      (∇² f y ≤ ((1 - (Mf : ℝ) * d) ^ (2 : ℕ))⁻¹ • ∇² f x) := by
  sorry

end SelfConcordantSurface

end EuclideanBridge

end
