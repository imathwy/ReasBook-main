import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section
open scoped Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Definition 6.30.3 gives the affine-majorant formula for the closure of a
  concave function.
- `core/canonical`: the closure owner already introduced in this chapter is `concaveClosure`.
- `bridge/view`: the formula is mediated upstream by
  `concaveClosure_eq_iInf_affineMajorant_of_eq_iSup_affineMinorant`; this file keeps the main
  theorem surface at that generic owner layer (assuming the convex-side affine-minorant
  representation of `cl(-g)`), and then records the finite-dimensional scalar-field pairing and
  inner-product specializations as downstream bridges.

Primary mathematical domain:
- convex/concave duality for `WithTopBot`-valued functions on ordered scalar codomains.

Domain-style sampling used here:
- `concaveClosure`;
- `AffineMajorant`;
- `concaveClosure_eq_iInf_affineMajorant_of_eq_iSup_affineMinorant`;
- `Function.IsConcave.concaveClosure_eq_iInf_affineMajorant_of_pairingSubConstRepresentable`;
- `AffineMap.exists_eq_inner_add_const` for the finite-dimensional inner-product bridge.

Primitive data vs derived API:
- primitive owner: `concaveClosure g`;
- primitive bridge input: the convex-side representation
  `cl(-g) x = ⨆ h : AffineMinorant (-g), h.toWithBotTop x`;
- derived bridge API: the source-facing affine-majorant formula expressing `concaveClosure g` as
  the pointwise infimum of affine majorants of `g`; the item then discharges the bridge input on
  the finite-dimensional scalar-field pairing layer and finally specializes to inner-product spaces
  through the affine-representation bridge.

Layer target: `bridge/view`. The item is a textbook specification of the already introduced owner
`concaveClosure`, so the main labeled entry is a direct recall of that canonical owner rather than
another wrapper definition.
-/

/- Definition 6.30.3 (1): the textbook closure `cl g` of a concave function is the canonical
Chapter 6 owner `concaveClosure g`. -/
recall concaveClosure

section

variable {𝕜 : Type*} [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜] [Ring 𝕜]
variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]

-- Proof sketch: apply the generic owner theorem from `Definition_6_30_2` pointwise.
/-- Definition 6.30.3 (2), canonical function-level bridge form: if the convex-side closure
`cl(-g)` is represented pointwise by the supremum of affine minorants of `-g`, then the concave
closure of `g` is the pointwise infimum of affine majorants of `g`. -/
theorem concaveClosure_eq_iInf_affineMajorant
    [IsOrderedAddMonoid 𝕜]
    (g : E → WithTopBot 𝕜)
    (hcl : cl(-g) = fun x ↦ ⨆ h : AffineMinorant (-g), h.toWithBotTop x) :
    concaveClosure g = fun x ↦ ⨅ h : AffineMajorant g, h.toWithTopBot x := by
  funext x
  exact concaveClosure_eq_iInf_affineMajorant_of_eq_iSup_affineMinorant g x
    (congrArg (fun f : E → WithTopBot 𝕜 ↦ f x) hcl)

/-- Definition 6.30.3 (2), canonical bridge form at a fixed point `x`. -/
theorem concaveClosure_apply_eq_iInf_affineMajorant
    [IsOrderedAddMonoid 𝕜]
    (g : E → WithTopBot 𝕜) (x : E)
    (hcl : cl(-g) x = ⨆ h : AffineMinorant (-g), h.toWithBotTop x) :
    concaveClosure g x =
      ⨅ h : AffineMajorant g, h.toWithTopBot x := by
  exact concaveClosure_eq_iInf_affineMajorant_of_eq_iSup_affineMinorant g x hcl

end

section

variable {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)]
variable {E : Type*}
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
variable [FiniteDimensional 𝕜 E] [HasLinearPairing E E 𝕜]
variable [HasContinuousPairing E E 𝕜] [HasPairingSwap E E 𝕜]

-- Proof sketch: discharge Definition 6.30.3 directly by the pairing-level bridge theorem from
-- `Definition_6_30_2`.
/-- Finite-dimensional scalar-field pairing bridge for Definition 6.30.3 (2), in canonical
function-level form. -/
theorem concaveClosure_eq_iInf_affineMajorant_of_pairingSubConstRepresentable
    (g : E → WithTopBot 𝕜) (hg : g.IsConcave 𝕜)
    (h_affine : AffineMinorant.IsPairingSubConstRepresentable (-g)) :
    concaveClosure g = fun x ↦ ⨅ h : AffineMajorant g, h.toWithTopBot x := by
  funext x
  exact hg.concaveClosure_eq_iInf_affineMajorant_of_pairingSubConstRepresentable x h_affine

/-- Finite-dimensional scalar-field pairing bridge for Definition 6.30.3 (2), evaluated at a
fixed point `x`. -/
theorem concaveClosure_apply_eq_iInf_affineMajorant_of_pairingSubConstRepresentable
    (g : E → WithTopBot 𝕜) (x : E) (hg : g.IsConcave 𝕜)
    (h_affine : AffineMinorant.IsPairingSubConstRepresentable (-g)) :
    concaveClosure g x =
      ⨅ h : AffineMajorant g, h.toWithTopBot x := by
  simpa using congrArg (fun f : E → WithTopBot 𝕜 ↦ f x)
    (concaveClosure_eq_iInf_affineMajorant_of_pairingSubConstRepresentable
      g hg h_affine)

end

section

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Definition 6.30.3 (2), Euclidean specialization: on a finite-dimensional real inner-product
space, and hence in particular on `ℝ^n`, the concave closure equals the pointwise infimum of all
affine majorants. -/
theorem concaveClosure_eq_iInf_affineMajorant_of_innerProduct
    (g : E → WithTopBot ℝ) (hg : g.IsConcave ℝ) :
    concaveClosure g = fun x ↦ ⨅ h : AffineMajorant g, h.toWithTopBot x := by
  letI : HasLinearPairing E E ℝ := instHasLinearPairingInner E
  letI : HasContinuousPairing E E ℝ := instHasContinuousPairingInner E
  letI : HasPairingSwap E E ℝ := instHasPairingSwapInner E
  funext x
  have h_affine : AffineMinorant.IsPairingSubConstRepresentable (-g) := by
    intro h
    rcases AffineMap.exists_eq_inner_add_const (f := h.1) with ⟨y, α, hrepr⟩
    refine ⟨y, -α, ?_⟩
    ext z
    rw [pairingSubConstAffineMap_apply]
    have hreprz : (h.1 : E → ℝ) z = inner ℝ y z + α := by
      simpa using congrArg (fun f : E → ℝ ↦ f z) hrepr
    simpa [real_inner_comm, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hreprz
  exact concaveClosure_apply_eq_iInf_affineMajorant_of_pairingSubConstRepresentable g x hg h_affine

/-- Definition 6.30.3 (2), Euclidean specialization evaluated at a fixed point `x`. -/
theorem concaveClosure_apply_eq_iInf_affineMajorant_of_innerProduct
    (g : E → WithTopBot ℝ) (x : E) (hg : g.IsConcave ℝ) :
    concaveClosure g x =
      ⨅ h : AffineMajorant g, h.toWithTopBot x := by
  simpa using congrArg (fun f : E → WithTopBot ℝ ↦ f x)
    (concaveClosure_eq_iInf_affineMajorant_of_innerProduct g hg)

end
