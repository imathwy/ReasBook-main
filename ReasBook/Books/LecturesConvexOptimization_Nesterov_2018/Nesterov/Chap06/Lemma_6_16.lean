import LecturesConvexOptimization_Nesterov_2018.Chap06.Definition_6_56

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Lemma 6.16 lies in the Chapter 6 restricted-duality / concavity domain.

Sampled owner declarations:
- `restrictedDualFunction` in `Definition_6_55`, the Chapter 6 owner of the restricted dual
  supremum;
- `scaledRestrictedDualFunction` in `Definition_6_56`, the Chapter 6 owner of the contracted
  restricted dual supremum;
- `AffineMap.lineMap` in mathlib, the canonical affine owner of the contraction
  `y = (1 - τ) • xBar + τ • x` used inside `scaledRestrictedDualFunction`;
- `ConcaveOn` in mathlib, the canonical concavity owner on a feasible set.

Best owner abstraction:
- source-facing: the interval estimate comparing the scaled and unscaled restricted dual
  functions;
- core/canonical: `restrictedDualFunction` and `scaledRestrictedDualFunction`;
- bridge/view: the real-valued specialization `fun x ↦ (F x : WithTop ℝ)`.

Primitive data:
- the feasible set `Q`;
- the real-valued concave function `F`;
- the feasible base point `xBar ∈ Q`;
- the contraction parameter `τ ∈ [0, 1]`;
- the dual vector `s`.

Derived API:
- the canonical restricted dual value
  `restrictedDualFunction Q (fun x ↦ (F x : WithTop ℝ)) ... s`;
- the canonical scaled restricted dual value
  `scaledRestrictedDualFunction Q (fun x ↦ (F x : WithTop ℝ)) ... τ s`;
- the interval comparison below.

The previous file rebuilt local `ℝ`-valued owners for the same restricted-dual suprema already
introduced in `Definition_6_55` and `Definition_6_56`. This refinement removes that duplicate
wheel, keeps the owner layer in the Chapter 6 canonical `WithTop ℝ` form, and presents Lemma 6.16
as the real-valued bridge obtained from the canonical lift `fun x ↦ (F x : WithTop ℝ)`.
-/

/-- Lemma 6.16: for a concave real-valued function `F` on `Q`, the scaled restricted dual
function of the canonical `WithTop` lift of `F` at `(τ, xBar)` lies between `0` and `τ` times the
unscaled restricted dual function. -/
-- Proof sketch: the lower bound comes from the feasible choice `x = xBar`, where the affine gap
-- is `0`. For the upper bound, write `y = (1 - τ) • xBar + τ • x`; concavity keeps `y` in `Q`,
-- and `F y ≥ (1 - τ) * F xBar + τ * F x` gives
-- `s (xBar - y) + F xBar - F y ≤ τ * (s (xBar - x) + F xBar - F x)` pointwise. Taking suprema
-- yields the claimed factor-`τ` estimate.
theorem scaledRestrictedDualFunction_mem_Icc_of_concaveOn
    {Q : Set E} {F : E → ℝ} (hF : ConcaveOn ℝ Q F)
    {xBar : E} (hxBar : xBar ∈ Q) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (s : StrongDual ℝ E) :
    scaledRestrictedDualFunction Q (fun x ↦ (F x : WithTop ℝ))
        ⟨xBar, by simp [hxBar, withTopEffectiveDomain]⟩ τ s ∈
      Set.Icc
        (0 : WithTop ℝ)
        (((τ : WithTop ℝ) *
          restrictedDualFunction Q (fun x ↦ (F x : WithTop ℝ))
            ⟨xBar, by simp [hxBar, withTopEffectiveDomain]⟩ s)) := sorry

end
