import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_5_0_28 (from Chap05) -/
noncomputable section

open scoped Gradient WithTopConvexAnalysis

attribute [local instance] Chap05RealProdL2.instSeminormedAddCommGroupRealProd
attribute [local instance] Chap05RealProdL2.instNormedAddCommGroupRealProd
attribute [local instance] Chap05RealProdL2.instNormedSpaceRealProd
attribute [local instance] Chap05RealProdL2.instInnerProductSpaceRealProd
attribute [local instance] Chap05RealProdL2.instCompleteSpaceRealProd

local notation "P" => ℝ × ℝ
local notation "Q" => (perspectiveCone ℝ : Set P)
local notation "perspectiveSquare" =>
  perspectiveTransform (fun y : ℝ ↦ y ^ (2 : ℕ))

/- Proposition 5.0.28 lies in the chapter's perspective-transform / effective-domain /
explicit-gradient-image domain.

Primary domain:
- the perspective transform of the scalar square function, viewed through the chapter's canonical
  `+∞`-extension owner, and the explicit image of its gradient.

Relevant owner-style declarations sampled before refinement:
- `perspectiveCone` in `Remark_3_1_2_3`, the chapter owner for the cone `τ > 0` together with the
  origin;
- `mem_perspectiveCone_iff`, the canonical membership bridge for that owner;
- `perspectiveTransform`, the chapter owner for the perspective transform on `ℝ × E`;
- `fenchelPrimalExtension` in `Chap05/FenchelPrimalExtension`, the chapter owner for extending a
  real-valued function by `⊤` away from a feasible set;
- `dom` / `withTopRealPart` from `Definition_3_3`, the chapter owners for the finite-value domain
  and its real representative;
- `Chap05RealProdL2.instInnerProductSpaceRealProd`, the chapter owner bridge that equips the raw
  pair model `ℝ × ℝ` with the canonical `L²` inner-product structure;
- mathlib `∇` / `HasGradientAt`, the canonical ambient gradient owner on the genuine
  differentiability region.

Best owner abstraction:
- source-facing: the specific perspective-square specialization of the chapter owner
  `fenchelPrimalExtension` and the explicit parabola theorem for its gradient image;
- core/canonical: `fenchelPrimalExtension`, `perspectiveCone ℝ`, `perspectiveTransform`, `dom`,
  `withTopRealPart`, and the ambient gradient on the raw pair owner `P` equipped with the
  chapter `RealProdL2` structure;
- bridge/view: the pointwise formulas on the positive cone and the effective-domain
  identification carrying the origin.

Primitive data:
- the chapter owner cone `perspectiveCone ℝ : ConvexCone ℝ P`;
- the chapter owner perspective transform specialized to `fun y : ℝ ↦ y ^ (2 : ℕ)`.

Derived API:
- the specialization `F := fenchelPrimalExtension (perspectiveCone ℝ)
    (perspectiveTransform (fun y : ℝ ↦ y ^ (2 : ℕ)))`;
- the effective-domain identification `dom F = perspectiveCone ℝ`;
- the interior-domain bridge `interior (dom F) = {z | 0 < z.1}`;
- the displayed formula for the ambient gradient on the raw pair owner `P`;
- the parabola image theorem for that actual gradient on the positive cone.

The previous version exposed a bespoke local `+∞`-extension and a totalized gradient map,
assigning an arbitrary value at the origin. That is not mathematically faithful because the origin
belongs to the effective domain but not to the differentiability region. This refinement keeps the
same textbook semantics, deletes the redundant local wrapper, reuses the chapter owners
`fenchelPrimalExtension`, `perspectiveCone`, `perspectiveTransform`, `dom`, and
`withTopRealPart`, and states the source-facing gradient theorems directly on the raw pair owner
`P` via the chapter `RealProdL2` bridge instead of exposing explicit `WithLp` transport, with the
origin appearing only in the effective-domain bridge. -/

local notation "F" =>
  fenchelPrimalExtension Q perspectiveSquare

/-- The origin belongs to the effective domain of the perspective-square extension. -/
theorem zero_mem_dom_perspectiveSquare : (0 : P) ∈ dom F := by
  exact
    ((mem_dom_fenchelPrimalExtension_iff :
      (0 : P) ∈ dom F ↔ (0 : P) ∈ Q).2 ((mem_perspectiveCone_iff).2 (Or.inr rfl)))

/-- On pairs with positive first coordinate, the canonical perspective-square extension is given
by the usual perspective formula `y² / τ`. -/
theorem perspectiveSquare_apply_of_positive_fst {z : P} (hz : 0 < z.1) :
    F z = (((z.2 ^ (2 : ℕ) / z.1 : ℝ)) : WithTop ℝ) := by
  rw [fenchelPrimalExtension_apply_of_mem]
  · have hsq :
        perspectiveSquare z = z.2 ^ (2 : ℕ) / z.1 := by
      have hz0 : z.1 ≠ 0 := hz.ne'
      rw [perspectiveTransform_apply_of_pos _ hz]
      calc
        z.1 * ((z.1⁻¹ • z.2) ^ (2 : ℕ))
            = z.1 * ((z.1⁻¹ * z.2) ^ (2 : ℕ)) := by rfl
        _ = z.1 * (z.1⁻¹ ^ (2 : ℕ) * z.2 ^ (2 : ℕ)) := by rw [mul_pow]
        _ = (z.1 * z.1⁻¹ ^ (2 : ℕ)) * z.2 ^ (2 : ℕ) := by ring
        _ = z.1⁻¹ * z.2 ^ (2 : ℕ) := by
          congr 1
          calc
            z.1 * z.1⁻¹ ^ (2 : ℕ) = (z.1 * z.1⁻¹) * z.1⁻¹ := by
              simp [pow_two]
              ring
            _ = z.1⁻¹ := by simp [hz0]
        _ = z.2 ^ (2 : ℕ) / z.1 := by rw [div_eq_mul_inv, mul_comm]
    simp [hsq]
  · exact (mem_perspectiveCone_iff).2 (Or.inl hz)

/-- The finite-value domain of the canonical perspective-square extension is exactly the chapter
owner cone `perspectiveCone ℝ`. -/
theorem perspectiveSquare_effectiveDomain :
    dom F = perspectiveCone ℝ := by
  change dom F = Q
  exact dom_fenchelPrimalExtension

/-- The differentiability region of the finite real part of the canonical perspective-square
extension is exactly the open positive cone `τ > 0`. The origin remains in `dom F`, but only as a
boundary point of the effective domain. -/
theorem perspectiveSquare_interior_effectiveDomain :
    interior (dom F) = {z : P | 0 < z.1} := by
  rw [perspectiveSquare_effectiveDomain]
  have hzero_not_mem :
      (0 : P) ∉ interior (perspectiveCone ℝ : Set P) := by
    intro hzero
    have himage :
        Prod.fst '' (perspectiveCone ℝ : Set P) = Set.Ici (0 : ℝ) := by
      ext τ
      constructor
      · rintro ⟨z, hz, rfl⟩
        rcases z with ⟨τ, x⟩
        rcases (mem_perspectiveCone_iff).1 hz with hτ | hz0
        · exact le_of_lt hτ
        · cases hz0
          have h0 : (0 : ℝ) ≤ 0 := le_rfl
          exact h0
      · intro hτ
        by_cases hτ0 : τ = 0
        · refine ⟨0, (mem_perspectiveCone_iff).2 (Or.inr rfl), ?_⟩
          simp [hτ0]
        · have hτ_pos : 0 < τ := lt_of_le_of_ne hτ (Ne.symm hτ0)
          refine ⟨(τ, 0), (mem_perspectiveCone_iff).2 (Or.inl hτ_pos), ?_⟩
          simp
    have hzero_image :
        (0 : ℝ) ∈ interior (Prod.fst '' (perspectiveCone ℝ : Set P)) :=
      isOpenMap_fst.image_interior_subset (perspectiveCone ℝ : Set P) ⟨0, hzero, rfl⟩
    rw [himage] at hzero_image
    simp at hzero_image
  have hpos_mem :
      {z : P | 0 < z.1} ⊆ interior (perspectiveCone ℝ : Set P) := by
    refine (isOpen_lt continuous_const continuous_fst).subset_interior_iff.2 ?_
    intro z hz
    exact (mem_perspectiveCone_iff).2 (Or.inl hz)
  refine subset_antisymm ?_ hpos_mem
  intro z hz
  rcases (mem_perspectiveCone_iff).1 (interior_subset hz) with hz1 | hz0
  · exact hz1
  · subst z
    exact (hzero_not_mem hz).elim

/-- On pairs with positive first coordinate, the canonical ambient gradient of the finite real
part of the perspective-square extension on the raw pair owner `P` is given by the displayed
rational formula. -/
theorem perspectiveSquare_gradient_eq_formula_of_positive_fst
    {z : P} (hz : 0 < z.1) :
    ∇ (withTopRealPart F) z =
      (-((z.2 / z.1) ^ (2 : ℕ)), (2 : ℝ) * (z.2 / z.1)) := sorry

/-- Proposition 5.0.28: the image of the gradient of the perspective-square function is the
parabola in `ℝ × ℝ` cut out by `g₁ = -(g₂)² / 4`, where the gradient is taken on the genuine
differentiability region `τ > 0`. -/
theorem perspectiveSquare_gradient_image_eq_parabola :
    (fun z : P ↦ ∇ (withTopRealPart F) z) '' {z : P | 0 < z.1} =
      {g : P | g.1 = -(g.2 ^ (2 : ℕ)) / 4} := sorry

end

/-! ### Proposition_5_0_29 (from Chap05) -/
open scoped ConvexAnalysis Gradient WithTopConvexAnalysis

noncomputable section

universe u

/- Proposition 5.0.29 lies in the chapter's Fenchel-conjugacy / gradient-Hessian duality domain.

Primary domain:
- differentiability of the finite real part of the canonical Fenchel dual under a globally unique
  Fenchel-support maximizer hypothesis, together with the inverse-Hessian duality at interior
  maximizing primal points.

Relevant owner-style declarations sampled before refinement:
- `dom` and `extendedRealRealPart` in `Chap03/Definition_3_1_1_3`, the chapter owners for the
  effective domain and finite real part of an `EReal`-valued function;
- `fenchelDual` / notation `f⋆` in `Chap05/Definition_5_0_27`, the chapter owner for the
  Fenchel conjugate of a `WithTop ℝ`-valued function;
- `hessian` in `Chap01/Definition_1_4_16`, the chapter owner for second derivatives of real-valued
  functions on complete real inner-product spaces;
- `IsMaxOn`, the canonical maximizer predicate for the Fenchel support functional
  `y ↦ ⟪s, y⟫ - f y` on `dom f`.

Best owner abstraction:
- source-facing: the unique Fenchel-support maximizer realization of the canonical Fenchel dual
  value and the resulting gradient / inverse-Hessian conclusions, with primal interiority entering
  only in the second-order part;
- core/canonical: `f⋆`, `dom (f⋆)`, `extendedRealRealPart (f⋆)`, `hessian`, and
  `IsMaxOn`;
- bridge/view: the derived Fenchel-dual value identity at a support maximizer.

Primitive data:
- a `WithTop ℝ`-valued primal function `f`;
- for the source-facing gradient statement, a primal-dual point pair `(x, s)` with a unique
  owner-level Fenchel-support maximizer at slope `s`;
- for the second-order bridge statements, a candidate maximizing-point field `xStar` together
  with interior membership of the chosen maximizing points.

Derived API:
- the value identity `extendedRealRealPart (f⋆) s = inner ℝ s (xStar s) - withTopRealPart f
  (xStar s)` at a maximizing point;
- the pointwise gradient and branchwise Hessian-identification conclusions of
  Proposition 5.0.29.

The previous version rebuilt a parallel dual-function parameter `fStar : E → WithTop ℝ` and a
local wrapper around the canonical support-maximizer predicate. Those notions are already owned
upstream by `f⋆`, `dom (f⋆)`, `extendedRealRealPart (f⋆)`, `hessian`, and `IsMaxOn`. This
refinement deletes the duplicate dual layer, rewrites the inverse-Hessian surface through the
chapter owner `hessian`, and states the proposition directly on the canonical support-maximizer
surface. The redundant dual-value equality and raw value-based uniqueness clause are also removed
from the primitive input data: they are downstream consequences of the maximizer hypotheses, not
separate source-level structure. The Euclidean model `EuclideanSpace ℝ (Fin n)` and
finite-dimensionality are not the same issue: the Euclidean display model is unnecessary, but the
chapter's available differentiability bridge for this Fenchel-maximizer argument is only
finite-dimensional. The file therefore stays on the canonical owner level of a finite-dimensional
real inner-product space rather than claiming a new infinite-dimensional theorem. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section

variable {f : E → WithTop ℝ} {xStar : E → E}

-- Proof sketch: use the unique active Fenchel-support maximizer `x` at slope `s` to identify the
-- supporting affine function that realizes `(f⋆) s`; the finite real part of `f⋆` is then
-- differentiable at `s` with gradient `x`. The dual-domain membership is derived from the
-- maximizer hypothesis via the owner-level Fenchel value identity rather than stored as primitive
-- input.
/-- Proposition 5.0.29 (1): if `x` is the unique Fenchel-support maximizer of `f` on `dom f` at
the slope `s`, then the finite real part of `f⋆` has gradient `x` at `s`. This is the
source-facing owner statement: the uniqueness of the active maximizer is the mathematical input,
while primal-side first-order or interior hypotheses belong only to later proof routes and
second-order bridge theorems. The ambient finite-dimensionality is part of the justified owner
layer here, because the project's subgradient-to-gradient bridge is only developed in that
setting. -/
theorem fenchelConjugate_hasGradientAt
    {s x : E}
    (hx : x ∈ dom f)
    (hmax : IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) x)
    (hunique :
      ∀ ⦃y : E⦄, y ∈ dom f →
        IsMaxOn (fun z : E ↦ inner ℝ s z - withTopRealPart f z) (dom f) y → y = x) :
    HasGradientAt (extendedRealRealPart (f⋆)) x s := sorry

section HessianTransfer

-- Proof sketch: differentiate the first-order condition `∇ (withTopRealPart f) (xStar s) = s`
-- at the unique maximizing point and use the invertibility of the primal Hessian at `xStar s` to
-- identify the dual Hessian with the inverse Hessian operator of `f` there.
/-- Proposition 5.0.29 (2): under the same unique Fenchel-support maximizer hypotheses, and
assuming `withTopRealPart f` is `C²` on `interior (dom f)` and the primal Hessian is invertible
at those maximizing points, the Hessian of the finite real part of `f⋆` at `s` is the inverse
Hessian operator of `f` at `xStar s`. As in part (1), this theorem stays at the
finite-dimensional owner level justified by the chapter's first-order differentiability bridge. -/
theorem fenchelConjugate_hessian_eq_inverse
    (hf_contDiff : ContDiffOn ℝ 2 (withTopRealPart f) (interior (dom f)))
    (hxStar_mem : ∀ ⦃s : E⦄, s ∈ dom (f⋆) → xStar s ∈ interior (dom f))
    (hxStar_isMaximizer :
      ∀ ⦃s : E⦄, s ∈ dom (f⋆) →
        IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) (xStar s))
    (hxStar_unique :
      ∀ ⦃s x : E⦄, s ∈ dom (f⋆) → x ∈ dom f →
        IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) x → x = xStar s)
    (hxStar_hessian_invertible :
      ∀ ⦃s : E⦄, s ∈ dom (f⋆) →
        (hessian (withTopRealPart f) (xStar s)).IsInvertible)
    {s : E} (hs : s ∈ dom (f⋆)) :
    hessian (extendedRealRealPart (f⋆)) s =
      (hessian (withTopRealPart f) (xStar s)).inverse := sorry

-- Proof sketch: derive `s ∈ dom (f⋆)` from the Fenchel-support maximizer hypothesis at `x`, use
-- first-order optimality on the interior point `x` to recover `s = ∇ (withTopRealPart f) x`,
-- and then apply the owner-level inverse-Hessian identity. Global uniqueness identifies the
-- interior primal point `x` with `xStar s`, so the primal Hessian term rewrites directly at `x`.
/-- Proposition 5.0.29 (2), gradient-point form: if `withTopRealPart f` is `C²` on
`interior (dom f)`, `x ∈ interior (dom f)` is the unique Fenchel-support maximizer for the slope
`s`, and the primal Hessian is invertible at `x`, then the Hessian of the finite real part of
`f⋆` at `s` is the inverse Hessian operator of `f` at `x`. The dual-domain membership and
first-order identity are derived internally from the interior maximizer hypothesis, so they do
not appear as primitive inputs. -/
theorem fenchelConjugate_hessian_eq_inverse_of_fenchelSupport_isMaxOn {s x : E}
    (hf_contDiff : ContDiffOn ℝ 2 (withTopRealPart f) (interior (dom f)))
    (hx : x ∈ interior (dom f))
    (hx_isMaximizer :
      IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) x)
    (hx_unique :
      ∀ ⦃y : E⦄, y ∈ dom f →
        IsMaxOn (fun z : E ↦ inner ℝ s z - withTopRealPart f z) (dom f) y → y = x)
    (hx_hessian_invertible : (hessian (withTopRealPart f) x).IsInvertible) :
    hessian (extendedRealRealPart (f⋆)) s =
      (hessian (withTopRealPart f) x).inverse := sorry

end HessianTransfer

end

/-! ### Proposition_5_0_30 (from Chap05) -/
open scoped ConvexAnalysis Gradient WithTopConvexAnalysis

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Proposition 5.0.30 lies in the chapter's Fenchel-conjugacy / third-order differential-calculus
domain.

Sampled owner-style declarations:
* `fenchelDual` / notation `f⋆` in `Definition_5_0_27`, the chapter owner for the Fenchel dual;
* `dom` and `extendedRealRealPart` in `Chap03/Definition_3_1_1_3`, the canonical finite-value
  domain / finite-real-part owners for `EReal`-valued functions;
* `IsMaxOn`, the canonical maximizer predicate for the Fenchel support functional
  `y ↦ ⟪s, y⟫ - f y` on `dom f`;
* `gradient` / notation `∇`, the canonical first-order owner for the branch equation
  `∇ f (xStar s) = s`;
* `hessian` in `Chap01/Definition_1_4_16`, the intrinsic second-order owner;
* `fderiv ℝ (hessian g) x h` in `Definition_5_0_8`, the chapter owner for third derivatives;
* `fenchelConjugate_hessian_eq_inverse` in `Proposition_5_0_29`, the chapter owner for the
  preceding inverse-Hessian identity on `dom (f⋆)`;
* `exists_continuousLinearEquiv_fderiv_symm_eq` in mathlib, the canonical local-inverse
  differentiability bridge for genuine invertible Fréchet derivatives.

Best owner abstraction:
* source-facing: the third-derivative formula for `extendedRealRealPart (f⋆)` along a chosen
  Fenchel-maximizer branch `xStar : E → E` on `dom (f⋆)`;
* core/canonical: `extendedRealRealPart (f⋆)`, `hessian`, `∇`, and `IsMaxOn`;
* bridge/view: the prior identity
  `hessian (extendedRealRealPart (f⋆)) s = (hessian (withTopRealPart f) (xStar s)).inverse`.

Primitive data:
* the primal `WithTop ℝ`-valued function `f`;
* a branch `xStar : E → E` on `dom (f⋆)`;
* the source-facing facts that `xStar s` is the Fenchel-support maximizer at `s`,
  lies in `interior (dom f)`, and has invertible primal Hessian at those branch points.

Derived API:
* the branch derivative identity
  `HasFDerivAt xStar (hessian (extendedRealRealPart (f⋆)) s) s`, exposed as the public bridge
  theorem `fenchelConjugate_maximizerBranch_hasFDerivAt` and recovered from the unique interior
  maximizer branch via the local-inverse / gradient bridge;
* the third-derivative formula for `extendedRealRealPart (f⋆)`;
* the actual inverse-Hessian presentation recovered from Proposition 5.0.29 under the explicit
  invertibility hypothesis.

Source/core/bridge triage:
* source-facing: the branchwise `D³ f_*` formula on `dom (f⋆)`;
* core/canonical: the dual Hessian owner `hessian (extendedRealRealPart (f⋆))`;
* bridge/view: the reusable inverse-Hessian identity supplied separately by
  `fenchelConjugate_hessian_eq_inverse`, together with the branch-differentiability bridge theorem
  `fenchelConjugate_maximizerBranch_hasFDerivAt`.

The previous version kept a local copy of the inverse-Hessian relation as primitive data and used
Lean's totalized `ContinuousLinearMap.inverse` without recording either genuine invertibility or
the derivative of the maximizing branch. That weakened the textbook meaning. This refinement
restores the Proposition 5.0.29 owner hypotheses, keeps the branch `xStar` source-facing, exposes
the missing branch-differentiability data `DxStar(s) = ∇² f_*(s)` as a reusable bridge theorem
derived from the unique interior maximizer branch and the local-inverse / gradient bridge, and no
longer smuggles that step in as primitive theorem data. The first-order branch equation is not
retained as primitive data here, because this file reuses the upstream inverse-Hessian owner
theorem rather than reproving it. -/

section

-- Proof sketch: first derive `HasFDerivAt xStar (hessian (extendedRealRealPart (f⋆)) s) s`
-- as a reusable bridge theorem from the unique interior Fenchel-maximizer branch and the local-
-- inverse / gradient bridge around `xStar s`. Then differentiate the genuine inverse-Hessian
-- identity from Proposition 5.0.29 along that branch. The bridge step itself is only `C²`; the
-- `C³` hypothesis is used only for differentiating the primal Hessian at `xStar s`, and the
-- explicit invertibility hypothesis makes that inverse an actual inverse rather than Lean's
-- totalized fallback.
/-- The Fenchel-maximizer branch is differentiable with derivative
`∇² (extendedRealRealPart (f⋆)) s` at every dual-domain point once the maximizing branch is
unique, interior, and has genuinely invertible primal Hessian there. This is the public bridge
from the chosen Fenchel-support maximizer branch to the canonical dual Hessian owner used in
Proposition 5.0.30. -/
theorem fenchelConjugate_maximizerBranch_hasFDerivAt
    {f : E → WithTop ℝ} {xStar : E → E}
    (hf_contDiff : ContDiffOn ℝ 2 (withTopRealPart f) (interior (dom f)))
    (hxStar_mem : ∀ ⦃s : E⦄, s ∈ dom (f⋆) → xStar s ∈ interior (dom f))
    (hxStar_isMaximizer :
      ∀ ⦃s : E⦄, s ∈ dom (f⋆) →
        IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) (xStar s))
    (hxStar_unique :
      ∀ ⦃s x : E⦄, s ∈ dom (f⋆) → x ∈ dom f →
        IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) x → x = xStar s)
    (hxStar_hessian_invertible :
      ∀ ⦃s : E⦄, s ∈ dom (f⋆) →
        (hessian (withTopRealPart f) (xStar s)).IsInvertible)
    {s : E} (hs : s ∈ dom (f⋆)) :
    HasFDerivAt xStar (hessian (extendedRealRealPart (f⋆)) s) s := by
  sorry

/-- Proposition 5.0.30: let `xStar : E → E` be a chosen Fenchel-support maximizer branch on
`dom (f⋆)`. Assume `xStar s ∈ interior (dom f)` and the primal Hessian at `xStar s` is genuinely
invertible. Then the derivative of the dual Hessian at `s` is the third-derivative composition
formula obtained by differentiating the genuine inverse-Hessian identity from Proposition 5.0.29
along the public branch derivative `DxStar(s) = ∇² (extendedRealRealPart (f⋆)) s`.
This remains the source-facing branch theorem; the inverse-Hessian relation and the branch
differentiability are both reused through the upstream owner theorem
`fenchelConjugate_hessian_eq_inverse` and the public bridge theorem
`fenchelConjugate_maximizerBranch_hasFDerivAt` rather than copied as primitive theorem data. -/
theorem fenchelConjugate_hessianDerivative_formula
    {f : E → WithTop ℝ} {xStar : E → E}
    (hf_contDiff : ContDiffOn ℝ 3 (withTopRealPart f) (interior (dom f)))
    (hxStar_mem : ∀ ⦃s : E⦄, s ∈ dom (f⋆) → xStar s ∈ interior (dom f))
    (hxStar_isMaximizer :
      ∀ ⦃s : E⦄, s ∈ dom (f⋆) →
        IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) (xStar s))
    (hxStar_unique :
      ∀ ⦃s x : E⦄, s ∈ dom (f⋆) → x ∈ dom f →
        IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) x → x = xStar s)
    (hxStar_hessian_invertible :
      ∀ ⦃s : E⦄, s ∈ dom (f⋆) →
        (hessian (withTopRealPart f) (xStar s)).IsInvertible)
    {s : E} (hs : s ∈ dom (f⋆))
    (h : E) :
    fderiv ℝ (hessian (extendedRealRealPart (f⋆))) s h =
      -((hessian (extendedRealRealPart (f⋆)) s).comp
        ((fderiv ℝ (hessian (withTopRealPart f)) (xStar s)
            ((hessian (extendedRealRealPart (f⋆)) s) h)).comp
          (hessian (extendedRealRealPart (f⋆)) s))) := by
  have hxStar_hasFDerivAt :
      HasFDerivAt xStar (hessian (extendedRealRealPart (f⋆)) s) s :=
    fenchelConjugate_maximizerBranch_hasFDerivAt (hf_contDiff.of_le (by norm_num)) hxStar_mem
      hxStar_isMaximizer hxStar_unique hxStar_hessian_invertible hs
  sorry

end

/-! ### Proposition_5_0_31 (from Chap05) -/
open scoped DikinEllipsoidNotation Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
Proposition 5.0.31 lies in the Chapter 5 self-concordance / Dikin-ellipsoid domain.

Sampled owner declarations:
* `openDikinEllipsoid` and the notation `W⁰[f; x](r)` in `Definition_5_0_13`, the chapter owner
  and textbook surface for the local quadratic neighborhood;
* `mem_openDikinEllipsoid_inv_constant_iff_hessian_quadratic_lt_inv_sq` in
  `Definition_5_0_14`, the source-facing inverse-parameter quadratic bridge;
* `IsSelfConcordantOnWith.openDikinEllipsoid_inv_constant_subset` in `Theorem_5_1_5`, the
  canonical owner-level domain-inclusion theorem;
* `IsSelfConcordantOnWith.hessian_posSemidef` in `Definition_5_1_1`, which supplies the
  nonnegativity needed by the quadratic bridge.

Source/core/bridge triage:
* source-facing: the textbook inverse-Hessian quadratic neighborhood centered at `sBar`,
  together with the degenerate-point corollary at `0`;
* core/canonical: `W⁰[f; sBar](1 / (Mf : ℝ))` and
  `IsSelfConcordantOnWith.openDikinEllipsoid_inv_constant_subset`;
* bridge/view: the quadratic membership reformulation from `Definition_5_0_14`.

Primitive data:
* a domain `dom`, a self-concordance constant `Mf`, a function `f`, and a center `sBar`;
* the bundled owner hypothesis `IsSelfConcordantOnWith dom Mf f`;
* the displayed inverse-square Hessian quadratic inequality.

Derived API:
* the canonical Dikin neighborhood `W⁰[f; sBar](1 / (Mf : ℝ))`;
* the inverse-square quadratic reformulation of that neighborhood;
* the domain-membership conclusion.

This file therefore recalls the canonical Dikin-owner inclusion theorem directly and keeps only
the genuine quadratic-inequality bridge as new source-facing API. -/

/- Proposition 5.0.31 uses the canonical Dikin-owner inclusion theorem
`IsSelfConcordantOnWith.openDikinEllipsoid_inv_constant_subset` for the neighborhood
`W⁰[f; sBar](1 / (Mf : ℝ))`. -/
recall IsSelfConcordantOnWith.openDikinEllipsoid_inv_constant_subset

-- Proof sketch: rewrite the displayed quadratic bound as membership of `s` in the canonical
-- Dikin ellipsoid `W⁰[f; s̄](1 / M_f)` via the inverse-parameter quadratic bridge from
-- `Definition_5_0_14`, then apply the owner-level inclusion theorem
-- `IsSelfConcordantOnWith.openDikinEllipsoid_inv_constant_subset`. When `Mf = 0`, the bridge
-- identifies the displayed neighborhood with the empty Dikin ellipsoid, so the inclusion remains
-- vacuous without an extra positivity binder.
/-- Proposition 5.0.31: for a self-concordant function on an open convex domain `dom`, the
quadratic neighborhood `{s | ⟪s - s̄, ∇²f(s̄) (s - s̄)⟫ < 1 / M_f^2}` centered at `s̄ ∈ dom` is
contained in `dom`. Via Definition 5.0.14, this is the source-facing quadratic reformulation of
the canonical Dikin neighborhood `W⁰[f; sBar](1 / (Mf : ℝ))`. -/
theorem selfConcordant_quadratic_neighborhood_subset_domain
    (dom : Set E) {Mf : NNReal} {f : E → ℝ}
    [IsSelfConcordantOnWith dom Mf f]
    {sBar : E} (hsBar : sBar ∈ dom) :
    {s : E |
        inner ℝ (s - sBar) (hessian f sBar (s - sBar)) <
          1 / (Mf : ℝ) ^ (2 : ℕ)} ⊆
      dom := by
  intro s hs
  have hself : IsSelfConcordantOnWith dom Mf f := inferInstance
  have hsW : s ∈ W⁰[f; sBar](1 / (Mf : ℝ)) := by
    refine
      (mem_openDikinEllipsoid_inv_constant_iff_hessian_quadratic_lt_inv_sq
        f sBar s Mf (hself.hessian_posSemidef hsBar (s - sBar))).2 hs
  exact hself.openDikinEllipsoid_inv_constant_subset hsBar hsW

-- Proof sketch: apply `selfConcordant_quadratic_neighborhood_subset_domain` to the point `0`.
-- The displayed hypothesis is exactly the same quadratic inequality after simplifying
-- `0 - s̄ = -s̄` and the Hessian quadratic form in the displacement vector.
/-- If the Hessian quadratic form of the displacement from `s̄` to the origin is less than
`1 / M_f^2`, then the origin belongs to the domain. -/
theorem zero_mem_domain_of_selfConcordant_quadratic_neighborhood
    (dom : Set E) {Mf : NNReal} {f : E → ℝ}
    [IsSelfConcordantOnWith dom Mf f]
    {sBar : E} (hsBar : sBar ∈ dom)
    (hquad :
      inner ℝ sBar (hessian f sBar sBar) <
        1 / (Mf : ℝ) ^ (2 : ℕ)) :
    (0 : E) ∈ dom := by
  have hsubset :
      {s : E |
          inner ℝ (s - sBar) (hessian f sBar (s - sBar)) <
            1 / (Mf : ℝ) ^ (2 : ℕ)} ⊆ dom :=
    selfConcordant_quadratic_neighborhood_subset_domain dom hsBar
  exact hsubset (by simpa using hquad)

end
