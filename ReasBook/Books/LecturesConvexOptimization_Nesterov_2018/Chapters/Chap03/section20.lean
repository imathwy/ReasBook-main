import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_20 (from Chap03) -/
universe u

/-
This item is a recall-only entry in the chapter's dual-norm domain.

Layer targeted by this refinement:
- source-facing recall of the core/canonical dual-norm owner already defined in Chapter 2

Primary domain:
- dual norms of separated seminorms on Euclidean spaces `ℝⁿ`.

Sampled owner-style declarations:
- mathlib `Seminorm.closedBall_zero_eq`
- mathlib `normSeminorm`
- project `Seminorm.dualNorm`
- project `Seminorm.dualNorm_apply`

Best owner abstraction:
- `Seminorm.dualNorm p` on a real inner-product space

Primitive data:
- a seminorm `p : Seminorm ℝ E`
- a real inner-product-space structure on `E`
- the separation hypothesis `[Seminorm.IsNorm p]`

Derived API:
- `Seminorm.dualNorm_apply`
- the Euclidean specialization `Seminorm.dualNorm_normSeminorm_eq_norm`

Source/core/bridge triage:
- source-facing: the textbook dual norm attached to a norm or separated seminorm on `ℝⁿ`
- core/canonical: `Seminorm.dualNorm p` on a real inner-product space
- bridge/view: `Seminorm.dualNorm_apply`

The owner declarations already exist upstream in Chapter 2, so this file recalls only the dual
norm owner and its defining bridge formula instead of keeping a parallel Chapter 3 wrapper such
as `dualSeminorm` or re-recalling the support class `Seminorm.IsNorm`. Downstream Chapter 3
files should import this recall file rather than reaching back to Chapter 2 directly.
-/

open scoped SeminormDualNorm

namespace Seminorm

/- Definition 3.20: the dual norm attached to a norm on `ℝⁿ` is recalled through the canonical
Chapter 2 owner `Seminorm.dualNorm`, whose value at `g` is the maximum of `⟪g, x⟫` over the
closed unit ball of the primal norm. -/
recall dualNorm
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p : Seminorm ℝ E) [FiniteDimensional ℝ E] [p.IsNorm] :
    E → ℝ

/- The defining support-function formula is recalled through the canonical companion theorem, on
the source-facing notation `‖g‖[p,*]`. -/
recall dualNorm_apply
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p : Seminorm ℝ E) [FiniteDimensional ℝ E] [p.IsNorm] (g : E) :
    ‖g‖[p,*] = sSup ((fun x ↦ inner ℝ g x) '' {x | p x ≤ 1})

end Seminorm

/-! ### Lemma_3_20 (from Chap03) -/
noncomputable section

open Module LinearMap
open scoped BInducedNorm
open scoped InnerProduct
open scoped EllipsoidNotation
open scoped SeminormDualNorm

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/-
Lemma 3.20 lies in the chapter's centered-ellipsoid / support-value domain.

Sampled owner-style declarations:
- `affineEllipsoid` and `mem_affineEllipsoid_iff` in `Lemma_3_2_7`, the chapter owner/view for
  the textbook ellipsoid `E(H, x̄)`;
- `LinearMap.BilinForm.primalSeminorm` and `LinearMap.BilinForm.dualNorm_apply_strongDual` in
  `Chap04/Definition_4_2_6`, the project owners for the quadratic norm induced by a positive
  definite bilinear form and its dual support value;
- `Seminorm.inner_le_dualNorm_mul` in `Chap02/Definition_2_5`, the canonical duality inequality
  controlling `⟪c, x⟫` by the dual norm times the primal norm;
- downstream recall `Lemma_3_1_20`, which already treats this file's theorem as the owner result.

Best owner abstraction:
- source-facing: the maximum-attainment statement itself, expressed as `IsGreatest`;
- core/canonical: the chapter ellipsoid owner `affineEllipsoid` together with the bilinear-form
  induced seminorm owner attached to `A`;
- bridge/view: the dual-norm formula for the support value and the generic supremum consequence
  `hmax.csSup_eq`.

Primitive data:
- `A : Mat` with `hA : A.PosDef`;
- `c : E`.

Derived API:
- the centered ellipsoid `affineEllipsoid A⁻¹ 0`;
- the induced primal seminorm `x ↦ √⟪A x, x⟫`;
- the image of that ellipsoid under the linear functional `x ↦ ⟪c, x⟫`;
- the support value `√⟪c, A⁻¹ c⟫`.

Source/core/bridge triage:
- source-facing: the textbook claim that the linear functional attains its maximum on the
  centered ellipsoid, together with the maximizing value;
- core/canonical: `affineEllipsoid`, `LinearMap.BilinForm.primalSeminorm`, and
  `Seminorm.dualNorm`;
- bridge/view: the bilinear-form dual-norm formula and the companion supremum identity obtained
  generically from `IsGreatest`.

No earlier chapter/project theorem with this exact mathematical content was found, so this file
keeps the maximum-attainment theorem as the owner declaration rather than collapsing it to a
support-function equality and thereby losing the source-facing attainment data.
-/

private def matrixBilin (A : Mat) : LinearMap.BilinForm ℝ E :=
  ((innerSL ℝ).comp A.toEuclideanLin.toContinuousLinearMap).toBilinForm

private theorem matrixBilin_isSymm_of_posDef
    (A : Mat) (hA : A.PosDef) :
    (matrixBilin A).IsSymm := by
  rw [LinearMap.BilinForm.isSymm_def]
  intro x y
  change inner ℝ (A.toEuclideanLin x) y = inner ℝ (A.toEuclideanLin y) x
  have hPosLin : A.toEuclideanLin.IsPositive :=
    Matrix.isPositive_toEuclideanLin_iff.mpr hA.posSemidef
  simpa [real_inner_comm] using hPosLin.isSymmetric x y

private theorem matrixBilin_posDef_of_posDef
    (A : Mat) (hA : A.PosDef) :
    (matrixBilin A).toQuadraticMap.PosDef := by
  rw [QuadraticMap.posDef_iff_nonneg]
  refine ⟨?_, ?_⟩
  · intro x
    change 0 ≤ inner ℝ (A.toEuclideanLin x) x
    have hPosLin : A.toEuclideanLin.IsPositive :=
      Matrix.isPositive_toEuclideanLin_iff.mpr hA.posSemidef
    simpa [real_inner_comm] using hPosLin.inner_nonneg_right x
  · intro x hx
    by_contra hx0
    have hx' : x.ofLp ≠ 0 := by
      intro h0
      apply hx0
      ext i
      exact congrArg (fun y : Fin n → ℝ ↦ y i) h0
    have hdot : 0 < dotProduct x.ofLp (A.mulVec x.ofLp) := by
      simpa using hA.dotProduct_mulVec_pos hx'
    have hdot_eq : inner ℝ (A.toEuclideanLin x) x = dotProduct x.ofLp (A.mulVec x.ofLp) := by
      have hinner := EuclideanSpace.inner_eq_star_dotProduct (A.toEuclideanLin x) x
      simp only [Matrix.ofLp_toLpLin] at hinner
      simpa [dotProduct_comm] using hinner
    have hx_inner : inner ℝ (A.toEuclideanLin x) x = 0 := by
      simpa [matrixBilin] using hx
    rw [hdot_eq] at hx_inner
    exact hdot.ne' hx_inner

private theorem inner_toEuclideanLin_pos_of_posDef
    (A : Mat) (hA : A.PosDef) {c : E} (hc : c ≠ 0) :
    0 < inner ℝ c (A.toEuclideanLin c) := by
  have hc' : c.ofLp ≠ 0 := by
    intro h0
    apply hc
    ext i
    exact congrArg (fun y : Fin n → ℝ ↦ y i) h0
  have hdot : 0 < dotProduct c.ofLp (A.mulVec c.ofLp) := by
    simpa using hA.dotProduct_mulVec_pos hc'
  have hdot_eq : inner ℝ c (A.toEuclideanLin c) = dotProduct c.ofLp (A.mulVec c.ofLp) := by
    have hinner := EuclideanSpace.inner_eq_star_dotProduct (A.toEuclideanLin c) c
    simp only [Matrix.ofLp_toLpLin] at hinner
    calc
      inner ℝ c (A.toEuclideanLin c) = inner ℝ (A.toEuclideanLin c) c := by
        rw [real_inner_comm]
      _ = dotProduct c.ofLp (A.mulVec c.ofLp) := by
        simpa using hinner
  rw [hdot_eq]
  exact hdot

/-- Lemma 3.20: for a symmetric positive-definite matrix `A`, the linear functional
`x ↦ ⟪c, x⟫` attains its maximum on the centered ellipsoid `affineEllipsoid A⁻¹ 0`, equivalently
on `{x | ⟪A x, x⟫ ≤ 1}`, and that maximum is `√⟪c, A⁻¹ c⟫`. -/
-- Proof sketch: use compactness of the closed ellipsoid and continuity of `x ↦ ⟪c, x⟫` to obtain
-- a maximizer. At an optimal point, the quadratic constraint is active; then apply the
-- first-order optimality condition for the Lagrangian to identify the maximizer with a scalar
-- multiple of `A⁻¹ c`, and solve for the multiplier using the boundary equation.
theorem isGreatest_inner_image_spdEllipsoid
    (A : Mat) (hA : A.PosDef) (c : E) :
    IsGreatest ((fun x : E ↦ inner ℝ c x) '' E(A⁻¹, (0 : E)))
      (Real.sqrt (inner ℝ c ((A⁻¹).toEuclideanLin c))) := by
  letI : Invertible A := hA.isUnit.invertible
  by_cases hc : c = 0
  · refine ⟨?_, ?_⟩
    · refine ⟨0, center_mem_affineEllipsoid A⁻¹ (0 : E), ?_⟩
      simp [hc]
    · rintro y ⟨x, hx, rfl⟩
      simp [hc]
  · let B : LinearMap.BilinForm ℝ E := matrixBilin A
    let hSymm : B.IsSymm := matrixBilin_isSymm_of_posDef A hA
    let hPos : B.toQuadraticMap.PosDef := matrixBilin_posDef_of_posDef A hA
    let p : Seminorm ℝ E := B.primalSeminorm hPos
    letI : Seminorm.IsNorm p := B.primalSeminorm_isNorm hPos
    have hdual :
        Seminorm.dualNorm p c = Real.sqrt (inner ℝ c ((A⁻¹).toEuclideanLin c)) := by
      have hpreimage :
          ((B.toDual (B.nondegenerate_of_posDef hPos)).symm
            (InnerProductSpace.toDual ℝ E c).toLinearMap : E) =
            (A⁻¹).toEuclideanLin c := by
        apply (B.toDual (B.nondegenerate_of_posDef hPos)).injective
        ext y
        change
          B
              (((B.toDual (B.nondegenerate_of_posDef hPos)).symm
                (InnerProductSpace.toDual ℝ E c).toLinearMap)) y =
            B ((A⁻¹).toEuclideanLin c) y
        rw [LinearMap.BilinForm.apply_toDual_symm_apply]
        change inner ℝ c y = inner ℝ (A.toEuclideanLin ((A⁻¹).toEuclideanLin c)) y
        rw [show A.toEuclideanLin ((A⁻¹).toEuclideanLin c) = c by
          ext i
          simp only [Matrix.ofLp_toLpLin]
          simp]
      calc
        Seminorm.dualNorm p c =
            B.dualNorm hPos (InnerProductSpace.toDual ℝ E c).toLinearMap := by
              rw [Seminorm.dualNorm_apply, B.dualNorm_eq_sSup_primalUnitBall_strongDual]
              simp [p, InnerProductSpace.toDual_apply_apply]
        _ = Real.sqrt
              ((InnerProductSpace.toDual ℝ E c)
                ((B.toDual (B.nondegenerate_of_posDef hPos)).symm
                  (InnerProductSpace.toDual ℝ E c).toLinearMap)) := by
              simpa using
                LinearMap.BilinForm.dualNorm_apply_strongDual B hSymm hPos
                  (InnerProductSpace.toDual ℝ E c)
        _ = Real.sqrt (inner ℝ c ((A⁻¹).toEuclideanLin c)) := by
              rw [hpreimage]
              rfl
    let q : ℝ := inner ℝ c ((A⁻¹).toEuclideanLin c)
    have hq : 0 < q := inner_toEuclideanLin_pos_of_posDef A⁻¹ hA.inv hc
    let x0 : E := (Real.sqrt q)⁻¹ • (A⁻¹).toEuclideanLin c
    refine ⟨?_, ?_⟩
    · refine ⟨x0, ?_, ?_⟩
      · rw [mem_affineEllipsoid_iff]
        have hsqrt : Real.sqrt q ≠ 0 := ne_of_gt <| Real.sqrt_pos.2 hq
        have hAinv : A.toEuclideanLin ((A⁻¹).toEuclideanLin c) = c := by
          ext i
          simp only [Matrix.ofLp_toLpLin]
          simp
        have hquad : inner ℝ (A.toEuclideanLin x0) x0 = 1 := by
          calc
            inner ℝ (A.toEuclideanLin x0) x0
                = inner ℝ ((Real.sqrt q)⁻¹ • c)
                    ((Real.sqrt q)⁻¹ • (A⁻¹).toEuclideanLin c) := by
                      simp [x0, hAinv]
            _ = ((Real.sqrt q)⁻¹) ^ (2 : ℕ) * q := by
                  rw [inner_smul_left, inner_smul_right]
                  simp [q, pow_two, mul_comm, mul_left_comm]
            _ = 1 := by
                  field_simp [hsqrt]
                  nlinarith [Real.sq_sqrt (le_of_lt hq)]
        simpa [sub_zero, Matrix.inv_inv_of_invertible] using hquad.le
      · calc
          inner ℝ c x0 = (Real.sqrt q)⁻¹ * q := by
            simpa [x0, q, mul_comm] using
              show
                inner ℝ c ((Real.sqrt q)⁻¹ • (A⁻¹).toEuclideanLin c) =
                  (Real.sqrt q)⁻¹ * inner ℝ c ((A⁻¹).toEuclideanLin c) by
                rw [inner_smul_right]
          _ = Real.sqrt q := by
            have hsqrt : Real.sqrt q ≠ 0 := ne_of_gt <| Real.sqrt_pos.2 hq
            field_simp [hsqrt]
            nlinarith [Real.sq_sqrt (le_of_lt hq)]
          _ = Real.sqrt (inner ℝ c ((A⁻¹).toEuclideanLin c)) := by
            simp [q]
    · rintro y ⟨x, hx, rfl⟩
      have hp_x : p x ≤ 1 := by
        rw [mem_affineEllipsoid_iff] at hx
        simpa [p, B, matrixBilin, LinearMap.BilinForm.primalSeminorm_apply] using hx
      calc
        inner ℝ c x ≤ Seminorm.dualNorm p c * p x :=
          Seminorm.inner_le_dualNorm_mul p x c
        _ ≤ Seminorm.dualNorm p c * 1 := by
              have hdual_nonneg : 0 ≤ Seminorm.dualNorm p c := by
                rw [hdual]
                exact Real.sqrt_nonneg _
              exact mul_le_mul_of_nonneg_left hp_x hdual_nonneg
        _ = Real.sqrt (inner ℝ c ((A⁻¹).toEuclideanLin c)) := by
              rw [hdual]
              simp

/-! ### Proposition_3_20 (from Chap03) -/
noncomputable section

open scoped SupportFunction
open scoped SeminormDualNorm
open scoped WithTopConvexAnalysis

universe u

/- Proposition 3.20 lies in the chapter's dual-norm / subdifferential domain.

Sampled owner-style declarations:
- `supportFunction` and `supportFunction_apply` from `Definition_3_9`, the chapter owner for
  support functions;
- `Seminorm.dualNorm` and `Seminorm.dualNorm_apply` from `Definition_3_20`, the chapter recall of
  the dual-norm owner;
- `IsSubgradientAt`, `subdifferential`, and `mem_subdifferential_iff` from `Definition_3_1_5`, the
  chapter owners for extended-valued subgradients;
- `Seminorm.closedConvexFunction` from `Proposition_3_6` and
  `isGreatest_pairing_image_subdifferential_zero_of_convex_posHomogeneous` from
  `Proposition_3_19`, the upstream Chapter 3 owners that make the support-function statement a
  consequence of convexity plus positive homogeneity rather than a standalone duplicate duality
  theorem.

Best owner abstraction:
- `ξ[Q]` for the support function of a set `Q`;
- `Seminorm.dualNorm p` for the dual norm;
- `∂ f(x)` for the subdifferential statement.

Primitive data:
- a seminorm `p : Seminorm ℝ E`;
- the ambient real inner-product-space structure on `E`;
- the separation hypothesis `[p.IsNorm]` only for the dual-norm formulas;
- finite-dimensionality only for the source-facing dual-ball reformulations and for the
  finite-dimensional owner theorem identifying `p` with the support function of `∂p(0)`.

Derived API:
- the intrinsic origin-subdifferential formula for the lifted real-valued seminorm, derived
  directly from `mem_subdifferential_iff`;
- the owner-level support-function formula for `p` against its origin subdifferential;
- the source-facing dual-unit-ball reformulations of those two intrinsic statements.

Source/core/bridge triage:
- source-facing: the dual-unit-ball support-function and origin-subdifferential formulas;
- core/canonical: `subdifferential` together with the owner-level support-function statement on
  `∂ (fun y ↦ (p y : WithTop ℝ))(0)`;
- bridge/view: the intrinsic inequality description `{g | ∀ y, inner ℝ g y ≤ p y}` and its
  finite-dimensional dual-ball reformulation `{g | ‖g‖[p,*] ≤ 1}`.

This refinement removes the duplicate local effective-domain and subgradient API and rewrites the
proposition directly in the chapter owner vocabulary. The support-function part now passes first
through the canonical Chapter 3 owner `∂ (fun y ↦ (p y : WithTop ℝ))(0)`, so the finite-dimensional
source-facing dual-ball statement is only a bridge theorem rather than a second root description.
For the subdifferential part, the intrinsic inequality characterization `∀ y, ⟪g, y⟫ ≤ p y` is
the mathematically sound bridge on an arbitrary real inner-product space, while the closed dual
unit ball remains the finite-dimensional source-facing reformulation that additionally uses
`[p.IsNorm]`. -/

open Seminorm

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (p : Seminorm ℝ E)

/-- Helper for Proposition 3.20: a seminorm is positively homogeneous of degree `1` on all of
the ambient space. -/
lemma seminorm_isPositivelyHomogeneousOn_univ :
    IsPositivelyHomogeneousOn 1 Set.univ p := by
  refine ⟨?_, ?_⟩
  · intro y hy τ
    simp
  · intro y hy τ
    -- Rewrite the seminorm scaling law into the chapter's positive-homogeneity interface.
    simpa [Real.rpow_one, NNReal.smul_def, smul_eq_mul, Real.norm_of_nonneg τ.2] using
      (map_smul_eq_mul p (τ : ℝ) y)

/-- Proposition 3.20 (2), intrinsic owner form: the subdifferential of the seminorm at the
origin consists exactly of the vectors whose pairing with every `y` is bounded by `p y`. -/
-- Proof sketch: unfold `subdifferential` at `0` via `mem_subdifferential_iff`. Since the lifted
-- seminorm takes finite values everywhere and `p 0 = 0`, the supporting-hyperplane inequality is
-- exactly `⟪g, y⟫ ≤ p y` for every `y`.
theorem subdifferential_seminorm_at_zero_eq_inner_le :
    ∂ (fun y : E ↦ (p y : WithTop ℝ))(0) = {g | ∀ y : E, inner ℝ g y ≤ p y} := by
  ext g
  rw [mem_subdifferential_coe_real_iff]
  -- At the origin, the owner subgradient inequality is exactly the textbook pairing bound.
  constructor
  · intro hg y
    have hy := hg y
    simpa [map_zero p] using hy
  · intro hg y
    have hy := hg y
    simpa [map_zero p] using hy

/-- Proposition 3.20 (1), core/canonical owner form: on a finite-dimensional real inner-product
space, a seminorm is the support function of its origin subdifferential. -/
-- Proof sketch: `Seminorm.closedConvexFunction` supplies the convex owner data for the lifted
-- seminorm, and positive homogeneity comes directly from `Seminorm.map_smul_eq_mul`. Apply
-- `isGreatest_pairing_image_subdifferential_zero_of_convex_posHomogeneous` to the real-valued
-- seminorm `p` and rewrite the resulting `IsGreatest` statement as a support-function equality.
theorem supportFunction_subdifferential_seminorm_at_zero_eq
    [FiniteDimensional ℝ E] (x : E) :
    ξ[∂ (fun y : E ↦ (p y : WithTop ℝ))(0)] x = (p x : EReal) := by
  have hmax_real :
      IsGreatest ((fun g : E ↦ inner ℝ g x) '' ∂ (fun y : E ↦ (p y : WithTop ℝ))(0)) (p x) :=
    isGreatest_pairing_image_subdifferential_zero_of_convex_posHomogeneous
      (f := p) (hf_convex := p.convexOn)
      (hf_hom := seminorm_isPositivelyHomogeneousOn_univ (p := p)) x
  have hmax_ereal :
      IsGreatest
        ((fun g : E ↦ (inner ℝ g x : EReal)) '' ∂ (fun y : E ↦ (p y : WithTop ℝ))(0))
        (p x : EReal) := by
    -- Convert the real maximizer statement into the `EReal` support-function codomain.
    simpa only [Set.image_image] using
      (EReal.coe_strictMono.map_isGreatest).2 hmax_real
  -- The support function is precisely the supremum of the same pairing image.
  rw [supportFunction_apply]
  exact hmax_ereal.csSup_eq

/-- Proposition 3.20 (2), source-facing finite-dimensional form: the subdifferential of the
seminorm at the origin is exactly the closed unit ball of the dual norm. -/
-- Proof sketch: combine `subdifferential_seminorm_at_zero_eq_inner_le` with the finite-dimensional
-- equivalence between the intrinsic inequalities `∀ y, ⟪g, y⟫ ≤ p y` and the dual-ball condition
-- `‖g‖[p,*] ≤ 1`.
theorem subdifferential_seminorm_at_zero_eq_dualNorm_closedUnitBall
    [p.IsNorm] [FiniteDimensional ℝ E] :
    ∂ (fun y : E ↦ (p y : WithTop ℝ))(0) = {g | ‖g‖[p,*] ≤ 1} := by
  ext g
  rw [subdifferential_seminorm_at_zero_eq_inner_le (p := p)]
  change (∀ y : E, inner ℝ g y ≤ p y) ↔ ‖g‖[p,*] ≤ 1
  -- Rewrite the intrinsic support inequalities through the dual-norm owner formula.
  constructor
  · intro hg
    rw [Seminorm.dualNorm_apply]
    refine csSup_le ?_ ?_
    · refine ⟨0, ?_⟩
      refine ⟨0, ?_, ?_⟩
      · simp [map_zero p]
      · simp
    · rintro z ⟨y, hy, rfl⟩
      exact (hg y).trans hy
  · intro hg y
    calc
      inner ℝ g y ≤ ‖g‖[p,*] * p y := Seminorm.inner_le_dualNorm_mul p y g
      _ ≤ 1 * p y := mul_le_mul_of_nonneg_right hg (by positivity)
      _ = p y := by ring

/-- Proposition 3.20 (1), source-facing finite-dimensional form: the original seminorm is the
support function of the closed unit ball of its dual norm. -/
-- Proof sketch: rewrite the support set in
-- `supportFunction_subdifferential_seminorm_at_zero_eq` using
-- `subdifferential_seminorm_at_zero_eq_dualNorm_closedUnitBall`.
theorem supportFunction_dualNorm_closedUnitBall_eq [p.IsNorm] [FiniteDimensional ℝ E] (x : E) :
    ξ[{g : E | ‖g‖[p,*] ≤ 1}] x = (p x : EReal) := by
  -- Replace the source-facing dual ball by the canonical origin subdifferential from above.
  rw [← subdifferential_seminorm_at_zero_eq_dualNorm_closedUnitBall (p := p)]
  exact supportFunction_subdifferential_seminorm_at_zero_eq (p := p) x

end

/-! ### Theorem_3_20 (from Chap03) -/
noncomputable section

open scoped ConvexAnalysis WithTopConvexAnalysis

/- Theorem 3.20 is a recall-only Euclidean specialization in the chapter's Fenchel-biconjugacy
domain.

Primary domain:
- Fenchel conjugates, biduals, and subdifferentials of `ℝ ∪ {+∞}`-valued functions on `ℝⁿ`.

Sampled owner-style declarations:
- `fenchelConjugate` in `Definition_6_1`, the core owner;
- the source-facing Fenchel-dual notation `f⋆` in `Definition_3_1_2_1`;
- the source-facing Fenchel-bidual notation `f⋆⋆` in `Theorem_3_1_5_2`;
- the intrinsic theorem declarations `fenchelBidual_le_of_mem_dom`,
  `subdifferential_subset_dom_fenchelDual`, and
  `fenchelBidual_eq_of_subdifferential_nonempty` in `Theorem_3_1_5_2`.

Best owner abstraction:
- the intrinsic theorem surface in `Theorem_3_1_5_2`, stated on the chapter's source-facing
  notation `f⋆` and `f⋆⋆`.

Primitive data:
- none in this file; the notation and theorem owners already live upstream.

Derived API:
- this Euclidean recall surface.

Source/core/bridge triage:
- source-facing: Theorem 3.20's Euclidean `ℝⁿ` specialization of the textbook Fenchel-biconjugacy
  statements;
- core/canonical: the intrinsic theorem declarations from `Theorem_3_1_5_2`;
- bridge/view: this finite-dimensional specialization by recall.

The previous refinement rebuilt a parallel Euclidean `f⋆` / `f⋆⋆` surface locally and then only
`#check`ed the theorem propositions. This file now consumes the owner-level notation and theorem
API from `Definition_3_1_2_1` and `Theorem_3_1_5_2` directly, so the Euclidean item is only the
specialization layer and does not maintain a second bridge surface. The explicit specialized
checks below expose the actual `E = EuclideanSpace ℝ (Fin n)` signatures instead of only
rechecking the generic owner names.
-/

section

variable {n : ℕ}
variable {f : EuclideanSpace ℝ (Fin n) → WithTop ℝ}
variable {x : EuclideanSpace ℝ (Fin n)}

/- Theorem 3.20 (1): in the Euclidean specialization `E = EuclideanSpace ℝ (Fin n)`, the
Fenchel bidual is bounded above by the original value at every point of `dom f`. -/
#check
  (fenchelBidual_le_of_mem_dom :
    x ∈ dom f → (f⋆⋆) x ≤ withTopToEReal (f x))

/- Theorem 3.20 (2): in the Euclidean specialization `E = EuclideanSpace ℝ (Fin n)`, every
subgradient belongs to the effective domain of the Fenchel dual. -/
#check
  (subdifferential_subset_dom_fenchelDual :
    ∂ f(x) ⊆ dom (f⋆))

/- Theorem 3.20 (3): in the Euclidean specialization `E = EuclideanSpace ℝ (Fin n)`, nonempty
subdifferential implies Fenchel-bidual equality at `x`. -/
#check
  (fenchelBidual_eq_of_subdifferential_nonempty :
    (∂ f(x)).Nonempty → (f⋆⋆) x = withTopToEReal (f x))

end

end
