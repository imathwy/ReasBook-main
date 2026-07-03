import Mathlib
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_5_4_7_3 (from Chap05) -/
noncomputable section

open EuclideanSpace (positiveOrthant)
open scoped HessianLocalNorm RelativeDirection

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "X₂" => positiveOrthant 2

/- Definition 5.4.7.3 lies in the Chapter 5 positive-orthant barrier / local-Hessian-norm domain.

Sampled owner declarations:
* `EuclideanSpace.positiveOrthant` and `EuclideanSpace.mem_positiveOrthant_iff` from
  `Chap01/Definition_1_10_2`, the intrinsic strict positive-orthant owner;
* `standardLogarithmicBarrierAmbient` from `Definition_5_4_3_2`, the chapter ambient bridge for
  the positive-orthant logarithmic barrier;
* `hessianLocalNorm` from `Definition_5_1_1`, the chapter owner for local Hessian norms;
* `sigmaThree` from `Definition_5_4_6_8`, the source-facing squared-local-norm bridge.

Source/core/bridge triage:
* source-facing: `scaledDirectionSigma x h`, the textbook scalar `σ`;
* core/canonical: the squared local norm `sigmaThree (standardLogarithmicBarrierAmbient 2) x h`;
* bridge/view: the explicit coordinate formula `σ = (h₁ / x₁)^2 + (h₂ / x₂)^2`.

Primitive data:
* a strictly positive base point `x : positiveOrthant 2`;
* a direction `h : ℝ²`.

Derived API:
* the specialized squared local norm `scaledDirectionSigma x h`;
* the owner-level identity with `‖h‖[standardLogarithmicBarrierAmbient 2; x]^2`;
* the coordinate expansion theorem below.

The earlier version exposed a totalized coordinate formula on all of `ℝ²`, which lost the strict
positivity semantics of the source barrier geometry. The refined file keeps the strict-domain base
point as primitive data and reuses the chapter owner `sigmaThree`, leaving the coordinate formula
as a companion bridge theorem. -/

/-- Definition 5.4.7.3: for a strictly positive point `x ∈ ℝ_{++}²` and a direction `h ∈ ℝ²`,
the scalar `σ` is the squared local norm induced by the positive-orthant logarithmic barrier. -/
abbrev scaledDirectionSigma (x : X₂) (h : E₂) : ℝ :=
  sigmaThree (standardLogarithmicBarrierAmbient 2) x h

/-- Expanding `scaledDirectionSigma x h` gives the square of the canonical Hessian local norm of
the positive-orthant logarithmic barrier at `x`. -/
theorem scaledDirectionSigma_def (x : X₂) (h : E₂) :
    scaledDirectionSigma x h =
      ‖h‖[standardLogarithmicBarrierAmbient 2; x] ^ (2 : ℕ) :=
  rfl

/-- The scalar `scaledDirectionSigma x h` is the squared Euclidean norm of the relative direction
`δ_x(h)`, written in Lean as `δ[x](h)`. -/
theorem scaledDirectionSigma_eq_norm_relativeDirection (x : X₂) (h : E₂) :
    scaledDirectionSigma x h = ‖δ[x](h)‖ ^ (2 : ℕ) := by
  rw [scaledDirectionSigma_def, positiveOrthantLogarithmicBarrier_localNorm_eq_norm_relativeDirection]

/-- The scalar `scaledDirectionSigma x h` is the sum of squares of the two scaled direction
components. -/
theorem scaledDirectionSigma_eq (x : X₂) (h : E₂) :
    scaledDirectionSigma x h =
      (h 0 / (x : E₂) 0) ^ (2 : ℕ) + (h 1 / (x : E₂) 1) ^ (2 : ℕ) := by
  rw [scaledDirectionSigma_eq_norm_relativeDirection]
  simpa [Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq (δ[x](h))

end

/-! ### Definition_5_4_7_4 (from Chap05) -/
noncomputable section

/- Definition 5.4.7.4 lies in the Chapter 5 power-cone / cone-composition domain.

Sampled owner declarations:
* `powerCone` from `Definition_5_4_7_1`, the earlier chapter owner for the symmetric power cone;
* `powerConeQ1` and `powerConeGeometricMean` from `Definition_5_4_7_1`, the primitive power-cone
  data reused here;
* `qTwoPlus` / `Q₂⁺` from `Definition_5_4_7_5`, the source-facing owner/notation for the
  comparison half-space `Q₂⁺`;
* `coneCompositionFeasibleSet` from `Definition_5_4_6_3`, the generic owner for feasible sets cut
  out by a cone-order comparison;
* mathlib `ConvexCone.positive`, the canonical owner for the nonnegative ray.

Source/core/bridge triage:
* source-facing: `power_cone_plus α`, the textbook one-sided power cone `K_α^+`;
* core/canonical: `coneCompositionFeasibleSet` specialized to the power-cone data and the
  positive cone on `ℝ`;
* bridge/view: the coordinate membership lemma `mem_power_cone_plus_iff`.

Primitive data:
* the orthant `powerConeQ1 = ℝ_+²`;
* the weighted geometric mean `powerConeGeometricMean α`;
* the positive cone `ConvexCone.positive ℝ ℝ`;
* the planar comparison set `Q₂⁺ = {(y, z) | z ≤ y}`.

Derived API:
* the source-facing owner `power_cone_plus α`;
* the coordinate membership characterization below.

This refinement keeps the textbook owner `K_α^+`, but defines it through the chapter's canonical
cone-composition owner instead of repeating the existential comparison geometry entrywise. -/

open scoped QTwoPlus

/-- Definition 5.4.7.4: for `α ∈ (0, 1)`, the one-sided power cone `K_α^+` consists of the
triples `((x₁, x₂), z)` with `(x₁, x₂) ∈ ℝ_+²` and `z ≤ x₁^α x₂^(1 - α)`. -/
def power_cone_plus (α : ℝ) : Set ((ℝ × ℝ) × ℝ) :=
  coneCompositionFeasibleSet
    powerConeQ1
    (ConvexCone.positive ℝ ℝ)
    (powerConeGeometricMean α)
    Q₂⁺

namespace PowerConePlus

/- Source-facing Lean notation for the textbook one-sided power cone `K_α^+`. -/
scoped notation:max "K_[" α:arg "]⁺" => power_cone_plus α

end PowerConePlus

open scoped PowerConePlus

-- Proof sketch: expand `power_cone_plus` through `mem_coneCompositionFeasibleSet_iff`. The
-- existential witness `y` satisfies `z ≤ y ≤ powerConeGeometricMean α (x₁, x₂)`, hence
-- `z ≤ powerConeGeometricMean α (x₁, x₂)`; conversely, if
-- `z ≤ powerConeGeometricMean α (x₁, x₂)`, choose `y = z`.
/-- A triple `((x₁, x₂), z)` lies in `K_[α]⁺` exactly when `x₁, x₂ ≥ 0` and
`z ≤ x₁^α x₂^(1 - α)`, equivalently `z ≤ powerConeGeometricMean α (x₁, x₂)`. -/
theorem mem_power_cone_plus_iff (α x₁ x₂ z : ℝ) :
    ((x₁, x₂), z) ∈ K_[α]⁺ ↔
      0 ≤ x₁ ∧ 0 ≤ x₂ ∧ z ≤ powerConeGeometricMean α (x₁, x₂) := by
  rw [power_cone_plus, mem_coneCompositionFeasibleSet_iff]
  constructor
  · rintro ⟨y, hQ1, hy, hyz⟩
    rw [mem_powerConeQ1_iff] at hQ1
    have hy' : y ≤ powerConeGeometricMean α (x₁, x₂) := by
      simpa [sub_nonneg] using hy
    exact ⟨hQ1.1, hQ1.2, le_trans hyz hy'⟩
  · rintro ⟨hx₁, hx₂, hz⟩
    refine ⟨z, (mem_powerConeQ1_iff x₁ x₂).2 ⟨hx₁, hx₂⟩, ?_, ?_⟩
    · simpa [sub_nonneg] using hz
    · exact (mem_qTwoPlus_iff z z).2 le_rfl

/-! ### Definition_5_4_7_5 (from Chap05) -/
noncomputable section

/- Chapter 5 planar half-space / logarithmic-barrier context for this item.

Sampled owner declarations:
* `sublevelLogBarrier` from `Theorem_5_1_4`, the chapter owner for barriers of the form
  `x ↦ -log (β - f x)`;
* `powerConeQ2` from `Definition_5_4_7_1`, the neighboring planar comparison-set owner;
* `qTwoBarrier` from `Definition_5_4_7_2`, the neighboring planar-cone barrier recall;
* mathlib set-builder half-spaces, the canonical owner layer for affine half-space domains.

Source/core/bridge triage:
* source-facing: `qTwoPlus`, with notation `Q₂⁺`, for the textbook half-space
  `Q₂⁺ = {(y, z) | z ≤ y}`;
* core/canonical: `sublevelLogBarrier (fun yz ↦ yz.2 - yz.1) 0`;
* bridge/view: the membership theorem and the pointwise evaluation theorem.

Primitive data:
* the source-facing half-space `Q₂⁺`.

Derived API:
* the recalled canonical barrier specialization
  `sublevelLogBarrier (fun yz : ℝ × ℝ ↦ yz.2 - yz.1) 0`;
* the source-facing membership and evaluation lemmas below.

This file therefore keeps `Q₂⁺` as the source-facing owner and reuses the chapter barrier owner
directly. The barrier clause of the numbered item is presented as a canonical recall, rather than
through a second public logarithmic-barrier alias. The textbook parameter `μ = 1` is already the
literal canonical parameter value, so no separate owner or bridge declaration is introduced for
it. -/

/-- The one-sided planar comparison set `Q₂⁺ = {(y, z) : z ≤ y}`. -/
def qTwoPlus : Set (ℝ × ℝ) :=
  {yz | yz.2 ≤ yz.1}

namespace QTwoPlus

/- Source-facing Lean notation for the textbook half-space `Q₂⁺`. -/
scoped notation:max "Q₂⁺" => qTwoPlus

end QTwoPlus

open scoped QTwoPlus

-- Proof sketch: unfold `qTwoPlus`; membership is exactly the defining inequality `z ≤ y` for the
-- half-space `Q₂⁺`.
/-- A pair `(y, z)` belongs to `Q₂⁺` exactly when `z ≤ y`. -/
theorem mem_qTwoPlus_iff (y z : ℝ) :
    (y, z) ∈ Q₂⁺ ↔ z ≤ y := by
  rfl

set_option linter.hashCommand false in
/- Definition 5.4.7.5 recalls the canonical logarithmic barrier specialization for
`Q₂⁺ = {(y, z) : z ≤ y}`. -/
#check (sublevelLogBarrier (fun yz : ℝ × ℝ ↦ yz.2 - yz.1) 0 : (ℝ × ℝ) → ℝ)

-- Proof sketch: apply `sublevelLogBarrier_apply` to the affine function
-- `fun yz : ℝ × ℝ ↦ yz.2 - yz.1` and rewrite `0 - (z - y)` as `y - z`.
/-- Evaluating the recalled barrier specialization at `(y, z)` recovers the textbook formula
`Phi^+(y, z) = -log (y - z)`. -/
theorem qTwoPlus_sublevelLogBarrier_apply (y z : ℝ) :
    sublevelLogBarrier (fun yz ↦ yz.2 - yz.1) 0 (y, z) = -Real.log (y - z) := by
  rw [sublevelLogBarrier_apply]
  ring_nf

end

/-! ### Definition_5_4_7_6 (from Chap05) -/
noncomputable section

open scoped EuclideanSpaceLp

variable (n : ℕ)

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)

/- Definition 5.4.7.6 lies in the Chapter 5 finite-dimensional `ℓ_p` epigraph / lifted-cone
domain.

Sampled owner declarations:
* `EuclideanSpace.LpExponent` from `Chap03/Definition_3_7`, the project owner for admissible
  finite-dimensional `ℓ_p` exponents `1 ≤ p < ∞`;
* `EuclideanSpace.lpSeminorm` and its notation surface `‖z‖_[p]` from `Chap03/Definition_3_7`,
  the intrinsic `ℓ_p` owner on `EuclideanSpace ℝ (Fin n)`;
* `constrainedEpigraph` from `Chap03/Definition_3_3`, the chapter owner for epigraphs over a
  specified feasible set;
* `mem_constrainedEpigraph_iff` from `Chap03/Definition_3_3`, the atomic membership bridge for
  that owner.

Best owner abstraction:
* the intrinsic epigraph
  `lpNormEpigraphCone n p : Set (ℝ × EuclideanSpace ℝ (Fin n))`
  built from `EuclideanSpace.lpSeminorm n p`.

Source/core/bridge triage:
* source-facing: `lpNormEpigraphCone n p`, the textbook epigraph cone written in the source order
  `(τ, z)`;
* core/canonical: `constrainedEpigraph Set.univ (fun z : Eₙ ↦ (‖z‖_[p] : WithTop ℝ))`, the
  chapter epigraph owner for the intrinsic `ℓ_p` seminorm;
* bridge/view: the permutation `Prod.swap`, plus the coordinate realization through
  `EuclideanSpace.equiv (Fin n) ℝ`.

Primitive data:
* the admissible exponent `p : EuclideanSpace.LpExponent`;
* the vector `z : EuclideanSpace ℝ (Fin n)`;
* the epigraph height `τ : ℝ`.

Derived API:
* the source-facing owner `lpNormEpigraphCone n p`;
* the intrinsic membership theorem `mem_lpNormEpigraphCone_iff`;
* the coordinate bridge `mem_lpNormEpigraphCone_coord_iff`.

This refinement removes the old coordinate-level owner on `Fin n → ℝ` and makes the intrinsic
Chapter 3 `ℓ_p` seminorm the public core. The raw coordinate presentation survives only as a
bridge theorem, not as a second owner. -/

/-- Definition 5.4.7.6: the epigraph cone of the finite-dimensional `ℓ_p` norm is the set of
pairs `(τ, z)` with `τ ≥ ‖z‖_[p]`, implemented as the chapter constrained epigraph of the
canonical Chapter 3 owner `EuclideanSpace.lpSeminorm n p`, read in the source order `(τ, z)`. -/
def lpNormEpigraphCone (p : EuclideanSpace.LpExponent) : Set (ℝ × Eₙ) :=
  Prod.swap ⁻¹' constrainedEpigraph Set.univ (fun z : Eₙ ↦ (‖z‖_[p] : WithTop ℝ))

/-- Membership in `lpNormEpigraphCone n p` is exactly the intrinsic epigraph inequality
`‖z‖_[p] ≤ τ`. -/
@[simp] theorem mem_lpNormEpigraphCone_iff
    {p : EuclideanSpace.LpExponent} {τ : ℝ} {z : Eₙ} :
    (τ, z) ∈ lpNormEpigraphCone n p ↔ ‖z‖_[p] ≤ τ := by
  change
    ((z, τ) : Eₙ × ℝ) ∈
        constrainedEpigraph Set.univ (fun w : Eₙ ↦ (‖w‖_[p] : WithTop ℝ)) ↔
      ‖z‖_[p] ≤ τ
  rw [mem_constrainedEpigraph_iff]
  simp

/-- Reading the intrinsic epigraph owner through the canonical coordinate identification
`EuclideanSpace.equiv (Fin n) ℝ` recovers the original coordinate inequality
`‖WithLp.toLp p z‖ ≤ τ`. -/
theorem mem_lpNormEpigraphCone_coord_iff
    (p : EuclideanSpace.LpExponent) {τ : ℝ} {z : Fin n → ℝ} :
    (τ, (EuclideanSpace.equiv (Fin n) ℝ).symm z) ∈ lpNormEpigraphCone n p ↔
      ‖WithLp.toLp (p : ENNReal) z‖ ≤ τ := by
  rw [mem_lpNormEpigraphCone_iff, EuclideanSpace.lpNorm_eq_sum]
  rw [PiLp.norm_eq_sum p.toReal_pos (WithLp.toLp (p : ENNReal) z)]
  simp [EuclideanSpace.equiv, Real.norm_eq_abs]

/-! ### Definition_5_4_7_7 (from Chap05) -/
open scoped BigOperators
open scoped PowerCone

noncomputable section

variable (n : ℕ)

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "LpLiftPointₙ" => ℝ × Eₙ × Eₙ

private abbrev liftedPowerConeCoord (τ : ℝ) (x z : Eₙ) (i : Fin n) : ((ℝ × ℝ) × ℝ) :=
  ((x i, τ), z i)

/- Definition 5.4.7.7 lies in the Chapter 5 finite-dimensional `ℓ_p` epigraph / lifted-barrier
domain.

Sampled owner declarations:
* `powerCone` from `Definition_5_4_7_1`, the source-facing symmetric power-cone owner for the
  coordinate triples `((x⁽ⁱ⁾, τ), z⁽ⁱ⁾)`;
* `power_cone_barrier` from `Theorem_5_4_7_3`, the chapter owner of the logarithmic power-cone
  barrier appearing in each summand of `Ψ_α`;
* `logarithmicBarrierDomain` / `LogarithmicBarrierPoint` from `Definition_5_4_5_7`, the chapter
  barrier-owner pattern "strict domain `Set` + subtype carrier + ambient bridge formula";
* `circumscribedEllipsoidBarrierDomain` / `CircumscribedEllipsoidBarrierPoint` from
  `Definition_5_4_5_5`, the same strict-domain pattern for a neighboring logarithmic barrier.

Source/core/bridge triage:
* source-facing: the strict lifted barrier domain `lpEpigraphConeBarrierLiftDomain α` and the
  barrier `lpEpigraphConeBarrierLifted α` on that domain;
* core/canonical: the coordinate owner `power_cone_barrier α` from the earlier power-cone files;
* bridge/view: the ambient finite-sum map `lpEpigraphConeBarrierLiftedAmbient α` and its
  coordinatewise textbook expansion.

Primitive data:
* coordinatewise strict membership in the canonical owner `interior K_[α]`;
* the shared positivity condition `τ > 0`, kept explicit because it is not recoverable from the
  coordinate owner when `n = 0`;
* the normalization equation `∑ i, x⁽ⁱ⁾ = τ`.

Derived API:
* the subtype carrier `LpEpigraphConeBarrierLiftPoint α`;
* the ambient barrier as a sum of the canonical coordinate barriers `power_cone_barrier α`;
* the companion theorem expanding that owner back to the raw textbook logarithmic formula.

This refinement keeps the barrier on its mathematically correct strict lifted domain rather than
on the closed witness set from the previous existence theorem, owns the coordinate strictness via
the earlier power-cone interior `interior K_[α]`, and reuses the chapter power-cone barrier owner
for each coordinate summand instead of duplicating that formula locally.
-/

/-- The lifted domain `𝓗_P` for the `ℓ_p` epigraph cone consists of triples `(τ, x, z)` such that
`x` is coordinatewise nonnegative, the inequalities
`(x^(i))^α τ^(1 - α) ≥ |z^(i)|` hold for every coordinate, and `∑ i, x^(i) = τ`. -/
def lpEpigraphConeLiftDomain (α : ℝ) : Set LpLiftPointₙ :=
  {p |
    (∀ i : Fin n, liftedPowerConeCoord n p.1 p.2.1 p.2.2 i ∈ K_[α]) ∧
      ∑ i : Fin n, p.2.1 i = p.1}

/-- A triple `(τ, x, z)` belongs to `lpEpigraphConeLiftDomain n α` exactly when it satisfies the
coordinatewise lifted `ℓ_p`-epigraph inequalities and the normalization equation
`∑ i, x^(i) = τ`. -/
theorem mem_lpEpigraphConeLiftDomain_iff
    (α τ : ℝ) (x z : Eₙ) :
    (τ, x, z) ∈ lpEpigraphConeLiftDomain n α ↔
      (∀ i : Fin n, 0 ≤ x i) ∧
        (∀ i : Fin n, Real.rpow (x i) α * Real.rpow τ (1 - α) ≥ |z i|) ∧
          ∑ i : Fin n, x i = τ := by
  constructor
  · rintro ⟨hp, hsum⟩
    refine ⟨?_, ?_, hsum⟩
    · intro i
      rcases (mem_powerCone_iff α (x i) τ (z i)).1 (hp i) with ⟨hxi, -, -⟩
      exact hxi
    · intro i
      rcases (mem_powerCone_iff α (x i) τ (z i)).1 (hp i) with ⟨-, -, hzi⟩
      exact hzi
  · rintro ⟨hx, hz, hsum⟩
    refine ⟨?_, hsum⟩
    have hτ : 0 ≤ τ := by
      have hsum_nonneg : 0 ≤ ∑ i : Fin n, x i :=
        Finset.sum_nonneg fun i _ ↦ hx i
      simpa [hsum] using hsum_nonneg
    intro i
    exact (mem_powerCone_iff α (x i) τ (z i)).2 ⟨hx i, hτ, hz i⟩

/-- The strict lifted domain `𝓗_P` on which the lifted `ℓ_p`-epigraph logarithmic barrier is
defined. Its primitive data are coordinatewise strict membership in the canonical power-cone owner
`interior K_[α]`, the shared positivity condition `τ > 0`, and the normalization
`∑ i, x^(i) = τ`. -/
def lpEpigraphConeBarrierLiftDomain (α : ℝ) : Set LpLiftPointₙ :=
  {p |
    (∀ i : Fin n, liftedPowerConeCoord n p.1 p.2.1 p.2.2 i ∈ interior K_[α]) ∧
      0 < p.1 ∧
        (∑ i : Fin n, p.2.1 i) = p.1}

/-- A triple `(τ, x, z)` belongs to `lpEpigraphConeBarrierLiftDomain n α` exactly when each
coordinate lies in `interior K_[α]`, with the shared strictness condition `τ > 0` and the
normalization `∑ i, x^(i) = τ`. -/
theorem mem_lpEpigraphConeBarrierLiftDomain_iff_interior
    (α τ : ℝ) (x z : Eₙ) :
    (τ, x, z) ∈ lpEpigraphConeBarrierLiftDomain n α ↔
      (∀ i : Fin n, liftedPowerConeCoord n τ x z i ∈ interior K_[α]) ∧
        0 < τ ∧
          (∑ i : Fin n, x i) = τ :=
  Iff.rfl

/-- Expanding the owner `interior K_[α]` rewrites strict lifted-domain membership back to the
coordinatewise positivity conditions from Definition 5.4.7.7. -/
theorem mem_lpEpigraphConeBarrierLiftDomain_iff
    (α τ : ℝ) (x z : Eₙ) :
    (τ, x, z) ∈ lpEpigraphConeBarrierLiftDomain n α ↔
      (∀ i : Fin n, 0 < x i) ∧
        0 < τ ∧
          (∀ i : Fin n,
            0 < Real.rpow (x i) (2 * α) * Real.rpow τ (2 * (1 - α)) - (z i) ^ (2 : ℕ)) ∧
            (∑ i : Fin n, x i) = τ := by
  rw [mem_lpEpigraphConeBarrierLiftDomain_iff_interior]
  sorry

/-- The subtype of points in the strict lifted `ℓ_p`-epigraph barrier domain. This is the natural
owner carrier for Definition 5.4.7.7. -/
abbrev LpEpigraphConeBarrierLiftPoint (α : ℝ) :=
  {p : LpLiftPointₙ // p ∈ lpEpigraphConeBarrierLiftDomain n α}

/-- The ambient lifted barrier is the finite sum of the canonical Chapter 5 power-cone barriers on
the coordinate triples `((x^(i), τ), z^(i))`. The barrier itself is obtained by restricting this
ambient map to `LpEpigraphConeBarrierLiftPoint n α`. -/
def lpEpigraphConeBarrierLiftedAmbient (α : ℝ) : LpLiftPointₙ → ℝ
  | (τ, x, z) => ∑ i : Fin n, power_cone_barrier α (liftedPowerConeCoord n τ x z i)

/-- Definition 5.4.7.7: for `α ∈ (0, 1)`, the barrier `Ψ_α` on the strict lifted domain `𝓗_P`
is the restriction of the ambient coordinatewise power-cone barrier sum. -/
def lpEpigraphConeBarrierLifted (α : ℝ) : LpEpigraphConeBarrierLiftPoint n α → ℝ :=
  fun p ↦ lpEpigraphConeBarrierLiftedAmbient n α p.1

/-- Evaluating the ambient lifted `ℓ_p`-epigraph barrier at `(τ, x, z)` is exactly the sum of the
canonical coordinate power-cone barriers. -/
theorem lpEpigraphConeBarrierLiftedAmbient_apply
    (α τ : ℝ) (x z : Eₙ) :
    lpEpigraphConeBarrierLiftedAmbient n α (τ, x, z) =
      ∑ i : Fin n, power_cone_barrier α (liftedPowerConeCoord n τ x z i) :=
  rfl

/-- Expanding the coordinate barrier owner `power_cone_barrier α` rewrites the ambient lifted
barrier back to the textbook logarithmic formula for `Ψ_α(τ, x, z)`. -/
theorem lpEpigraphConeBarrierLiftedAmbient_apply_formula
    (α τ : ℝ) (x z : Eₙ) (hτ : 0 ≤ τ) (hx : ∀ i : Fin n, 0 ≤ x i) :
    lpEpigraphConeBarrierLiftedAmbient n α (τ, x, z) =
      -∑ i : Fin n,
        (Real.log
            (Real.rpow (x i) (2 * α) * Real.rpow τ (2 * (1 - α)) - (z i) ^ (2 : ℕ)) +
          Real.log (x i) + Real.log τ) := by
  unfold lpEpigraphConeBarrierLiftedAmbient
  calc
    ∑ i : Fin n, power_cone_barrier α (liftedPowerConeCoord n τ x z i)
      = ∑ i : Fin n,
          (-(Real.log
              (Real.rpow (x i) (2 * α) * Real.rpow τ (2 * (1 - α)) - (z i) ^ (2 : ℕ)) +
            Real.log (x i) + Real.log τ)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [power_cone_barrier_apply α (x i) τ (z i) (hx i) hτ]
          ring
    _ = -∑ i : Fin n,
          (Real.log
              (Real.rpow (x i) (2 * α) * Real.rpow τ (2 * (1 - α)) - (z i) ^ (2 : ℕ)) +
            Real.log (x i) + Real.log τ) := by
          rw [Finset.sum_neg_distrib]

/-- Evaluating `lpEpigraphConeBarrierLifted n α` on a strict-domain point agrees with the ambient
bridge formula. -/
@[simp] theorem lpEpigraphConeBarrierLifted_apply
    (α : ℝ) (p : LpEpigraphConeBarrierLiftPoint n α) :
    lpEpigraphConeBarrierLifted n α p =
      lpEpigraphConeBarrierLiftedAmbient n α p :=
  rfl

/-- At a strict lifted-domain triple `(τ, x, z)`, the barrier `lpEpigraphConeBarrierLifted n α`
is the sum of the canonical coordinate power-cone barriers. -/
theorem lpEpigraphConeBarrierLifted_apply_triple
    (α τ : ℝ) (x z : Eₙ)
    (h : (τ, x, z) ∈ lpEpigraphConeBarrierLiftDomain n α) :
    lpEpigraphConeBarrierLifted n α ⟨(τ, x, z), h⟩ =
      ∑ i : Fin n, power_cone_barrier α (liftedPowerConeCoord n τ x z i) :=
  rfl

/-- At a strict lifted-domain triple `(τ, x, z)`, the barrier `lpEpigraphConeBarrierLifted n α`
recovers the textbook finite-sum formula for `Ψ_α(τ, x, z)`. -/
theorem lpEpigraphConeBarrierLifted_apply_triple_formula
    (α τ : ℝ) (x z : Eₙ)
    (h : (τ, x, z) ∈ lpEpigraphConeBarrierLiftDomain n α) :
    lpEpigraphConeBarrierLifted n α ⟨(τ, x, z), h⟩ =
      -∑ i : Fin n,
        (Real.log
            (Real.rpow (x i) (2 * α) * Real.rpow τ (2 * (1 - α)) - (z i) ^ (2 : ℕ)) +
          Real.log (x i) + Real.log τ) := by
  rw [mem_lpEpigraphConeBarrierLiftDomain_iff] at h
  have hx : ∀ i : Fin n, 0 ≤ x i := fun i ↦ (h.1 i).le
  have hτ : 0 ≤ τ := h.2.1.le
  simpa [lpEpigraphConeBarrierLifted] using
    lpEpigraphConeBarrierLiftedAmbient_apply_formula n α τ x z hτ hx

end

/-! ### Definition_5_4_7_8 (from Chap05) -/
noncomputable section

open scoped EntropyEpigraph

/-
Definition 5.4.7.8 lies in the Chapter 5 entropy-epigraph / cone-composition domain.

Sampled owner declarations:
* `constrainedEpigraph` and `mem_constrainedEpigraph_iff` from `Chap03/Definition_3_3`, the
  chapter owner for epigraphs over a specified feasible set;
* `ξ` and `Q₂` from `Definition_5_4_7_9`, the entropy-specific map and downstream half-space
  already used by the later barrier theorem;
* `coneCompositionFeasibleSet` and `mem_coneCompositionFeasibleSet_iff` from
  `Definition_5_4_6_3`, the chapter owner for the composed feasible-set construction;
* mathlib `ConvexCone.positive`, the canonical owner for the scalar cone `ℝ₊`.

Best owner abstraction:
* `constrainedEpigraph (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ))
    (fun x : ℝ × ℝ ↦ ((-ξ x : ℝ) : WithTop ℝ))`.

Primitive data:
* the strict positive orthant in the source-facing statement of Definition 5.4.7.8;
* the entropy map `ξ`, whose negative is the relative-entropy height on that orthant.

Derived API:
* the explicit coordinate membership theorem below;
* the cone-composition identification used by the later barrier construction.

Source/core/bridge triage:
* source-facing: `entropyEpigraphCone`;
* core/canonical: `constrainedEpigraph`;
* bridge/view: `entropyEpigraphCone_eq_coneCompositionFeasibleSet`.

The later file `Definition_5_4_7_9` supplies the entropy-specific map `ξ` and the half-space
`Q₂`, while reusing the earlier Chapter 5 orthant owners directly. Definition 5.4.7.8 itself is
the open-domain source-facing constrained epigraph of relative entropy, and the cone-composition
presentation is retained only as a companion bridge for the later barrier theorem. -/

/-- Definition 5.4.7.8: the entropy-epigraph cone is the constrained epigraph of the
relative-entropy height `-ξ(x) = x^(1) [log x^(1) - log x^(2)]` on the strict positive
orthant. -/
def entropyEpigraphCone : Set ((ℝ × ℝ) × ℝ) :=
  constrainedEpigraph
    (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ))
    (fun x : ℝ × ℝ ↦ ((-ξ x : ℝ) : WithTop ℝ))

/-- A triple `((x₁, x₂), z)` lies in `entropyEpigraphCone` exactly when `x₁ > 0`, `x₂ > 0`, and
`z ≥ x₁ (log x₁ - log x₂)`. -/
theorem mem_entropyEpigraphCone_iff (x₁ x₂ z : ℝ) :
    ((x₁, x₂), z) ∈ entropyEpigraphCone ↔
      x₁ > 0 ∧ x₂ > 0 ∧ z ≥ x₁ * (Real.log x₁ - Real.log x₂) := by
  rw [entropyEpigraphCone, mem_constrainedEpigraph_iff]
  constructor
  · rintro ⟨hx, hz'⟩
    have hξ : (-ξ (x₁, x₂) : ℝ) = x₁ * (Real.log x₁ - Real.log x₂) := by
      rw [entropyEpigraphRelativeEntropy_eq_neg_mul_log_sub hx.1 hx.2]
      ring
    have hz : x₁ * (Real.log x₁ - Real.log x₂) ≤ z := by
      exact_mod_cast (show (((x₁ * (Real.log x₁ - Real.log x₂) : ℝ) : WithTop ℝ) ≤ z) from by
        simpa [hξ] using hz')
    refine ⟨hx.1, hx.2, ?_⟩
    simpa using hz
  · rintro ⟨hx₁, hx₂, hz⟩
    have hξ : (-ξ (x₁, x₂) : ℝ) = x₁ * (Real.log x₁ - Real.log x₂) := by
      rw [entropyEpigraphRelativeEntropy_eq_neg_mul_log_sub hx₁ hx₂]
      ring
    have hz' : (((x₁ * (Real.log x₁ - Real.log x₂) : ℝ) : WithTop ℝ) ≤ z) := by
      exact_mod_cast hz
    refine ⟨by simpa using And.intro hx₁ hx₂, ?_⟩
    simpa [hξ] using hz'

/-- The source-facing entropy epigraph cone is exactly the chapter cone-composition feasible set
built from `ξ` and `Q₂`. -/
theorem entropyEpigraphCone_eq_coneCompositionFeasibleSet :
    entropyEpigraphCone =
      coneCompositionFeasibleSet
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ))
        (ConvexCone.positive ℝ ℝ)
        ξ
        Q₂ := by
  ext p
  rcases p with ⟨⟨x₁, x₂⟩, z⟩
  rw [mem_entropyEpigraphCone_iff, mem_coneCompositionFeasibleSet_iff]
  constructor
  · rintro ⟨hx₁, hx₂, hz⟩
    refine ⟨ξ (x₁, x₂), ?_, ?_, ?_⟩
    · simpa using And.intro hx₁ hx₂
    · rw [ConvexCone.mem_positive]
      simp
    · rw [mem_entropyEpigraphQ2_iff]
      have hξ := entropyEpigraphRelativeEntropy_eq_neg_mul_log_sub hx₁ hx₂
      simpa [hξ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        sub_nonneg.mpr hz
  · rintro ⟨y, hx, hy, hz⟩
    have hx₁ : 0 < x₁ := by simpa using hx.1
    have hx₂ : 0 < x₂ := by simpa using hx.2
    have hy_le : y ≤ ξ (x₁, x₂) := by
      rw [ConvexCone.mem_positive] at hy
      exact sub_nonneg.mp hy
    have hyz : -y ≤ z := by
      rw [mem_entropyEpigraphQ2_iff] at hz
      exact neg_le_iff_add_nonneg.mpr <| by simpa [add_comm] using hz
    refine ⟨hx₁, hx₂, ?_⟩
    have hξ := entropyEpigraphRelativeEntropy_eq_neg_mul_log_sub hx₁ hx₂
    have hnegξ : -ξ (x₁, x₂) ≤ z := by
      calc
        -ξ (x₁, x₂) ≤ -y := neg_le_neg hy_le
        _ ≤ z := hyz
    simpa [hξ] using hnegξ

/-! ### Definition_5_4_7_9 (from Chap05) -/
noncomputable section

/- Definition 5.4.7.9 lies in the Chapter 5 entropy-epigraph / cone-composition domain.

Sampled owner declarations:
* `powerConeQ1`, `powerConeBarrier`, and `powerConeBarrierParameter` from
  `Definition_5_4_7_1`, the earlier Chapter 5 owners for the orthant `ℝ_+²`, its logarithmic
  barrier, and the parameter `ν = 2`;
* mathlib `ConvexCone.positive`, the canonical owner for the scalar cone `ℝ_+`;
* `sublevelLogBarrier` from `Theorem_5_1_4`, the chapter owner for barriers of affine half-space
  domains of the form `β - f x > 0`;
* `coneCompositionFeasibleSet` from `Definition_5_4_6_3`, the downstream owner that consumes the
  data assembled here in `Definition_5_4_7_8`.

Best owner abstraction:
* reuse the existing orthant/barrier owners `powerConeQ1`, `powerConeBarrier`, and
  `powerConeBarrierParameter`, together with `ConvexCone.positive ℝ ℝ`;
* keep only the entropy-specific map `ξ` and the affine half-space `Q₂` as new source-facing
  data in this file;
* reuse the canonical half-space barrier specialization
  `sublevelLogBarrier (fun yz : ℝ × ℝ ↦ -yz.1 - yz.2) 0`.

Primitive data:
* the relative-entropy map `entropyEpigraphRelativeEntropy`;
* the half-space `entropyEpigraphQ2`.

Derived API:
* the textbook quotient formula for `entropyEpigraphRelativeEntropy`;
* the positive-orthant bridge rewriting that formula as a logarithmic difference;
* the membership lemma for `entropyEpigraphQ2`;
* the canonical half-space barrier specialization and its pointwise evaluation.

Source/core/bridge triage:
* source-facing: `entropyEpigraphRelativeEntropy` and `entropyEpigraphQ2`;
* core/canonical: `powerConeQ1`, `powerConeBarrier`, `powerConeBarrierParameter`,
  `ConvexCone.positive ℝ ℝ`, and `sublevelLogBarrier`;
* bridge/view: the coordinate evaluation lemmas below.

This refinement removes the duplicate local orthant, orthant-barrier, scalar-cone, and
half-space-barrier-parameter wrappers. Definition 5.4.7.9 now reuses the existing Chapter 5
owners for those pieces, keeps only the entropy-specific data as new declarations, and takes the
textbook quotient formula as the primitive owner rather than storing the positive-orthant
`log x₁ - log x₂` expansion as data. -/

/- Definition 5.4.7.9 reuses the earlier orthant owner `powerConeQ1 = ℝ_+²`. -/
recall powerConeQ1
recall mem_powerConeQ1_iff

/- Definition 5.4.7.9 reuses the earlier orthant logarithmic barrier and its parameter `ν = 2`. -/
recall powerConeBarrier
recall powerConeBarrier_apply
recall powerConeBarrierParameter
recall powerConeBarrierParameter_eq

/- Definition 5.4.7.9 reuses the canonical positive cone `ConvexCone.positive ℝ ℝ` as the scalar
cone `K = ℝ_+`. -/
set_option linter.hashCommand false in
#check (ConvexCone.positive ℝ ℝ : ConvexCone ℝ ℝ)

set_option linter.hashCommand false in
#check ConvexCone.mem_positive

/-- Definition 5.4.7.9: in the entropy-epigraph composition model, the scalar map
`ξ(x) = -x^(1) [log x^(1) - log x^(2)]` is the relative-entropy term on `ℝ²`. -/
def entropyEpigraphRelativeEntropy : (ℝ × ℝ) → ℝ :=
  fun x ↦ -x.1 * Real.log (x.1 / x.2)

namespace EntropyEpigraph

/- Source-facing Lean notation for the textbook entropy-epigraph map `ξ`. -/
scoped notation:max "ξ" => entropyEpigraphRelativeEntropy

end EntropyEpigraph

open scoped EntropyEpigraph

/-- Evaluating `ξ` at `(x₁, x₂)` gives the textbook formula
`-x^(1) log (x^(1) / x^(2))`. -/
theorem entropyEpigraphRelativeEntropy_apply (x₁ x₂ : ℝ) :
    ξ (x₁, x₂) = -x₁ * Real.log (x₁ / x₂) :=
  rfl

-- Proof sketch: on the strict positive orthant, rewrite the logarithm of the quotient with
-- `Real.log_div`.
/- On the strict positive orthant, `ξ` can be written as
`-x^(1) [log x^(1) - log x^(2)]`. -/
theorem entropyEpigraphRelativeEntropy_eq_neg_mul_log_sub
    {x₁ x₂ : ℝ} (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) :
    ξ (x₁, x₂) = -x₁ * (Real.log x₁ - Real.log x₂) := by
  rw [entropyEpigraphRelativeEntropy_apply, Real.log_div hx₁.ne' hx₂.ne']

/-- The half-space `Q₂ = {(y, z) ∈ ℝ × ℝ : y + z ≥ 0}` used in the entropy-epigraph
composition model. -/
def entropyEpigraphQ2 : Set (ℝ × ℝ) :=
  {yz | 0 ≤ yz.1 + yz.2}

namespace EntropyEpigraph

/- Source-facing Lean notation for the textbook entropy-epigraph half-space `Q₂`. -/
scoped notation:max "Q₂" => entropyEpigraphQ2

end EntropyEpigraph

/-- A pair `(y, z)` belongs to `Q₂` exactly when `y + z ≥ 0`. -/
theorem mem_entropyEpigraphQ2_iff (y z : ℝ) :
    (y, z) ∈ Q₂ ↔ 0 ≤ y + z := by
  simp [entropyEpigraphQ2]

/- Definition 5.4.7.9 reuses the canonical logarithmic barrier specialization for
`Q₂ = {(y, z) : y + z ≥ 0}`. -/
set_option linter.hashCommand false in
#check (sublevelLogBarrier (fun yz : ℝ × ℝ ↦ -yz.1 - yz.2) 0 : (ℝ × ℝ) → ℝ)

/-- Evaluating the recalled half-space barrier specialization at `(y, z)` gives the textbook
formula `Φ(y, z) = -log (y + z)`. -/
theorem entropyEpigraphQ2_sublevelLogBarrier_apply (y z : ℝ) :
    sublevelLogBarrier (fun yz : ℝ × ℝ ↦ -yz.1 - yz.2) 0 (y, z) = -Real.log (y + z) := by
  rw [sublevelLogBarrier_apply]
  ring_nf

end

/-! ### Lemma_5_4_7_1 (from Chap05) -/
noncomputable section

attribute [local instance] Chap05RealProdL2.instSeminormedAddCommGroupRealProd
attribute [local instance] Chap05RealProdL2.instNormedAddCommGroupRealProd
attribute [local instance] Chap05RealProdL2.instNormedSpaceRealProd
attribute [local instance] Chap05RealProdL2.instInnerProductSpaceRealProd
attribute [local instance] Chap05RealProdL2.instCompleteSpaceRealProd
attribute [local instance] Chap05RealProdL2.instSeminormedAddCommGroupRealProdProd
attribute [local instance] Chap05RealProdL2.instNormedAddCommGroupRealProdProd
attribute [local instance] Chap05RealProdL2.instNormedSpaceRealProdProd
attribute [local instance] Chap05RealProdL2.instInnerProductSpaceRealProdProd
attribute [local instance] Chap05RealProdL2.instCompleteSpaceRealProdProd

open scoped PowerConePlus

/- Lemma 5.4.7.1 lies in the Chapter 5 power-cone / self-concordant-barrier domain.

Sampled owner declarations:
* `power_cone_plus` from `Definition_5_4_7_4`, the source-facing owner for the one-sided power
  cone `K_α^+`;
* `IsSelfConcordantBarrierOnWith` from `Definition_5_3_2`, the chapter owner for a
  `ν`-self-concordant barrier;
* `IsSelfConcordantBarrierOnWith.barrierParameter_ge_sum_alpha_div_beta_of_recession_directions`
  from `Theorem_5_4_1_2`, the canonical barrier-parameter lower-bound owner theorem;
* `Chap05RealProdL2.instInnerProductSpaceRealProdProd` from `RealProdL2`, the chapter owner
  bridge equipping the raw triple model `((ℝ × ℝ) × ℝ)` with the canonical Euclidean `L²`
  ambient structure needed by the barrier owner theorem.

Source/core/bridge triage:
* source-facing: the lower bound `ν ≥ 3` for barriers on `K_[α]⁺`;
* core/canonical: the barrier owner
  `IsSelfConcordantBarrierOnWith (interior (K_[α]⁺)) ν F`;
* bridge/view: the shared `RealProdL2` ambient-instance activation together with the proof-level
  recession directions `((1, 0), 0)`, `((0, 1), 0)`, and `((0, 0), -1)` and the auxiliary point
  family `((1, 1), -τ)`.

Primitive data:
* the source-facing cone owner `K_[α]⁺`;
* the barrier owner `hF : IsSelfConcordantBarrierOnWith (interior (K_[α]⁺)) ν F`.

Derived API:
* the source-facing lower bound `(3 : ℝ) ≤ (ν : ℝ)`.

The source-facing cone owner `K_[α]⁺` remains the public surface. This file now reuses the
chapter-wide `RealProdL2` ambient bridge instead of repeating local `WithLp` instance blocks, and
the explicit recession directions remain proof-only data rather than public API. -/

-- Proof sketch: apply
-- `barrierParameter_ge_sum_alpha_div_beta_of_recession_directions` directly to the cone
-- `K_[α]⁺` with recession directions `((1, 0), 0)`, `((0, 1), 0)`, and
-- `((0, 0), -1)`, base point `((1, 1), -τ)`, and coefficients
-- `α₁ = α₂ = β₁ = β₂ = 1`, `α₃ = τ`, `β₃ = 1 + τ`. This gives
-- `ν ≥ 2 + τ / (1 + τ)`. Under the contradiction hypothesis `ν < 3`, choosing
-- `τ = ν / (3 - ν)` turns this into `2 + ν / 3 ≤ ν`, which is impossible.
/-- Lemma 5.4.7.1: for `0 < α < 1`, every `ν`-self-concordant barrier for the one-sided power
cone `K_α^+` has barrier parameter at least `3`. -/
theorem power_cone_plus_barrierParameter_ge_three
    {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1)
    {ν : NNReal} {F : ((ℝ × ℝ) × ℝ) → ℝ}
    (hF : IsSelfConcordantBarrierOnWith (interior (K_[α]⁺)) ν F) :
    (3 : ℝ) ≤ (ν : ℝ) := by
  sorry

/-! ### Lemma_5_4_7_2 (from Chap05) -/
noncomputable section

open Matrix
open scoped MatrixOrder RealSymmetricMatrixSpace

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "SymmMat" => 𝕊^n
local notation "Point" => SymmMat × SymmMat
local notation "Z" => WithLp 2 Point
local notation "ofZ" => (WithLp.ofLp : Z → Point)

/- Lemma 5.4.7.2 lies in the Chapter 5 self-concordant-barrier / symmetric-matrix inverse-epigraph
domain.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantBarrierOnWith` in `Chap05/Definition_5_3_2`, the chapter owner for
  `ν`-self-concordant barriers;
* `IsSelfConcordantBarrierOnWith.barrierParameter_ge_sum_alpha_div_beta_of_recession_directions`
  in `Chap05/Theorem_5_4_1_2`, the canonical owner of the recession-direction barrier lower
  bound;
* mathlib `WithLp.prodContinuousLinearEquiv`, the canonical `L²` product bridge between raw pairs
  and the ambient Hilbert-space owner;
* `RealSymmetricMatrixSpace.symmetricMatrixNormedAddCommGroup`,
  `RealSymmetricMatrixSpace.symmetricMatrixNormedSpace`, and
  `RealSymmetricMatrixSpace.symmetricMatrixCompleteSpace` in `Chap05/Definition_5_4_4_2`, the
  chapter owner layer for the intrinsic Frobenius geometry on `𝕊^n`;
* `𝕊^n` in `Chap05/Definition_5_4_4_1`, the chapter owner for real symmetric matrices;
* `𝕊^n₊` in `Chap05/Definition_5_4_4_3`, the positive-semidefinite cone owner;
* `𝕊^n₊₊` in `Chap05/Definition_5_4_4_5`, the intrinsic strict positive-definite cone owner.

Best owner abstraction:
* source-facing: the inverse epigraph `𝓘_n = {(X, Y) | X ≻ 0, Y ⪰ X⁻¹}`;
* core/canonical: the barrier owner on the canonical ambient product `Z = WithLp 2 (𝕊^n × 𝕊^n)`;
* bridge/view: the source-facing raw-pair set `matrixInverseEpigraph` and its pullback along
  `WithLp.ofLp`.

Primitive data:
* `n : ℕ`;
* the source-facing set `matrixInverseEpigraph : Set (𝕊^n × 𝕊^n)`.

Derived API:
* the membership theorem `mem_matrixInverseEpigraph_iff`;
* the barrier-parameter lower bound
  `matrixInverseEpigraph_barrierParameter_ge_two_mul_dimension`.

The previous file encoded points of `𝓘_n` as raw coordinates in the full matrix-entry Euclidean
space and rebuilt projection/instance scaffolding just to recover the symmetric matrices. That
ambient level is too low: the source mathematics is about symmetric matrices and the chapter
already owns `𝕊^n`, `𝕊^n₊₊`, and their Frobenius Hilbert-space structure. This refinement
therefore keeps the public set owner on the intrinsic product `𝕊^n × 𝕊^n`, but moves the barrier
theorem itself to the canonical `L²` product owner `Z = WithLp 2 (𝕊^n × 𝕊^n)` via the bridge
`WithLp.ofLp`. Downstream users now reuse the chapter owner instances directly instead of carrying
any parallel local ambient geometry.
-/

/-- The inverse-epigraph set `𝓘_n = {(X, Y) | X ≻ 0, Y ⪰ X⁻¹}` of symmetric real `n × n`
matrices. -/
def matrixInverseEpigraph : Set Point :=
  {XY | XY.1 ∈ 𝕊^n₊₊ ∧ (XY.1 : Mat)⁻¹ ≤ (XY.2 : Mat)}

/-- A pair `(X, Y)` belongs to `matrixInverseEpigraph` exactly when `X` is positive definite and
`Y` dominates `X⁻¹` in the Löwner order. -/
@[simp] theorem mem_matrixInverseEpigraph_iff (XY : Point) :
    XY ∈ matrixInverseEpigraph ↔
      XY.1 ∈ 𝕊^n₊₊ ∧ (XY.1 : Mat)⁻¹ ≤ (XY.2 : Mat) :=
  Iff.rfl

-- Proof sketch: apply
-- `barrierParameter_ge_sum_alpha_div_beta_of_recession_directions` to
-- `matrixInverseEpigraph` with base point `(γ I, γ I)` for `γ > 1`, recession directions the
-- `2n` rank-one directions `(eᵢ eᵢᵀ, 0)` and `(0, eᵢ eᵢᵀ)`, backward-step coefficients
-- `β = γ - 1 / γ`, and forward coefficients `α = γ - 1`. The combined step reaches `(I, I)`,
-- giving `ν ≥ 2n * γ / (1 + γ)`; letting `γ → ∞` yields `ν ≥ 2n`.
/-- Lemma 5.4.7.2: any self-concordant barrier for the inverse-epigraph set
`𝓘_n = {(X, Y) | X ≻ 0, Y ⪰ X⁻¹}` has parameter at least `2 n`. -/
theorem matrixInverseEpigraph_barrierParameter_ge_two_mul_dimension
    {ν : NNReal} {F : Z → ℝ}
    (hF : IsSelfConcordantBarrierOnWith
      (ofZ ⁻¹' interior matrixInverseEpigraph) ν F) :
    (2 * n : ℝ) ≤ (ν : ℝ) := by
  let Q : Set Z := ofZ ⁻¹' matrixInverseEpigraph
  have hQ_interior :
      interior Q = ofZ ⁻¹' interior matrixInverseEpigraph := by
    simpa [Q] using
      ((WithLp.prodContinuousLinearEquiv 2 ℝ SymmMat SymmMat).toHomeomorph.preimage_interior
        matrixInverseEpigraph).symm
  have hF' : IsSelfConcordantBarrierOnWith (interior Q) ν F := by
    simpa [hQ_interior] using hF
  letI : IsSelfConcordantBarrierOnWith (interior Q) ν F := hF'
  sorry

end

/-! ### Theorem_5_4_7_1 (from Chap05) -/
noncomputable section

open scoped PowerConeGeometricMean

/- Theorem 5.4.7.1 lies in the Chapter 5 power-cone / directional-derivative domain.

Sampled owner declarations:
* `powerConeGeometricMean` from `Definition_5_4_7_1`, the source-facing owner for the weighted
  geometric mean `ξ(x) = (x^(1))^α (x^(2))^(1 - α)`;
* mathlib `lineDeriv`, the canonical first directional-derivative owner;
* `secondDirectionalDerivative` from `Definition_5_0_10`, the chapter owner for
  `D²f(x)[h,h]`;
* `thirdDirectionalDerivative` from `Definition_5_0_10`, the chapter owner for
  `D³f(x)[h,h,h]`.

Source/core/bridge triage:
* source-facing: the explicit directional-derivative formulas for the weighted geometric mean;
* core/canonical: `lineDeriv`, `secondDirectionalDerivative`, and `thirdDirectionalDerivative`
  applied to `powerConeGeometricMean α`;
* bridge/view: no extra wrapper beyond those direct owner specializations.

Primitive data:
* the exponent `α`;
* the base point `x` and direction `h`;
* positivity of the two coordinates of `x`.

Derived API:
* the explicit first-, second-, and third-directional-derivative identities below.

The file therefore keeps the source-facing formulas but states them directly on the canonical
directional-derivative owners already fixed earlier in the chapter, rather than introducing a
parallel local slice-level API.
-/

section

variable {α : ℝ} {x h : ℝ × ℝ}

local notation "ξ" => ξ[α]

-- Proof sketch: differentiate the directional slice
-- `t ↦ ξ (x + t • h)` at `t = 0`, use the positive coordinate assumptions to identify the
-- derivatives of the two `Real.rpow` factors, and factor out `ξ x`.
/-- Theorem 5.4.7.1 (1): the first directional derivative of
`ξ(x) = (x^(1))^α (x^(2))^(1 - α)` at a point with positive coordinates satisfies
`Dξ(x)[h] = [α (h^(1) / x^(1)) + (1 - α) (h^(2) / x^(2))] ξ(x)`. -/
theorem powerConeGeometricMean_firstDirectionalDerivative
    (hx₁ : 0 < x.1) (hx₂ : 0 < x.2)
    :
    lineDeriv ℝ ξ x h =
      (α * (h.1 / x.1) + (1 - α) * (h.2 / x.2)) * ξ x := sorry

-- Proof sketch: differentiate the first-derivative identity once more along the same direction
-- `h`; the derivative of `h.1 / x.1` contributes `-(h.1 / x.1)^2` and similarly for the second
-- coordinate, after which the algebra simplifies to
-- `-α (1 - α) ((h.1 / x.1) - (h.2 / x.2))^2 ξ(x)`.
/-- Theorem 5.4.7.1 (2): the second directional derivative of
`ξ(x) = (x^(1))^α (x^(2))^(1 - α)` at a point with positive coordinates satisfies
`D²ξ(x)[h,h] = -α (1 - α) ((h^(1) / x^(1)) - (h^(2) / x^(2)))² ξ(x)`. -/
theorem powerConeGeometricMean_secondDirectionalDerivative
    (hx₁ : 0 < x.1) (hx₂ : 0 < x.2)
    :
    secondDirectionalDerivative ξ x h =
      (-α * (1 - α) * (h.1 / x.1 - h.2 / x.2) ^ (2 : ℕ)) * ξ x := sorry

-- Proof sketch: differentiate the second-derivative identity from part `(2)` along `h`, use the
-- first-derivative formula from part `(1)` to rewrite the derivative of `ξ`, and factor out the
-- common term `D²ξ(x)[h,h]`.
/-- Theorem 5.4.7.1 (3): the third directional derivative of
`ξ(x) = (x^(1))^α (x^(2))^(1 - α)` at a point with positive coordinates satisfies
`D³ξ(x)[h,h,h] =
  -D²ξ(x)[h,h] ((2 - α) (h^(1) / x^(1)) + (1 + α) (h^(2) / x^(2)))`. -/
theorem powerConeGeometricMean_thirdDirectionalDerivative
    (hx₁ : 0 < x.1) (hx₂ : 0 < x.2)
    :
    thirdDirectionalDerivative ξ x h =
      -secondDirectionalDerivative ξ x h *
        ((2 - α) * (h.1 / x.1) + (1 + α) * (h.2 / x.2)) := sorry

end

/-! ### Theorem_5_4_7_10 (from Chap05) -/
open scoped BigOperators RelativeDirection MonomialXi StandardSimplex
open EuclideanSpace (positiveOrthant)

noncomputable section

variable {n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Xₙ" => positiveOrthant n

/- Theorem 5.4.7.10 lies in the Chapter 5 simplex-monomial / positive-orthant directional-
derivative domain.

Sampled owner declarations:
* `lineDerivWithin` from mathlib, the canonical owner for within-domain directional derivatives
  along affine lines;
* `ambientMonomialXi` and `ξ_[a]` from `Definition_5_4_7_17`, the ambient/source-facing owners
  for the simplex monomial;
* `lineDerivWithin_log_monomialXi_eq_centerMass_relativeDirection` from `Theorem_5_4_7_9`, the
  adjacent owner-level logarithmic derivative identity this theorem builds on;
* `Finset.centerMass` together with the notation `δ[x](h)` from `Definition_5_4_7_14` and
  `Definition_5_4_7_18`, the canonical weighted-mean owner and the source-facing relative
  direction.

Source/core/bridge triage:
* source-facing: the textbook identity `D ξ_a(x)[h] = ξ_a(x) ⟪a, δ_x(h)⟫`;
* core/canonical: `lineDerivWithin ℝ (ambientMonomialXi a) Xₙ x h`;
* bridge/view: the source-facing value `ξ_[a] x` and the logarithmic derivative theorem from
  `Theorem_5_4_7_9`.

This file therefore stays as a thin bridge theorem over the ambient owner `lineDerivWithin`; it
keeps no parallel logarithmic-derivative wrapper, and it treats Theorem 5.4.7.9 as the upstream
owner-level input rather than restating that API locally.
-/

-- Proof sketch: combine the scalar chain rule for `exp` with the logarithmic derivative identity
-- from `Theorem_5_4_7_9`, using that on the strict positive orthant
-- `ambientMonomialXi a = Real.exp ∘ (Real.log ∘ ambientMonomialXi a)`, and then rewrite the
-- value term by `ambientMonomialXi_eq_monomialXi`.
/-- Theorem 5.4.7.10: for `a ∈ Δₙ`, the directional derivative of the monomial `ξ_a` at a
strictly positive point `x` along `h` is
`ξ_a(x) Finset.univ.centerMass a (δ_x(h)) = ξ_a(x) ⟪a, δ_x(h)⟫`. -/
theorem lineDerivWithin_monomialXi_eq_monomialXi_mul_centerMass_relativeDirection
    (a : Δ[n]) (x : Xₙ) (h : Eₙ) :
    lineDerivWithin ℝ (ambientMonomialXi a) Xₙ x h =
      ξ_[a] x * Finset.univ.centerMass a (δ[x](h)) := by
  sorry

end

/-! ### Theorem_5_4_7_11 (from Chap05) -/
open scoped BigOperators RelativeDirection MonomialXi StandardSimplex
open EuclideanSpace (positiveOrthant)

noncomputable section

variable {n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Xₙ" => positiveOrthant n

/- Theorem 5.4.7.11 lies in the Chapter 5 simplex-monomial / directional-second-derivative
domain.

Sampled owner declarations:
* `secondDirectionalDerivative` in `Definition_5_0_10`, the chapter owner for `D²f(x)[h,h]`;
* `ambientMonomialXi` and `ξ_[a]` in `Definition_5_4_7_17`, the simplex monomial owner and its
  ambient/source-facing bridge;
* `quantityS2` in `Definition_5_4_7_18`, the source-facing weighted centered second moment of the
  relative direction.

Source/core/bridge triage:
* source-facing: Theorem 5.4.7.11's identity `D² ξ_a(x)[h,h] = -ξ_a(x) S₂`;
* core/canonical: `secondDirectionalDerivative (ambientMonomialXi a) x h`;
* bridge/view: the expanded quadratic polynomial in the weighted mean
  `Finset.univ.centerMass a (δ[x](h))` and weighted square sum
  `a ⬝ᵥ fun i ↦ (δ[x](h) i) ^ (2 : ℕ)`.

The file is therefore downstream from the existing owners `secondDirectionalDerivative`,
`ambientMonomialXi`, `ξ_[a]`, and `quantityS2`. It keeps only the derivative theorem and its
explicit bridge formula, rather than restating any local wrapper for the monomial, the relative
direction, or the centered second moment. -/

-- Proof sketch: differentiate the directional slice of the ambient monomial once more along the
-- repeated direction `h`, rewrite the derivative of each relative coordinate `h i / x i` as
-- `-(h i / x i)^2`, and factor the result into `ξ_a(x)` times the weighted mean square minus the
-- weighted square sum.
/-- The second directional derivative of the simplex monomial `ξ_a` admits the expanded formula
`ξ_a(x) (m^2 - ⟪a, [δ]^2⟫)`, where `δ = δ_x(h)` and
`m = Finset.univ.centerMass a (δ[x](h)) = ⟪a, δ⟫`. -/
theorem monomialXi_secondDirectionalDerivative_eq_mul_quadratic_relativeDirection_polynomial
    (a : Δ[n]) (x : Xₙ) (h : Eₙ) :
    secondDirectionalDerivative (ambientMonomialXi a) x h =
        ξ_[a] x *
          (Finset.univ.centerMass a (δ[x](h)) ^ (2 : ℕ) -
            a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i) ^ (2 : ℕ)) := sorry

-- Proof sketch: combine the expanded second-derivative formula with the identity
-- `quantityS2 a x h = ⟪a, [δ_x(h)]^2⟫ - ⟪a, δ_x(h)⟫^2`, so the bracket equals `-S₂`.
/-- Theorem 5.4.7.11: the second directional derivative of `ξ_a` on the positive orthant equals
`-ξ_a(x) S₂`, where `S₂ = quantityS2 a x h` is the weighted second centered moment of the
relative direction `δ_x(h)`. -/
theorem monomialXi_secondDirectionalDerivative_eq_neg_mul_quantityS2
    (a : Δ[n]) (x : Xₙ) (h : Eₙ) :
    secondDirectionalDerivative (ambientMonomialXi a) x h =
        -(ξ_[a] x * quantityS2 a x h) := sorry

end

/-! ### Theorem_5_4_7_12 (from Chap05) -/
open scoped BigOperators RelativeDirection MonomialXi StandardSimplex
open EuclideanSpace (positiveOrthant)

noncomputable section

variable {n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Xₙ" => positiveOrthant n

/- Theorem 5.4.7.12 lies in the chapter's simplex-monomial / directional-derivative domain.

Sampled owner declarations:
* `thirdDirectionalDerivative` in `Definition_5_0_10`, the chapter owner for
  `D³f(x)[h,h,h]`;
* `ambientMonomialXi` and `ξ_[a]` in `Definition_5_4_7_17`, the simplex monomial owner and its
  ambient bridge;
* `quantityS2` in `Definition_5_4_7_18`, the weighted centered second moment;
* `quantityS3` in `Definition_5_4_7_19`, the weighted centered third moment.

Source/core/bridge triage:
* source-facing: the explicit formulas for the third directional derivative of `ξ_a`;
* core/canonical: `thirdDirectionalDerivative (ambientMonomialXi a) x h`;
* bridge/view: the expanded cubic polynomial in the weighted mean and its reformulation in terms
  of `S₂` and `S₃`.

This file therefore keeps the theorem content but uses the chapter owner
`thirdDirectionalDerivative` as the public derivative surface, rather than restating the raw
`iteratedFDerivWithin` expression.
-/

section

variable (a : Δ[n]) (x : Xₙ) (h : Eₙ)

local notation "m" => Finset.univ.centerMass a (δ[x](h))

-- Proof sketch: differentiate the second-derivative identity for `ξ_a` along the repeated
-- direction `h`, use `D ξ_a(x)[h] = ξ_a(x) m`, `D m[h] = -⟪a, [δ]^2⟫`, and
-- `D ⟪a, [δ]^2⟫[h] = -2 ⟪a, [δ]^3⟫`, then factor out the common multiplicative term `ξ_a(x)`.
/-- The third directional derivative of the simplex monomial `ξ_a` equals `ξ_a(x)` times the
cubic polynomial in the weighted mean
`m = Finset.univ.centerMass a (δ[x](h)) = ⟪a, δ_x(h)⟫`, the weighted square sum
`⟪a, [δ_x(h)]^2⟫`, and the weighted cube sum `⟪a, [δ_x(h)]^3⟫`. -/
theorem monomialXi_thirdDirectionalDerivative_eq_mul_cubic_relativeDirection_polynomial :
    thirdDirectionalDerivative (ambientMonomialXi a) x h =
        ξ_[a] x *
          (m ^ (3 : ℕ) -
            3 * m * (a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i) ^ (2 : ℕ)) +
            2 * (a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i) ^ (3 : ℕ))) := sorry

-- Proof sketch: start from the expanded cubic formula for the third derivative, expand the
-- centered-cube quantity `S₃`, use the definition of `S₂` as the weighted centered square sum,
-- and collect like terms in `m`.
/-- Theorem 5.4.7.12: the third directional derivative of `ξ_a` on the positive orthant equals
`ξ_a(x) (2 S₃ + 3 m S₂)`, where `m = ⟪a, δ_x(h)⟫`,
`S₂ = quantityS2 a x h`, and
`S₃ = quantityS3 a x h`. -/
theorem monomialXi_thirdDirectionalDerivative_eq_mul_two_S3_add_three_mean_S2 :
    thirdDirectionalDerivative (ambientMonomialXi a) x h =
        ξ_[a] x * (2 * quantityS3 a x h + 3 * m * quantityS2 a x h) := sorry

end

end

/-! ### Theorem_5_4_7_13 (from Chap05) -/
open scoped HessianLocalNorm MonomialXi StandardSimplex
open EuclideanSpace (positiveOrthant)

noncomputable section

variable {n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Xₙ" => positiveOrthant n

/- Theorem 5.4.7.13 lies in the Chapter 5 simplex-monomial / barrier-compatibility domain.

Sampled owner declarations:
* `IsBetaCompatibleWith` from `Definition_5_4_6_2`, the chapter owner for compatibility with a
  self-concordant barrier;
* `ambientMonomialXi` and `ξ_[a]` from `Definition_5_4_7_17`, the simplex-monomial owner and its
  ambient bridge;
* `monomialXi_secondDirectionalDerivative_eq_neg_mul_quantityS2` from `Theorem_5_4_7_11`, the
  owner-level formula for `D² ξ_a`;
* `monomialXi_thirdDirectionalDerivative_eq_mul_two_S3_add_three_mean_S2` from
  `Theorem_5_4_7_12`, the owner-level formula for `D³ ξ_a`;
* `positiveOrthantLogarithmicBarrier_localNorm_eq_norm_relativeDirection` from
  `Theorem_5_4_7_8`, the bridge identifying the barrier local norm with the relative-direction
  norm.

Source/core/bridge triage:
* source-facing: the textbook `β = 1` compatibility statement for the monomial `ξ_a`;
* core/canonical: `IsBetaCompatibleWith` on `positiveOrthant n`;
* bridge/view: the derivative identities for `ξ_a` and the local-norm formula for the orthant
  logarithmic barrier.

The public statement is already at the correct owner level, so this file keeps that owner surface
and avoids introducing any parallel wrapper around the ambient monomial or the barrier.
-/

private theorem positiveOrthant_eq_preimage_piIoi :
    (Xₙ : Set Eₙ) =
      ((EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph) ⁻¹'
        Set.pi Set.univ (fun _ : Fin n ↦ Set.Ioi (0 : ℝ)) := by
  ext x
  simp [EuclideanSpace.positiveOrthant]

private theorem positiveOrthant_isOpen : IsOpen (Xₙ : Set Eₙ) := by
  rw [positiveOrthant_eq_preimage_piIoi]
  exact (isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_Ioi).preimage
    ((EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph.continuous)

private theorem positiveOrthant_convex : Convex ℝ (Xₙ : Set Eₙ) := by
  rw [positiveOrthant_eq_preimage_piIoi]
  exact (convex_pi fun _ _ ↦ convex_Ioi (0 : ℝ)).linear_preimage
    (EuclideanSpace.equiv (Fin n) ℝ).toLinearMap

private theorem positiveOrthant_interior_eq : interior (Xₙ : Set Eₙ) = Xₙ :=
  positiveOrthant_isOpen.interior_eq

private theorem positiveOrthant_interior_nonempty :
    (interior (Xₙ : Set Eₙ)).Nonempty := by
  have hx : WithLp.toLp 2 (fun _ : Fin n ↦ (1 : ℝ)) ∈ Xₙ := by
    rw [EuclideanSpace.mem_positiveOrthant_iff]
    intro j
    exact (zero_lt_one : (0 : ℝ) < 1)
  exact ⟨_, by rwa [positiveOrthant_interior_eq]⟩

private theorem ambientMonomialXi_contDiffOn_positiveOrthant (a : Δ[n]) :
    ContDiffOn ℝ 3 (ambientMonomialXi a) (Xₙ : Set Eₙ) := by
  unfold ambientMonomialXi
  refine contDiffOn_prod fun i _ ↦ ?_
  have hcoord : ContDiffOn ℝ 3 (fun x : Eₙ ↦ x i) (Xₙ : Set Eₙ) := by
    simpa using
      (show ContDiffOn ℝ 3 (fun x : Eₙ ↦ x i) (Xₙ : Set Eₙ) from
        contDiffOn_piLp_apply (2 : ENNReal))
  exact hcoord.rpow_const_of_ne fun x hx ↦
    ne_of_gt ((EuclideanSpace.mem_positiveOrthant_iff.mp hx) i)

private theorem standardLogarithmicBarrierAmbient_isSelfConcordantBarrierOn_positiveOrthant :
    IsSelfConcordantBarrierOnWith (Xₙ : Set Eₙ) (n : NNReal)
      (standardLogarithmicBarrierAmbient n) := by
  sorry

private theorem monomialXi_compatibility_bound
    (a : Δ[n]) {x : Eₙ} (hx : x ∈ Xₙ) (h : Eₙ) :
    (3 * ‖h‖[standardLogarithmicBarrierAmbient n; x]) •
        (-vectorSecondDirectionalDerivative (ambientMonomialXi a) x h) -
      vectorThirdDirectionalDerivative (ambientMonomialXi a) x h ∈
        ConvexCone.positive ℝ ℝ := by
  sorry

-- Proof sketch: use the explicit formulas for the second and third directional derivatives of the
-- monomial `x ↦ x^a`, rewrite the third derivative in terms of the centered quantities `S₂` and
-- `S₃`, bound `S₃` by `S₂ * ‖δ_x(h)‖`, and then identify `‖δ_x(h)‖` with the local norm of the
-- positive-orthant logarithmic barrier.
/-- Theorem 5.4.7.13: for `a ∈ Δₙ`, the monomial
`ξ_a(x) = x^a = ∏_{i=1}^n (x^(i))^(a^(i))` is `1`-compatible with the logarithmic barrier
`F(x) = -\sum_{i=1}^n \log x^(i)` on the strict positive orthant `\mathbb{R}^n_{++}`. -/
theorem monomial_isOneCompatibleWith_positiveOrthantLogarithmicBarrier
    (a : Δ[n]) :
    IsBetaCompatibleWith
      Xₙ
      (ConvexCone.positive ℝ ℝ)
      (standardLogarithmicBarrierAmbient n)
      (1 : NNReal)
      (ambientMonomialXi a) := by
  refine
    { convex_domain := positiveOrthant_convex
      interior_nonempty := positiveOrthant_interior_nonempty
      one_le_parameter := by norm_num
      selfConcordantBarrier := ?_
      contDiffOn := ?_
      compatibility_bound := ?_ }
  · refine ⟨(n : NNReal), ?_⟩
    simpa [positiveOrthant_interior_eq] using
      standardLogarithmicBarrierAmbient_isSelfConcordantBarrierOn_positiveOrthant
  · simpa [positiveOrthant_interior_eq] using
      ambientMonomialXi_contDiffOn_positiveOrthant a
  · intro x hx h
    simpa [one_mul, positiveOrthant_interior_eq] using
      monomialXi_compatibility_bound a (by simpa [positiveOrthant_interior_eq] using hx) h

/-! ### Theorem_5_4_7_14 (from Chap05) -/
open scoped BigOperators Gradient MonomialXi StandardSimplex
open EuclideanSpace (positiveOrthant)

noncomputable section

variable {n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Xₙ" => positiveOrthant n

/- Theorem 5.4.7.14 lies in the Chapter 5 posynomial / positive-orthant barrier-compatibility
domain.

Sampled owner declarations:
* `ambientMonomialXi` and `ξ_[a]` from `Definition_5_4_7_17`, the ambient/source-facing owners for
  simplex monomials;
* `IsBetaCompatibleWith` from `Definition_5_4_6_2`, the chapter owner for barrier compatibility;
* `IsBetaCompatibleWith.smul` and `IsBetaCompatibleWith.add` from `Theorem_5_4_6_2`, the canonical
  closure API for positive combinations;
* `monomial_isOneCompatibleWith_positiveOrthantLogarithmicBarrier` from `Theorem_5_4_7_13`, the
  monomial compatibility owner theorem.

Best owner abstraction:
* source-facing: `posynomialXi` on the strict positive orthant;
* core/canonical: `IsBetaCompatibleWith` applied to the ambient finite sum of monomial terms;
* bridge/view: evaluation of that ambient finite sum on `positiveOrthant n`.

Primitive data:
* the positive coefficients `α : Fin m → Set.Ioi (0 : ℝ)`;
* the simplex exponents `a : Fin m → Δ[n]`.

Derived API:
* the source-facing owner `posynomialXi`;
* its evaluation lemma `posynomialXi_apply`;
* the bridge lemma identifying the corresponding ambient finite sum with `posynomialXi` on
  `positiveOrthant n`;
* the compatibility theorem for that ambient finite sum.

The previous version introduced a second public owner `ambientPosynomialXi` whose only role was to
repackage the ambient finite combination already determined by the monomial owners and the
`IsBetaCompatibleWith` closure API. This refinement keeps `posynomialXi` as the public owner,
adds a named bridge from the canonical ambient finite sum to `posynomialXi`, and uses that bridge
to keep the source-facing posynomial connected to the ambient compatibility surface without
preserving a parallel wrapper.
-/

/-- The posynomial `ξ(x) = \sum_{k=1}^m α_k x^{a_k}` on the strict positive orthant. -/
def posynomialXi
    (n m : ℕ)
    (α : Fin m → Set.Ioi (0 : ℝ))
    (a : Fin m → Δ[n]) :
    positiveOrthant n → ℝ :=
  ∑ k : Fin m, (α k : ℝ) • ξ_[(a k)]

/-- Evaluating `posynomialXi n m α a` at a positive vector gives the textbook sum formula. -/
@[simp] theorem posynomialXi_apply
    (n m : ℕ)
    (α : Fin m → Set.Ioi (0 : ℝ))
    (a : Fin m → Δ[n])
    (x : positiveOrthant n) :
    posynomialXi n m α a x =
      ∑ k : Fin m, (α k : ℝ) * ξ_[(a k)] x := by
  simp [posynomialXi, smul_eq_mul]

/-- Restricting the canonical ambient finite sum of monomial terms to the strict positive orthant
recovers the source-facing posynomial `posynomialXi n m α a`. -/
@[simp] theorem sum_smul_ambientMonomialXi_eq_posynomialXi
    (n m : ℕ)
    (α : Fin m → Set.Ioi (0 : ℝ))
    (a : Fin m → Δ[n])
    (x : positiveOrthant n) :
    (∑ k : Fin m, (α k : ℝ) • ambientMonomialXi (a k)) x = posynomialXi n m α a x := by
  simp [posynomialXi, smul_eq_mul]

private theorem zero_isOneCompatibleWith_positiveOrthantLogarithmicBarrier :
    IsBetaCompatibleWith
      (positiveOrthant n)
      (ConvexCone.positive ℝ ℝ)
      (standardLogarithmicBarrierAmbient n)
      (1 : NNReal)
      (0 : Eₙ → ℝ) := by
  sorry

/-- Theorem 5.4.7.14: the posynomial
`ξ(x) = \sum_{k=1}^m α_k x^{a_k}` with positive coefficients and simplex exponents is
`1`-compatible with the logarithmic barrier
`F(x) = -\sum_{i=1}^n \log x^{(i)}` on the positive orthant `\mathbb{R}^n_{++}`. -/
theorem posynomialXi_isOneCompatibleWith_positiveOrthantLogarithmicBarrier
    (m : ℕ)
    (α : Fin m → Set.Ioi (0 : ℝ))
    (a : Fin m → Δ[n]) :
    IsBetaCompatibleWith
      (positiveOrthant n)
      (ConvexCone.positive ℝ ℝ)
      (standardLogarithmicBarrierAmbient n)
      (1 : NNReal)
      (∑ k : Fin m, (α k : ℝ) • ambientMonomialXi (a k)) := by
  -- The ambient function in the compatibility statement restricts to `posynomialXi n m α a`
  -- by `sum_smul_ambientMonomialXi_eq_posynomialXi`.
  induction m with
  | zero =>
      simpa using zero_isOneCompatibleWith_positiveOrthantLogarithmicBarrier
  | succ m ih =>
      have hhead :
          IsBetaCompatibleWith
            (positiveOrthant n)
            (ConvexCone.positive ℝ ℝ)
            (standardLogarithmicBarrierAmbient n)
            (1 : NNReal)
            ((α 0 : ℝ) • ambientMonomialXi (a 0)) := by
        simpa using
          IsBetaCompatibleWith.smul
            (monomial_isOneCompatibleWith_positiveOrthantLogarithmicBarrier (a 0))
            ⟨α 0, (α 0).2.le⟩
      have htail :
          IsBetaCompatibleWith
            (positiveOrthant n)
            (ConvexCone.positive ℝ ℝ)
            (standardLogarithmicBarrierAmbient n)
            (1 : NNReal)
            (∑ k : Fin m, ((α k.succ : Set.Ioi (0 : ℝ)) : ℝ) • ambientMonomialXi (a k.succ)) :=
        ih (fun k ↦ α k.succ) (fun k ↦ a k.succ)
      simpa [Fin.sum_univ_succ] using IsBetaCompatibleWith.add hhead htail

end

/-! ### Theorem_5_4_7_15 (from Chap05) -/
universe u

/- Theorem 5.4.7.15 lies in the same self-concordant-barrier / exponential-transform domain as
Lemma 5.3.1.

Sampled owner-style declarations:
* `IsSelfConcordantBarrierOnWith` in `Definition_5_3_2`, the barrier owner;
* `IsSelfConcordantBarrierOnWith.concaveOn_exp_neg_div` in `Lemma_5_3_1`, already stated with the
  exact interface required here;
* `isSelfConcordantBarrierOnWith_iff_concaveOn_exp_neg_div` in `Lemma_5_3_1`, the numbered
  source-facing characterization built from that owner theorem.

Best owner abstraction:
* `IsSelfConcordantBarrierOnWith.concaveOn_exp_neg_div`.

Primitive data:
* none in this file beyond the owner theorem's existing parameters.

Derived API:
* this recall-only source-facing entry point.

Source/core/bridge triage:
* source-facing: the textbook statement of Theorem 5.4.7.15;
* core/canonical: `IsSelfConcordantBarrierOnWith.concaveOn_exp_neg_div`;
* bridge/view: this recall surface.

The previous file duplicated the owner theorem from `Lemma_5_3_1` with the same interface. This
refinement removes that parallel theorem and reuses the canonical owner-level declaration
directly. -/

/- Theorem 5.4.7.15 is `IsSelfConcordantBarrierOnWith.concaveOn_exp_neg_div`. -/
recall IsSelfConcordantBarrierOnWith.concaveOn_exp_neg_div

/-! ### Theorem_5_4_7_2 (from Chap05) -/
noncomputable section

open scoped PowerConeGeometricMean

/- Theorem 5.4.7.2 lies in the Chapter 5 power-cone compatibility domain.

Sampled owner declarations:
* `powerConeGeometricMean`, `powerConeQ1`, and `powerConeBarrier` from `Definition_5_4_7_1`, the
  earlier source-facing power-cone data on raw pairs;
* `IsBetaCompatibleWith` from `Definition_5_4_6_2`, the chapter owner for compatibility;
* `Chap05RealProdL2.instInnerProductSpaceRealProd` from `RealProdL2`, the chapter owner bridge
  equipping the raw pair model `ℝ × ℝ` with the canonical Euclidean `L²` ambient structure;
* `entropyEpigraphRelativeEntropy_isOneCompatibleWith_powerConeBarrier` from
  `Theorem_5_4_7_6`, the nearby compatibility theorem on the same raw-pair orthant owner.

Source/core/bridge triage:
* source-facing: the `β = 1` compatibility theorem for the weighted geometric mean on `Q₁`;
* core/canonical: `IsBetaCompatibleWith` together with the raw-pair owners from
  `Definition_5_4_7_1`;
* bridge/view: the chapter `RealProdL2` owner activation that realizes the raw pair ambient
  structure through the canonical `L²` model.

Primitive data:
* the orthant `powerConeQ1`;
* the orthant barrier `powerConeBarrier`;
* the scalar cone `ConvexCone.positive ℝ ℝ`;
* the weighted geometric mean `ξ[α]`.

Derived API:
* the `β = 1` compatibility theorem below.

This file therefore reuses the raw-pair owners directly and keeps no parallel `WithLp` pullback
copy of the same compatibility statement. -/

attribute [local instance] Chap05RealProdL2.instSeminormedAddCommGroupRealProd
attribute [local instance] Chap05RealProdL2.instNormedAddCommGroupRealProd
attribute [local instance] Chap05RealProdL2.instNormedSpaceRealProd
attribute [local instance] Chap05RealProdL2.instInnerProductSpaceRealProd
attribute [local instance] Chap05RealProdL2.instCompleteSpaceRealProd

-- Proof sketch: use the explicit formula for `D³ξ(x)[h,h,h]` in terms of `-D²ξ(x)[h,h]`, and
-- compute `hessianLocalNorm powerConeBarrier x h` as
-- `((h.1 / x.1)^2 + (h.2 / x.2)^2)^(1/2)` on the positive orthant. Cauchy--Schwarz then bounds
-- the linear factor `((2 - α) (h.1 / x.1) + (1 + α) (h.2 / x.2))` by
-- `3 * hessianLocalNorm powerConeBarrier x h` when `0 < α < 1`, yielding the defining cone-order
-- inequality in the positive cone of `ℝ`.
/-- Theorem 5.4.7.2: for `0 < α < 1`, the weighted geometric mean
`ξ(x) = (x^(1))^α (x^(2))^(1 - α)` is `1`-compatible with the logarithmic barrier
`F(x) = -log x^(1) - log x^(2)` on the orthant `Q₁ = ℝ_+²`, relative to the scalar cone
`ℝ_+`. -/
theorem powerConeGeometricMean_isOneCompatibleWith_powerConeBarrier
    {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    IsBetaCompatibleWith powerConeQ1 (ConvexCone.positive ℝ ℝ)
      powerConeBarrier (1 : NNReal) ξ[α] := by
  sorry
