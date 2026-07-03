import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_29 (from Chap07) -/
noncomputable section

open Matrix
open scoped EllipsoidNotation

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- Definition 7.29 lies in the Chapter 7 centered ellipsoid-rounding domain.

Sampled owner-style declarations:
- `matrixEllipsoid` in `Chap07/Definition_7_26`, the source-facing ellipsoid owner;
- `centeredMatrixEllipsoid_one_eq_affineEllipsoid` in `Chap07/Definition_7_26`, the unit-radius
  bridge for centered ellipsoids;
- `IsBetaRounding` in `Chap07/Definition_7_27`, the chapter owner of ellipsoid roundings with
  arbitrary center and outer radius;
- `IsGammaNRounding` in `Chap07/Definition_7_32`, a nearby positive-definite rounding predicate
  built on the same `W[r](v, G)` ellipsoid surface.

Best owner abstraction:
- source-facing: `IsEllipsoidalRounding` and `IsInitialApproximation`;
- core/canonical: `IsBetaRounding`;
- bridge/view: the centered specialization `v = 0` and the fixed outer radius
  `β = γ * Real.sqrt (n : ℝ)`.

Primitive data:
- a set `C : Set E`;
- a matrix `G : Mat`;
- positive definiteness of `G`;
- a centered `β`-rounding of `C`.

Derived API:
- the unit centered ellipsoid inclusion `W[1](G) ⊆ C`;
- the outer inclusion `C ⊆ W[(γ * Real.sqrt (n : ℝ))](G)`;
- the `Fact` instance and the existential outer-radius view for initial approximations.

The duplicate wheel in the previous file was the centered rounding data itself: it restated the
same inclusion pattern already owned by `IsBetaRounding`. This file now keeps the source-facing
names, but reuses the chapter owner directly and derives the centered view from it.
-/

/-- Definition 7.29: for a convex centrally symmetric body `C ⊆ ℝⁿ`, an ellipsoidal rounding of
radius `γ √n` is a positive-definite matrix `G` such that the unit centered ellipsoid `W₁(G)` is
contained in `C` and `C` is contained in `W_(γ √n)(G)`. -/
abbrev IsEllipsoidalRounding (C : Set E) (gamma : ℝ) (G : Mat) : Prop :=
  G.PosDef ∧ IsBetaRounding C (gamma * Real.sqrt (n : ℝ)) G (0 : E)

namespace IsEllipsoidalRounding

theorem posDef {C : Set E} {gamma : ℝ} {G : Mat}
    (h : IsEllipsoidalRounding C gamma G) :
    G.PosDef :=
  h.1

theorem toIsBetaRounding {C : Set E} {gamma : ℝ} {G : Mat}
    (h : IsEllipsoidalRounding C gamma G) :
    IsBetaRounding C (gamma * Real.sqrt (n : ℝ)) G (0 : E) :=
  h.2

theorem unit_ellipsoid_subset {C : Set E} {gamma : ℝ} {G : Mat}
    (h : IsEllipsoidalRounding C gamma G) :
    W[1](G) ⊆ C := by
  simpa using h.toIsBetaRounding.unit_matrixEllipsoid_subset

theorem subset_outer_ellipsoid {C : Set E} {gamma : ℝ} {G : Mat}
    (h : IsEllipsoidalRounding C gamma G) :
    C ⊆ W[(gamma * Real.sqrt (n : ℝ))](G) := by
  simpa using h.toIsBetaRounding.subset_beta_ellipsoid

end IsEllipsoidalRounding

/-- An ellipsoidal rounding records positive definiteness together with the inner and outer
centered-ellipsoid inclusions from the definition. -/
instance {C : Set E} {gamma : ℝ} {G : Mat}
    (h : IsEllipsoidalRounding C gamma G) :
    Fact (G.PosDef ∧ W[1](G) ⊆ C ∧ C ⊆ W[(gamma * Real.sqrt (n : ℝ))](G)) where
  out := ⟨h.posDef, h.unit_ellipsoid_subset, h.subset_outer_ellipsoid⟩

/-- An initial approximation is a positive-definite matrix whose unit centered ellipsoid lies in
`C` and for which `C` is contained in some centered ellipsoid `W_R(G0)` with `R ≥ 1`. -/
abbrev IsInitialApproximation (C : Set E) (G0 : Mat) : Prop :=
  G0.PosDef ∧ ∃ R : ℝ, 1 ≤ R ∧ IsBetaRounding C R G0 (0 : E)

namespace IsInitialApproximation

theorem posDef {C : Set E} {G0 : Mat} (h : IsInitialApproximation C G0) :
    G0.PosDef :=
  h.1

theorem exists_betaRounding {C : Set E} {G0 : Mat}
    (h : IsInitialApproximation C G0) :
    ∃ R : ℝ, 1 ≤ R ∧ IsBetaRounding C R G0 (0 : E) :=
  h.2

theorem unit_ellipsoid_subset {C : Set E} {G0 : Mat}
    (h : IsInitialApproximation C G0) :
    W[1](G0) ⊆ C := by
  rcases h.exists_betaRounding with ⟨R, hR, hrounding⟩
  simpa using hrounding.unit_matrixEllipsoid_subset

theorem exists_outer_radius {C : Set E} {G0 : Mat}
    (h : IsInitialApproximation C G0) :
    ∃ R : ℝ, 1 ≤ R ∧ C ⊆ W[R](G0) := by
  rcases h.exists_betaRounding with ⟨R, hR, hrounding⟩
  exact ⟨R, hR, by simpa using hrounding.subset_beta_ellipsoid⟩

end IsInitialApproximation

end

/-! ### Proposition_7_29 (from Chap07) -/
open scoped BigOperators

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-
Proposition 7.29 lies in the barrier-subgradient / weighted-average domain.

Mandatory domain-style sampling:
- `DualBarrierSubgradientMethod` in `Algorithm_7_12`, the source-facing owner of the iterates and
  stepsizes;
- `barrierSubgradientWeightSum` in `Theorem_7_15` and
  `barrierSubgradientAverageDualityGap_le_maximalGap` in `Lemma_7_12`, the chapter owners for
  `S_k` and the nearby averaged-gap estimate;
- `Finset.centerMass` and `ConcaveOn.le_map_centerMass`, the canonical finite weighted-average
  owner and Jensen inequality for concave functions;
- `maximalValueOn` and `barrierSubgradientMaximalGap`, the faithful `EReal` owners for the primal
  optimum `f_*` and the maximal gap `ℓ_k⋆`.

Best owner abstraction:
- source-facing: the weighted primal-value average generated by a `DualBarrierSubgradientMethod`;
- core/canonical: `Finset.centerMass` for that normalized average, together with
  `barrierSubgradientWeightSum`, `maximalValueOn`, and `barrierSubgradientMaximalGap`;
- bridge/view: the textbook quotient formula
  `(∑ λ_i f(x_i)) / (∑ λ_i)`, which is just the scalar expansion of `Finset.centerMass`.

Primitive data:
- the method owner `method : DualBarrierSubgradientMethod P f`;
- the index `k`.

Derived API:
- the scalar weighted average `centerMass` of the sampled values `f(method i)`;
- the normalization factor `barrierSubgradientWeightSum`;
- the explicit-rate specialization obtained by combining the main estimate with an assumed maximal
  gap bound.

The previous version duplicated both the denominator `S_k` and the normalized weighted average as
raw quotient expressions. This refinement keeps the proposition source-facing, but moves its public
surface to the existing weighted-average and gap owners already established earlier in the chapter.
-/

-- Proof sketch: for each feasible `y ∈ P`, concavity gives
-- `f y ≤ f(x_i) + ⟪g_i, y - x_i⟫` for every `i`. Multiply by the positive step sizes,
-- sum from `i = 0` to `k`, and then take the supremum over `y ∈ P` to identify the gap term
-- `barrierSubgradientMaximalGap ... k`.
/-- Proposition 7.29: for a concave objective on the feasible set of the barrier subgradient
method, the weighted average of the values `f(x_i)` over the first `k + 1` iterates, written
canonically as a `Finset.centerMass`, is within `ℓ_k⋆ / S_k` of the maximal value
`f_* = maximalValueOn P f`, where `ℓ_k⋆` is `barrierSubgradientMaximalGap ... k` and
`S_k = barrierSubgradientWeightSum ... k`. -/
theorem barrierSubgradientMethod_primal_efficiency_estimate
    {P : Set E} {f : E → ℝ}
    (method : DualBarrierSubgradientMethod P f) (k : ℕ) :
    maximalValueOn P f -
        (((Finset.range (k + 1)).centerMass
            (fun i ↦ (method.stepSize i : ℝ))
            (fun i ↦ f (method i)) : ℝ) : EReal) ≤
      method.maximalGap k /
        barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k :=
  sorry

-- Proof sketch: combine `barrierSubgradientMethod_primal_efficiency_estimate` with the explicit
-- bound assumed for `barrierSubgradientMaximalGap ... k / S_k`, where that bound is the one
-- obtained in the text from the parameter choice `(7.3.19)`.
/-- When the maximal-gap estimate produced by the parameter choice `(7.3.19)` holds, the weighted
average of the sampled values `f(x_i)` satisfies the corresponding explicit rate. -/
theorem barrierSubgradientMethod_primal_efficiency_estimate_explicit_rate
    {P : Set E} {f : E → ℝ}
    (method : DualBarrierSubgradientMethod P f) {M ν : ℝ}
    (hgap :
      ∀ k : ℕ,
        method.maximalGap k /
          barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k ≤
          ((2 * M *
              (Real.sqrt (ν / ((k : ℝ) + 1)) + ν / ((k : ℝ) + 1)) *
                (1 + Real.log (2 + (3 / 2 : ℝ) * Real.sqrt (ν * ((k : ℝ) + 1)))) : ℝ)))
    (k : ℕ) :
    maximalValueOn P f -
        (((Finset.range (k + 1)).centerMass
            (fun i ↦ (method.stepSize i : ℝ))
            (fun i ↦ f (method i)) : ℝ) : EReal) ≤
      ((2 * M *
          (Real.sqrt (ν / ((k : ℝ) + 1)) + ν / ((k : ℝ) + 1)) *
            (1 + Real.log (2 + (3 / 2 : ℝ) * Real.sqrt (ν * ((k : ℝ) + 1)))) : ℝ)) :=
  sorry
