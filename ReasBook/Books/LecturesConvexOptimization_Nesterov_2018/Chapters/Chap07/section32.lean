import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_32 (from Chap07) -/
noncomputable section

open scoped EllipsoidNotation

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- Definition 7.32 lies in the Chapter 7 translated ellipsoid-rounding domain.

Sampled owner-style declarations:
- `IsBetaRounding` in `Chap07/Definition_7_27`, the chapter owner of ellipsoid roundings with an
  arbitrary center and outer radius;
- `IsBetaRounding.unit_matrixEllipsoid_subset` in `Chap07/Definition_7_27`, the source-facing
  radius-`1` inclusion derived from that owner;
- `matrixEllipsoid` in `Chap07/Definition_7_26`, the source-facing variable-radius ellipsoid
  owner;
- `IsEllipsoidalRounding` in `Chap07/Definition_7_29`, the nearby centered specialization already
  refined to `IsBetaRounding`.

Best owner abstraction:
- source-facing: `IsGammaNRounding`, which adds convexity, `1 < γ`, and positive definiteness to
  the translated `γ n`-rounding setup;
- core/canonical: `IsBetaRounding`;
- bridge/view: the derived `v ∈ interior C`, `W[1](v, G) ⊆ C`, and `C ⊆ W[(γ * n)](v, G)`
  consequences.

Primitive data:
- a set `C : Set E`;
- a rounding parameter `γ : ℝ`;
- a matrix `G : Mat`;
- a center `v : E`;
- the core rounding datum `IsBetaRounding C (γ * n) G v`;
- convexity of `C`;
- the positivity assumptions `1 < γ` and `G.PosDef`.

Derived API:
- the inherited `IsBetaRounding` projections for the inner and outer ellipsoid containments;
- the derived interior facts `v ∈ interior C` and `(interior C).Nonempty`;
- the source-facing unit-radius inclusion derived from the inherited core owner.

Source/core/bridge triage:
- source-facing: `IsGammaNRounding`;
- core/canonical: `IsBetaRounding`;
- bridge/view: the namespace projection lemmas below.

The previous file duplicated the rounding data already owned by `IsBetaRounding` as primitive
fields. This refinement keeps the extra source-facing hypotheses from Definition 7.32, moves the
rounding core back to the chapter owner, and derives interiority from the inner positive-definite
ellipsoid instead of storing it as primitive data. The public owner is now a structure extending
`IsBetaRounding`, so the core containment data is inherited rather than repackaged through a
conjunction and a global `Fact` bundle.
-/

/-- Definition 7.32: a `γ n`-rounding of a convex set `C ⊆ ℝⁿ` with nonempty interior is a
center `v` and a positive-definite matrix `G` such that `γ > 1`, the unit ellipsoid `W₁(v,G)` is
contained in `C`, and `C` is contained in the outer ellipsoid `W_(γ n)(v,G)`. -/
structure IsGammaNRounding
    (C : Set E) (γ : ℝ) (G : Mat) (v : E) : Prop extends IsBetaRounding C (γ * n) G v where
  /-- The ambient set `C` is convex. -/
  convex : Convex ℝ C
  /-- The rounding parameter satisfies `γ > 1`. -/
  one_lt_gamma : 1 < γ
  /-- The rounding matrix is positive definite. -/
  posDef : G.PosDef

namespace IsGammaNRounding

theorem center_mem_interior {C : Set E} {γ : ℝ} {G : Mat} {v : E}
    (h : IsGammaNRounding C γ G v) :
    v ∈ interior C := by
  have hsubset : E(G, v) ⊆ C := h.toIsBetaRounding.unit_ellipsoid_subset
  exact interior_mono hsubset (center_mem_interior_affineEllipsoid G v h.posDef)

theorem interior_nonempty {C : Set E} {γ : ℝ} {G : Mat} {v : E}
    (h : IsGammaNRounding C γ G v) :
    (interior C).Nonempty :=
  ⟨v, h.center_mem_interior⟩

theorem unit_matrixEllipsoid_subset {C : Set E} {γ : ℝ} {G : Mat} {v : E}
    (h : IsGammaNRounding C γ G v) :
    W[1](v, G) ⊆ C := by
  exact h.toIsBetaRounding.unit_matrixEllipsoid_subset

theorem subset_outer_ellipsoid {C : Set E} {γ : ℝ} {G : Mat} {v : E}
    (h : IsGammaNRounding C γ G v) :
    C ⊆ W[(γ * n)](v, G) := by
  exact h.toIsBetaRounding.subset_beta_ellipsoid

end IsGammaNRounding

/-- A `γ n`-rounding canonically supplies the underlying `β`-rounding with
`β = γ n`. -/
instance {C : Set E} {γ : ℝ} {G : Mat} {v : E}
    (h : IsGammaNRounding C γ G v) :
    Fact (IsBetaRounding C (γ * n) G v) where
  out := h.toIsBetaRounding

end

/-! ### Proposition_7_32 (from Chap07) -/
open scoped BigOperators
open EuclideanSpace (nonnegativeOrthant)

noncomputable section

universe u

variable {m : ℕ} {OD : Type u} [Fintype OD]

local notation "E" => EuclideanSpace ℝ (Fin m)

/- Proposition 7.32 lies in the Chapter 7 fractional-covering / concurrent-flow duality domain.

Sampled owner-style declarations:
- `fractionalCoveringPhiStar` in `Proposition_7_31`, the source-facing owner of the infimum
  `φ⋆ = inf ⟪b, t⟫ / ψ(t)` on the nonnegative orthant;
- `fractionalCoveringNormalizedPsiSup` in `Proposition_7_31`, the source-facing owner of the
  normalized supremum of `ψ`;
- `fractionalCoveringPhiStar_eq_inv_normalizedPsiSup` in `Proposition_7_31`, the Chapter 7 owner
  theorem that already proves the reciprocal relation used here;
- `IsPositivelyHomogeneousOn` in `Chap03/Definition_3_1_7`, the project owner of positive
  homogeneity on a cone.

Best owner abstraction:
- source-facing: the maximal concurrent-flow dual specialization of Proposition 7.31;
- core/canonical: `fractionalCoveringPhiStar`, `fractionalCoveringNormalizedPsiSup`, and
  `fractionalCoveringPhiStar_eq_inv_normalizedPsiSup`;
- bridge/view: the finite weighted-sum objective `t ↦ ∑ od, d od * shortestPath od t`.

Primitive data:
- the capacity vector `barf`;
- the demand family `d`;
- the shortest-path family `shortestPath`.

Derived API:
- the dual objective written directly as the finite sum over `OD`;
- the reciprocal-value identity below, obtained by specializing the owner theorem.

This refinement deletes the duplicate local wrapper
`maximalConcurrentFlowDualObjective`. That definition was an exact one-file alias for the finite
sum objective and had no downstream users, so the public surface is cleaner if Proposition 7.32
specializes the Chapter 7 owner theorem directly to the canonical function expression.
-/

-- Proof sketch: specialize Proposition 7.31 to the objective
-- `ψ(t) = ∑ od, d od * shortestPath od t`. The stated positivity and
-- positive-homogeneity hypotheses are exactly the assumptions needed for the normalization
-- argument that identifies the dual value with the reciprocal of the normalized supremum.
/-- Proposition 7.32: for the maximal concurrent flow problem with capacity vector `barf`,
demands `d_{i,j}`, and shortest-path costs `SP_{i,j}(t)`, specializing Proposition 7.31 to the
dual objective `ψ(t) = ∑_{(i,j) ∈ 𝒪𝒟} d_{i,j} SP_{i,j}(t)` identifies the dual value `λ⋆` with
the reciprocal of the supremum of `ψ` on the normalized nonnegative slice `⟪barf, t⟫ = 1`,
which is the textbook formula `ψ⋆ = λ⋆⁻¹`. -/
theorem maximalConcurrentFlow_dualValue_eq_inv_normalizedDualObjectiveSup
    (barf : E) (d : OD → ℝ) (shortestPath : OD → E → ℝ)
    (hbarf_pos_on_orthant :
      ∀ t : E, t ∈ nonnegativeOrthant m → t ≠ 0 → 0 < inner ℝ barf t)
    (hobjective_pos :
      ∀ t : E, t ∈ nonnegativeOrthant m → t ≠ 0 →
        0 < ∑ od, d od * shortestPath od t)
    (hobjective_hom :
      IsPositivelyHomogeneousOn 1 (nonnegativeOrthant m)
        (fun t ↦ ∑ od, d od * shortestPath od t)) :
    fractionalCoveringPhiStar barf (fun t ↦ ∑ od, d od * shortestPath od t) =
      (fractionalCoveringNormalizedPsiSup
        barf (fun t ↦ ∑ od, d od * shortestPath od t))⁻¹ := by
  simpa using fractionalCoveringPhiStar_eq_inv_normalizedPsiSup
    barf
    (fun t ↦ ∑ od, d od * shortestPath od t)
    hbarf_pos_on_orthant
    hobjective_pos
    hobjective_hom
