import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_49 (from Chap03) -/
noncomputable section

universe u

section Ambient

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Definition 3.49 lies in the convex-feasibility separation-oracle domain.

Sampled owner-style declarations:
- `SeparatesPointFromWith` in `Definition_3_1_4_1`, the chapter owner for a nonzero affine
  separator between a point and a set;
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner of an
  ambient feasible set together with a real-valued objective;
- `ConvexMinimizationWithSeparationOracle` in `Definition_3_51`, the later source-facing owner for
  constrained convex minimization with a stricter infeasible-query oracle.

Best owner abstraction:
- source-facing owner: `FeasibilityProblemWithSeparationOracle E`;
- core separating witness for an infeasible query: `SeparatesPointFromWith S xBar g ⟪g, xBar⟫`;
- derived callable owner view: `SeparationOracle S`.

Primitive data:
- the feasible set `S`;
- its nonempty / closed / convex witnesses;
- the oracle reply map.

Derived API:
- the retained half-space cut `cuttingHalfspace xBar g` attached to a separating reply;
- the bridge between that cut and the upstream point/set separation owner;
- its canonical nonzero-vector bridge to `AffineHyperplane.closedLowerHalfspace`;
- its closedness and convexity lemmas;
- no extra callable wrapper, since `SeparationOracle S` is already the direct query-to-answer map.

Because Definition 3.49 is objective-free, `SetConstrainedMinimizationProblem` is only a possible
bridge/view downstream, not the public owner here. -/

/-- The retained half-space cut determined by a query point `xBar` and vector `g`,
equivalently `{x | 0 ≤ ⟪g, xBar - x⟫}`. -/
def cuttingHalfspace (xBar g : E) : Set E :=
  {x | inner ℝ g x ≤ inner ℝ g xBar}

/-- Membership in the retained cut is exactly the textbook inequality
`0 ≤ ⟪g, xBar - x⟫`. -/
@[simp] theorem mem_cuttingHalfspace_iff {xBar g x : E} :
    x ∈ cuttingHalfspace xBar g ↔ 0 ≤ inner ℝ g (xBar - x) := by
  simp [cuttingHalfspace, inner_sub_right, sub_nonneg]

/-- For a nonzero cutting vector, the retained cut is exactly the closed lower half-space of the
earlier affine-hyperplane owner with offset `⟪g, xBar⟫`. -/
theorem cuttingHalfspace_eq_closedLowerHalfspace {xBar g : E} (hg : g ≠ 0) :
    cuttingHalfspace xBar g =
      (⟨g, hg, inner ℝ g xBar⟩ : AffineHyperplane E).closedLowerHalfspace :=
  rfl

/-- The retained cut is closed. -/
theorem cuttingHalfspace_closed (xBar g : E) :
    IsClosed (cuttingHalfspace xBar g) := by
  simpa [cuttingHalfspace] using
    (isClosed_le (continuous_const.inner continuous_id) continuous_const)

/-- The retained cut is convex. -/
theorem cuttingHalfspace_convex (xBar g : E) :
    Convex ℝ (cuttingHalfspace xBar g) := by
  simpa [cuttingHalfspace, innerₗ_apply_apply] using
    (convex_halfSpace_le (LinearMap.isLinear (innerₗ E g)) (inner ℝ g xBar))

/-- The retained-cut formulation `S ⊆ cuttingHalfspace xBar g` is exactly the upstream
point-versus-set separation owner specialized to the canonical offset `⟪g, xBar⟫`. -/
theorem separatesPointFromWith_inner_iff {S : Set E} {xBar g : E} :
    SeparatesPointFromWith S xBar g (inner ℝ g xBar) ↔
      g ≠ 0 ∧ S ⊆ cuttingHalfspace xBar g := by
  constructor
  · intro hsep
    refine ⟨hsep.ne_zero, ?_⟩
    intro x hx
    simpa [cuttingHalfspace] using hsep.le_offset hx
  · rintro ⟨hg, hcut⟩
    refine ⟨hg, ?_⟩
    constructor
    · simpa [cuttingHalfspace] using hcut
    · simp [AffineHyperplane.closedUpperHalfspace]

/-- A separation-oracle answer at `xBar` either certifies feasibility or, on an infeasible query,
returns a genuine separating vector in the chapter's canonical point/set separation sense. -/
inductive SeparationOracleAnswer (S : Set E) (xBar : E) where
  /-- The oracle certifies that the query point already lies in the feasible set. -/
  | feasible : xBar ∈ S → SeparationOracleAnswer S xBar
  /-- The oracle returns a vector `g` witnessing that the infeasible query point `xBar` is
  separated from `S` by the retained cut `⟪g, x⟫ ≤ ⟪g, xBar⟫`. -/
  | separatingVector :
      (g : E) →
      xBar ∉ S →
      SeparatesPointFromWith S xBar g (inner ℝ g xBar) →
      SeparationOracleAnswer S xBar

namespace SeparationOracleAnswer

/-- The observable part of a separation-oracle answer: `none` means the oracle certified the
query point feasible, while `some g` records the separating vector returned on an infeasible
query. -/
def oracleReply {S : Set E} {xBar : E} (answer : SeparationOracleAnswer S xBar) : Option E :=
  match answer with
  | .feasible _ => none
  | .separatingVector g _ _ => some g

@[simp] theorem oracleReply_feasible {S : Set E} {xBar : E} (hxBar : xBar ∈ S) :
    (SeparationOracleAnswer.feasible hxBar).oracleReply = (none : Option E) :=
  rfl

@[simp] theorem oracleReply_separatingVector {S : Set E} {xBar g : E}
    (hxBar : xBar ∉ S)
    (hsep : SeparatesPointFromWith S xBar g (inner ℝ g xBar)) :
    (SeparationOracleAnswer.separatingVector g hxBar hsep).oracleReply = some g :=
  rfl

/-- A separating answer cuts away the infeasible query point while keeping the feasible set in
the retained half-space. -/
theorem separatingVector_subset_cuttingHalfspace {S : Set E} {xBar g : E}
    (hsep : SeparatesPointFromWith S xBar g (inner ℝ g xBar)) :
    S ⊆ cuttingHalfspace xBar g :=
  (separatesPointFromWith_inner_iff.mp hsep).2

end SeparationOracleAnswer

/-- A separation oracle for `S` answers each query point by either certifying membership in `S`
or producing a separating vector. -/
abbrev SeparationOracle (S : Set E) : Type u :=
  ∀ xBar : E, SeparationOracleAnswer S xBar

end Ambient

section Ambient

variable (E : Type u) [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Definition 3.49: a feasibility problem with separation oracle consists of a nonempty closed
convex set `S` in a real inner-product space together with a separation oracle that, for every
query point `xBar`, either certifies `xBar ∈ S` or, when `xBar ∉ S`, returns a nonzero vector
`g` that separates `xBar` from `S` by the retained-cut inequality `⟪g, xBar - x⟫ ≥ 0` for all
`x ∈ S`. Specializing `E = EuclideanSpace ℝ (Fin n)` recovers the textbook `ℝⁿ` formulation.
Solving the feasibility problem means producing a point of `S`. -/
structure FeasibilityProblemWithSeparationOracle where
  /-- The feasible set `S` in the ambient space. -/
  feasibleSet : Set E
  /-- The feasible set is nonempty. -/
  feasibleSet_nonempty : feasibleSet.Nonempty
  /-- The feasible set is closed. -/
  feasibleSet_closed : IsClosed feasibleSet
  /-- The feasible set is convex. -/
  feasibleSet_convex : Convex ℝ feasibleSet
  /-- A separation oracle for the feasible set. -/
  oracle : SeparationOracle feasibleSet

namespace FeasibilityProblemWithSeparationOracle

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The underlying Chapter 1 constrained-problem owner with the same feasible set and the
constant-zero objective. This is only a bridge/view: the source-facing owner remains the
feasibility problem together with its separation oracle. -/
def toSetConstrainedMinimizationProblem
    (problem : FeasibilityProblemWithSeparationOracle E) :
    SetConstrainedMinimizationProblem E where
  feasibleSet := problem.feasibleSet
  objective := fun _ ↦ 0

/-- A feasibility problem with separation oracle coerces to its feasible set. -/
instance : Coe (FeasibilityProblemWithSeparationOracle E) (Set E) where
  coe problem := problem.feasibleSet

/-- A feasibility problem with separation oracle can be used as the membership predicate of its
feasible set. -/
instance : Membership E (FeasibilityProblemWithSeparationOracle E) where
  mem problem x := x ∈ problem.feasibleSet

/-- Membership in the coerced feasible set of a feasibility problem is exactly feasibility in its
stored set `S`. -/
@[simp] theorem mem_coe
    {problem : FeasibilityProblemWithSeparationOracle E}
    {x : E} :
    x ∈ (problem : Set E) ↔ x ∈ problem.feasibleSet :=
  Iff.rfl

/-- Membership in a feasibility problem is exactly membership in its feasible set `S`. -/
@[simp] theorem mem_iff
    {problem : FeasibilityProblemWithSeparationOracle E}
    {x : E} :
    x ∈ problem ↔ x ∈ problem.feasibleSet :=
  by rfl

/-- The bridge to the generic constrained-problem owner keeps the original feasible set. -/
@[simp] theorem toSetConstrainedMinimizationProblem_feasibleSet
    (problem : FeasibilityProblemWithSeparationOracle E) :
    problem.toSetConstrainedMinimizationProblem.feasibleSet = problem.feasibleSet :=
  rfl

/-- Evaluating the bridged constrained problem returns the constant zero objective. -/
@[simp] theorem toSetConstrainedMinimizationProblem_apply
    (problem : FeasibilityProblemWithSeparationOracle E)
    (x : E) :
    problem.toSetConstrainedMinimizationProblem x = 0 :=
  rfl

/-- Feasibility in the bridged constrained problem is exactly feasibility in the original
problem. -/
@[simp] theorem mem_toSetConstrainedMinimizationProblem_feasibleSet_iff
    {problem : FeasibilityProblemWithSeparationOracle E}
    {x : E} :
    x ∈ problem.toSetConstrainedMinimizationProblem.feasibleSet ↔ x ∈ problem.feasibleSet :=
  Iff.rfl

end FeasibilityProblemWithSeparationOracle

end Ambient

/-! ### Proposition_3_49 (from Chap03) -/
open MeasureTheory
open scoped MeasureTheory RealInnerProductSpace

noncomputable section

universe u

section Ambient

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-
Proposition 3.49 is the spherical-cap estimate used in the Kelley complete-data example from
Section 3.3.2: if successive Kelley cuts keep intersecting the unit sphere, then the remaining
surface measure shrinks by the cap ratio `v(α) / v(0)`.

Mandatory domain-style sampling before refinement:
- `Metric.sphere`, the canonical owner of the unit sphere as a subset of the ambient space;
- `mem_sphere_zero_iff_norm`, the canonical bridge from sphere membership to the norm equation;
- `Isometry.euclideanHausdorffMeasure_image`, the canonical invariance of Euclidean Hausdorff
  measure under isometries;
- `Measure.euclideanHausdorffMeasure_smul₀`, the canonical scaling rule for Euclidean Hausdorff
  measure.

Best owner abstraction:
- source-facing: the spherical cap cut from the unit sphere by the inequality `α ≤ ⟪d, x⟫`,
  exactly the cap appearing in the Kelley-cut counting argument;
- core/canonical: `Metric.sphere` together with the ambient inner product and Euclidean
  Hausdorff surface measure `μHE[Module.finrank ℝ E - 1]`;
- bridge/view: `mem_sphere_zero_iff_norm` for pointwise membership, together with
  `Measure.euclideanHausdorffMeasure_def` as the bridge back to the scaled raw Hausdorff
  measure `μH[...]`.

Primitive data:
- a direction vector `d : E`;
- a threshold `α : ℝ`;
- the unit sphere `Metric.sphere (0 : E) 1`.

Derived API:
- membership expansion for the cap;
- the finite-dimensional Euclidean surface-measure comparison with the hemisphere case, which is
  the geometric input for the Kelley lower-bound construction.

The project does not already own a spherical-cap declaration upstream, so this file keeps
`sphericalCap` as the source-facing set owner. The source excerpt is stated in `ℝⁿ`, but the
mathematics only uses the finite-dimensional real inner-product-space structure, so the file
stays at that intrinsic owner level and recovers the textbook display model by specialization.
-/

/-- The spherical cap on the unit sphere cut out by the inequality `α ≤ ⟪d, x⟫`. -/
def sphericalCap (d : E) (α : ℝ) : Set E :=
  Metric.sphere (0 : E) 1 ∩ {x | α ≤ ⟪d, x⟫}

/-- Membership in `sphericalCap d α` means lying on the canonical unit-sphere owner and satisfying
the cap inequality. -/
@[simp] theorem mem_sphericalCap_iff {d x : E} {α : ℝ} :
    x ∈ sphericalCap d α ↔ x ∈ Metric.sphere (0 : E) 1 ∧ α ≤ ⟪d, x⟫ := by
  simp [sphericalCap]

/-- Rewriting `mem_sphericalCap_iff` through `mem_sphere_zero_iff_norm` recovers the textbook
norm-one characterization of spherical-cap membership. -/
theorem mem_sphericalCap_iff_norm {d x : E} {α : ℝ} :
    x ∈ sphericalCap d α ↔ ‖x‖ = 1 ∧ α ≤ ⟪d, x⟫ := by
  rw [mem_sphericalCap_iff, mem_sphere_zero_iff_norm]

end Ambient

section FiniteDimensional

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

local notation "sphereRank" => Module.finrank ℝ E - 1
local notation "sphereDim" => ((sphereRank : ℕ) : ℝ)

/-- Helper for Proposition 3.49: the contraction factor written as a square root. -/
private def sphericalCapScale (α : ℝ) : ℝ :=
  Real.sqrt (1 - α ^ 2)

/-- Helper for Proposition 3.49: the scalar profile on the distinguished `d`-axis is the Euclidean
norm of the pair `(α, sphericalCapScale α * t)`, so it varies with Lipschitz constant
`‖sphericalCapScale α‖`. -/
private lemma sqrt_alpha_sq_add_mul_sq_lipschitz {α : ℝ} (hα_left : 0 ≤ α) (hα_right : α ≤ 1) :
    LipschitzWith (Real.toNNReal (sphericalCapScale α))
      (fun t : ℝ ↦ Real.sqrt (α ^ 2 + (1 - α ^ 2) * t ^ 2)) := by
  -- The scalar profile is the `L²`-norm of the pair `(α, sphericalCapScale α * t)`.
  have h_scale_nonneg : 0 ≤ sphericalCapScale α := Real.sqrt_nonneg _
  have h_scale_sq : sphericalCapScale α ^ 2 = 1 - α ^ 2 := by
    rw [sphericalCapScale, Real.sq_sqrt]
    nlinarith [sq_nonneg α, hα_left, hα_right]
  have h_pair_norm :
      ∀ t : ℝ,
        ‖WithLp.toLp 2 ((α, sphericalCapScale α * t) : ℝ × ℝ)‖ =
          Real.sqrt (α ^ 2 + (1 - α ^ 2) * t ^ 2) := by
    intro t
    have h_arg_nonneg : 0 ≤ α ^ 2 + (1 - α ^ 2) * t ^ 2 := by
      rw [← h_scale_sq]
      positivity
    refine sq_eq_sq₀ ?_ (Real.sqrt_nonneg _) |>.mp ?_
    · positivity
    · rw [sq, Real.sq_sqrt]
      ·
        have h_abs_sq :
            |sphericalCapScale α| * |t| * (|sphericalCapScale α| * |t|) =
              (1 - α * α) * (t * t) := by
          rw [abs_of_nonneg h_scale_nonneg]
          nlinarith [sq_abs t, h_scale_sq]
        have h_sq :=
          WithLp.prod_norm_sq_eq_of_L2
            (WithLp.toLp 2 ((α, sphericalCapScale α * t) : ℝ × ℝ))
        simpa [sq, h_abs_sq] using h_sq
      · exact h_arg_nonneg
  have h_axis_norm :
      ∀ t : ℝ, ‖WithLp.toLp 2 ((0, sphericalCapScale α * t) : ℝ × ℝ)‖ = sphericalCapScale α * |t| := by
    intro t
    refine sq_eq_sq₀ ?_ (by positivity) |>.mp ?_
    · positivity
    ·
      have h_abs_sq :
          |sphericalCapScale α| * |t| * (|sphericalCapScale α| * |t|) =
            (sphericalCapScale α * |t|) ^ 2 := by
        rw [abs_of_nonneg h_scale_nonneg]
        ring
      have h_sq :=
        WithLp.prod_norm_sq_eq_of_L2
          (WithLp.toLp 2 ((0, sphericalCapScale α * t) : ℝ × ℝ))
      simpa [sq, h_abs_sq] using h_sq
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  rw [Real.dist_eq]
  calc
    |Real.sqrt (α ^ 2 + (1 - α ^ 2) * x ^ 2) - Real.sqrt (α ^ 2 + (1 - α ^ 2) * y ^ 2)| =
        |‖WithLp.toLp 2 ((α, sphericalCapScale α * x) : ℝ × ℝ)‖ -
          ‖WithLp.toLp 2 ((α, sphericalCapScale α * y) : ℝ × ℝ)‖| := by
          rw [h_pair_norm x, h_pair_norm y]
    _ ≤ ‖WithLp.toLp 2 ((α, sphericalCapScale α * x) : ℝ × ℝ) -
          WithLp.toLp 2 ((α, sphericalCapScale α * y) : ℝ × ℝ)‖ :=
        abs_norm_sub_norm_le _ _
    _ = ‖WithLp.toLp 2 ((0, sphericalCapScale α * (x - y)) : ℝ × ℝ)‖ := by
        have h_pair :
            (((α, sphericalCapScale α * x) : ℝ × ℝ) -
                ((α, sphericalCapScale α * y) : ℝ × ℝ)) =
              (0, sphericalCapScale α * (x - y)) := by
          refine Prod.ext ?_ ?_
          · simp
          · simp [sub_eq_add_neg]
            ring
        have h_toLp :
            WithLp.toLp 2 ((α, sphericalCapScale α * x) : ℝ × ℝ) -
                WithLp.toLp 2 ((α, sphericalCapScale α * y) : ℝ × ℝ) =
              WithLp.toLp 2
                ((((α, sphericalCapScale α * x) : ℝ × ℝ) -
                  ((α, sphericalCapScale α * y) : ℝ × ℝ))) := by
          rfl
        rw [h_toLp, h_pair]
    _ = sphericalCapScale α * dist x y := by
        rw [h_axis_norm (x - y), Real.dist_eq]
    _ = ↑(Real.toNNReal (sphericalCapScale α)) * dist x y := by
        simpa [Real.toNNReal_of_nonneg h_scale_nonneg]

/-- Helper for Proposition 3.49: the singleton direction `d` and its orthogonal complement split
the norm square of every vector. -/
private lemma inner_sq_add_norm_sq_orthogonalComplement_starProjection
    {d x : E} (hd : ‖d‖ = 1) :
    ⟪d, x⟫ ^ 2 + ‖((ℝ ∙ d)ᗮ).starProjection x‖ ^ 2 = ‖x‖ ^ 2 := by
  -- The span of a unit vector and its orthogonal complement give the textbook `t^2 + ‖y‖^2`
  -- decomposition.
  have hsplit := Submodule.norm_sq_eq_add_norm_sq_starProjection x (ℝ ∙ d)
  have hproj : ‖(ℝ ∙ d).starProjection x‖ ^ 2 = ⟪d, x⟫ ^ 2 := by
    rw [Submodule.starProjection_unit_singleton ℝ hd x, norm_smul, hd, mul_one, Real.norm_eq_abs,
      sq_abs]
  rw [hproj] at hsplit
  linarith

/-- Helper for Proposition 3.49: the hemisphere-to-cap contraction rescales the orthogonal
component by `√(1 - α^2)` and then reconstructs the `d`-component on the sphere. -/
private def sphericalCapContract (d : E) (α : ℝ) : E → E :=
  fun x ↦
    sphericalCapScale α • ((ℝ ∙ d)ᗮ).starProjection x +
      Real.sqrt (α ^ 2 + (1 - α ^ 2) * ⟪d, x⟫ ^ 2) • d

/-- Helper for Proposition 3.49: the contraction is globally `√(1 - α^2)`-Lipschitz because it
acts orthogonally on the `d` and `dᗮ` coordinates. -/
private lemma sphericalCapContract_lipschitz {d : E} (hd : ‖d‖ = 1) {α : ℝ}
    (hα_left : 0 ≤ α) (hα_right : α ≤ 1) :
    LipschitzWith (Real.toNNReal (sphericalCapScale α)) (sphericalCapContract d α) := by
  -- Route correction: the stable estimate comes from splitting the map into orthogonal
  -- `dᮮ` and `d` components, not from a direct triangle-inequality bound.
  let A : E → E := fun z ↦ sphericalCapScale α • ((ℝ ∙ d)ᗮ).starProjection z
  let B : E → E := fun z ↦ Real.sqrt (α ^ 2 + (1 - α ^ 2) * ⟪d, z⟫ ^ 2) • d
  have hg := sqrt_alpha_sq_add_mul_sq_lipschitz hα_left hα_right
  have h_scale_nonneg : 0 ≤ sphericalCapScale α := Real.sqrt_nonneg _
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  have h_diff :
      sphericalCapContract d α x - sphericalCapContract d α y = (A x - A y) + (B x - B y) := by
    -- Rewriting the difference into the two orthogonal coordinate directions isolates the
    -- contraction estimate.
    simp [A, B, sphericalCapContract, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hA_mem : A x - A y ∈ (ℝ ∙ d)ᗮ := by
    refine Submodule.sub_mem _ ?_ ?_
    · exact Submodule.smul_mem _ _ (Submodule.starProjection_apply_mem _ _)
    · exact Submodule.smul_mem _ _ (Submodule.starProjection_apply_mem _ _)
  have hB_mem : B x - B y ∈ ℝ ∙ d := by
    refine Submodule.sub_mem _ ?_ ?_
    · exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self d)
    · exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self d)
  have h_inner' : ⟪B x - B y, A x - A y⟫ = 0 := hA_mem _ hB_mem
  have h_inner : ⟪A x - A y, B x - B y⟫ = 0 := by
    rwa [inner_eq_zero_symm] at h_inner'
  have h_sq :
      ‖(A x - A y) + (B x - B y)‖ ^ 2 = ‖A x - A y‖ ^ 2 + ‖B x - B y‖ ^ 2 := by
    -- Orthogonality lets the output norm square split exactly into the two coordinate squares.
    simpa [sq] using
      (norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (A x - A y) (B x - B y) h_inner)
  have hA_sub : A x - A y = sphericalCapScale α • ((ℝ ∙ d)ᗮ).starProjection (x - y) := by
    calc
      A x - A y = sphericalCapScale α •
          (((ℝ ∙ d)ᗮ).starProjection x - ((ℝ ∙ d)ᗮ).starProjection y) := by
            simp [A, smul_sub]
      _ = sphericalCapScale α • ((ℝ ∙ d)ᗮ).starProjection (x - y) := by
        rw [((((ℝ ∙ d)ᗮ).starProjection.map_sub x y).symm)]
  have hA_sq :
      ‖A x - A y‖ ^ 2 = sphericalCapScale α ^ 2 * ‖((ℝ ∙ d)ᗮ).starProjection (x - y)‖ ^ 2 := by
    rw [hA_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg h_scale_nonneg]
    ring
  have hB_eq :
      B x - B y =
        (Real.sqrt (α ^ 2 + (1 - α ^ 2) * ⟪d, x⟫ ^ 2) -
          Real.sqrt (α ^ 2 + (1 - α ^ 2) * ⟪d, y⟫ ^ 2)) • d := by
    -- The `d`-component is a scalar difference times the fixed unit vector `d`.
    simp [B]
    rw [← sub_smul]
  have hB_norm_le : ‖B x - B y‖ ≤ sphericalCapScale α * |⟪d, x - y⟫| := by
    have h_dist := hg.dist_le_mul ⟪d, x⟫ ⟪d, y⟫
    have h_inner_sub : ⟪d, x⟫ - ⟪d, y⟫ = ⟪d, x - y⟫ := by
      rw [inner_sub_right]
    rw [hB_eq, norm_smul, hd, mul_one, Real.norm_eq_abs]
    rw [Real.dist_eq] at h_dist
    exact le_trans h_dist (by simpa [h_inner_sub, Real.dist_eq, abs_mul, h_scale_nonneg])
  have hB_sq_le : ‖B x - B y‖ ^ 2 ≤ sphericalCapScale α ^ 2 * ⟪d, x - y⟫ ^ 2 := by
    calc
      ‖B x - B y‖ ^ 2 ≤ (sphericalCapScale α * |⟪d, x - y⟫|) ^ 2 := by
        gcongr
      _ = sphericalCapScale α ^ 2 * ⟪d, x - y⟫ ^ 2 := by
        nlinarith [sq_abs ⟪d, x - y⟫]
  have hsum_sq : ‖(A x - A y) + (B x - B y)‖ ^ 2 ≤ sphericalCapScale α ^ 2 * ‖x - y‖ ^ 2 := by
    rw [h_sq, hA_sq]
    have hsplit_xy :=
      inner_sq_add_norm_sq_orthogonalComplement_starProjection (d := d) (x := x - y) hd
    nlinarith [hB_sq_le, hsplit_xy]
  have h_final_sq :
      ‖sphericalCapContract d α x - sphericalCapContract d α y‖ ^ 2 ≤
        (sphericalCapScale α * ‖x - y‖) ^ 2 := by
    rw [h_diff]
    have h_rhs_sq : sphericalCapScale α ^ 2 * ‖x - y‖ ^ 2 =
        (sphericalCapScale α * ‖x - y‖) ^ 2 := by
      ring
    rwa [h_rhs_sq] at hsum_sq
  have h_final :
      ‖sphericalCapContract d α x - sphericalCapContract d α y‖ ≤
        sphericalCapScale α * ‖x - y‖ := by
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp h_final_sq
  simpa [Real.toNNReal_of_nonneg h_scale_nonneg] using h_final

/-- Helper for Proposition 3.49: the unit cap at level `1` contains only the distinguished
direction. -/
private lemma eq_direction_of_mem_sphericalCap_one {d z : E} (hd : ‖d‖ = 1)
    (hz : z ∈ sphericalCap d 1) : z = d := by
  rcases (mem_sphericalCap_iff_norm.mp hz) with ⟨hz_norm, hz_inner⟩
  have h_inner_le : ⟪d, z⟫ ≤ 1 := by
    calc
      ⟪d, z⟫ ≤ ‖d‖ * ‖z‖ := real_inner_le_norm _ _
      _ = 1 := by rw [hd, hz_norm, one_mul]
  have h_inner_eq : ⟪d, z⟫ = 1 := le_antisymm h_inner_le hz_inner
  have hsplit :=
    inner_sq_add_norm_sq_orthogonalComplement_starProjection (d := d) (x := z) hd
  have horth_norm_zero : ‖((ℝ ∙ d)ᗮ).starProjection z‖ = 0 := by
    -- The cap inequality at level `1` forces the orthogonal component to vanish.
    nlinarith [hsplit, hz_norm, h_inner_eq]
  have horth_zero : ((ℝ ∙ d)ᗮ).starProjection z = 0 := by
    exact norm_eq_zero.mp horth_norm_zero
  -- Reconstructing `z` from its span and orthogonal parts shows that only `d` remains.
  calc
    z = (ℝ ∙ d).starProjection z + ((ℝ ∙ d)ᗮ).starProjection z := by
      simpa using (Submodule.starProjection_add_starProjection_orthogonal (K := ℝ ∙ d) z).symm
    _ = (⟪d, z⟫ : ℝ) • d + 0 := by
      rw [Submodule.starProjection_unit_singleton ℝ hd z, horth_zero]
    _ = d := by simp [h_inner_eq]

/-- Helper for Proposition 3.49: the orthogonal component of a point in the cap has squared norm at
most the cap radius squared. -/
private lemma norm_sq_orthogonalComplement_starProjection_le_cap_radius_sq {d z : E}
    (hd : ‖d‖ = 1) {α : ℝ} (hα_left : 0 ≤ α) (hz : z ∈ sphericalCap d α) :
    ‖((ℝ ∙ d)ᗮ).starProjection z‖ ^ 2 ≤ 1 - α ^ 2 := by
  rcases (mem_sphericalCap_iff_norm.mp hz) with ⟨hz_norm, hz_inner⟩
  have h_inner_nonneg : 0 ≤ ⟪d, z⟫ := le_trans hα_left hz_inner
  have hsplit :=
    inner_sq_add_norm_sq_orthogonalComplement_starProjection (d := d) (x := z) hd
  -- This is the intrinsic version of the textbook estimate `‖y‖² ≤ 1 - α²`.
  nlinarith [hsplit, hz_norm, hz_inner, h_inner_nonneg]

/-- Helper for Proposition 3.49: the strict-branch inverse candidate is the rescaled orthogonal
projection plus the positive `d`-axis coordinate needed to return to the unit sphere. -/
private def sphericalCapContractPreimageCandidate (d z : E) (α : ℝ) : E :=
  let c := sphericalCapScale α
  let u := ((ℝ ∙ d)ᗮ).starProjection z
  c⁻¹ • u + Real.sqrt (1 - ‖c⁻¹ • u‖ ^ 2) • d

/-- Helper for Proposition 3.49: the explicit strict-branch candidate lies in the hemisphere. -/
private lemma candidate_preimage_mem_sphericalCap_zero {d z : E} (hd : ‖d‖ = 1) {α : ℝ}
    (hα_left : 0 ≤ α) (hα_right : α < 1) (hz : z ∈ sphericalCap d α) :
    sphericalCapContractPreimageCandidate d z α ∈ sphericalCap d 0 := by
  set c : ℝ := sphericalCapScale α with hc
  set u : E := ((ℝ ∙ d)ᗮ).starProjection z with hu
  set s : ℝ := Real.sqrt (1 - ‖c⁻¹ • u‖ ^ 2) with hs
  have hc_sq_pos : 0 < 1 - α ^ 2 := by
    nlinarith [sq_nonneg α, hα_left, hα_right]
  have hc_pos : 0 < c := by
    rw [hc, sphericalCapScale]
    exact Real.sqrt_pos.mpr hc_sq_pos
  have hc_sq : c ^ 2 = 1 - α ^ 2 := by
    rw [hc, sphericalCapScale, Real.sq_sqrt]
    nlinarith [sq_nonneg α, hα_left, hα_right.le]
  have hu_mem : u ∈ (ℝ ∙ d)ᗮ := by
    rw [hu]
    exact Submodule.starProjection_apply_mem _ _
  have hu_sq_le : ‖u‖ ^ 2 ≤ c ^ 2 := by
    simpa [hu, hc_sq] using
      norm_sq_orthogonalComplement_starProjection_le_cap_radius_sq
        (d := d) (z := z) hd hα_left hz
  have hu_le_c : ‖u‖ ≤ c := by
    exact (sq_le_sq₀ (norm_nonneg _) (le_of_lt hc_pos)).mp hu_sq_le
  have hscaled_norm_le : ‖c⁻¹ • u‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc_pos)]
    have hmul := mul_le_mul_of_nonneg_left hu_le_c (inv_nonneg.mpr hc_pos.le)
    simpa [inv_mul_cancel₀ hc_pos.ne'] using hmul
  have hscaled_sq_le : ‖c⁻¹ • u‖ ^ 2 ≤ 1 := by
    nlinarith [hscaled_norm_le, norm_nonneg (c⁻¹ • u)]
  have hs_sq : s ^ 2 = 1 - ‖c⁻¹ • u‖ ^ 2 := by
    rw [hs, Real.sq_sqrt]
    linarith
  have hscaled_mem : c⁻¹ • u ∈ (ℝ ∙ d)ᗮ := by
    exact Submodule.smul_mem _ _ hu_mem
  have hd_mem_double : d ∈ ((ℝ ∙ d)ᗮ)ᗮ := by
    exact (ℝ ∙ d).le_orthogonal_orthogonal (Submodule.mem_span_singleton_self d)
  have h_inner_zero : ⟪c⁻¹ • u, s • d⟫ = 0 := by
    rw [inner_smul_right, Submodule.inner_left_of_mem_orthogonal
      (Submodule.mem_span_singleton_self d) hscaled_mem, mul_zero]
  have hnorm_sq : ‖c⁻¹ • u + s • d‖ ^ 2 = 1 := by
    calc
      ‖c⁻¹ • u + s • d‖ ^ 2 = ‖c⁻¹ • u‖ ^ 2 + ‖s • d‖ ^ 2 := by
        simpa [sq] using
          (norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
            (c⁻¹ • u) (s • d) h_inner_zero)
      _ = ‖c⁻¹ • u‖ ^ 2 + s ^ 2 := by
        have hnorm_sd_sq : ‖s • d‖ ^ 2 = s ^ 2 := by
          rw [norm_smul, hd, mul_one, Real.norm_eq_abs, sq_abs]
        rw [hnorm_sd_sq]
      _ = 1 := by
        nlinarith
  have hnorm : ‖c⁻¹ • u + s • d‖ = 1 := by
    nlinarith [hnorm_sq, norm_nonneg (c⁻¹ • u + s • d)]
  have hinner_nonneg : 0 ≤ ⟪d, c⁻¹ • u + s • d⟫ := by
    rw [inner_add_right, inner_smul_right, inner_smul_right, Submodule.inner_right_of_mem_orthogonal
      (Submodule.mem_span_singleton_self d) hu_mem, mul_zero, zero_add, real_inner_self_eq_norm_sq,
      hd]
    have hs_nonneg : 0 ≤ s := by
      rw [hs]
      exact Real.sqrt_nonneg _
    nlinarith
  -- The candidate sits on the unit sphere and keeps a nonnegative `d`-coordinate.
  rw [mem_sphericalCap_iff_norm]
  constructor
  · simpa [sphericalCapContractPreimageCandidate, hc, hu, hs] using hnorm
  · simpa [sphericalCapContractPreimageCandidate, hc, hu, hs] using hinner_nonneg

/-- Helper for Proposition 3.49: the strict-branch candidate maps back to the original cap point
under the contraction. -/
private lemma sphericalCapContract_candidate_preimage {d z : E} (hd : ‖d‖ = 1) {α : ℝ}
    (hα_left : 0 ≤ α) (hα_right : α < 1) (hz : z ∈ sphericalCap d α) :
    sphericalCapContract d α (sphericalCapContractPreimageCandidate d z α) = z := by
  set c : ℝ := sphericalCapScale α with hc
  set u : E := ((ℝ ∙ d)ᗮ).starProjection z with hu
  set s : ℝ := Real.sqrt (1 - ‖c⁻¹ • u‖ ^ 2) with hs
  have hc_sq_pos : 0 < 1 - α ^ 2 := by
    nlinarith [sq_nonneg α, hα_left, hα_right]
  have hc_pos : 0 < c := by
    rw [hc, sphericalCapScale]
    exact Real.sqrt_pos.mpr hc_sq_pos
  have hc_sq : c ^ 2 = 1 - α ^ 2 := by
    rw [hc, sphericalCapScale, Real.sq_sqrt]
    nlinarith [sq_nonneg α, hα_left, hα_right.le]
  rcases (mem_sphericalCap_iff_norm.mp hz) with ⟨hz_norm, hz_inner⟩
  have hz_inner_nonneg : 0 ≤ ⟪d, z⟫ := le_trans hα_left hz_inner
  have hu_mem : u ∈ (ℝ ∙ d)ᗮ := by
    rw [hu]
    exact Submodule.starProjection_apply_mem _ _
  have hu_sq_eq : ‖u‖ ^ 2 = 1 - ⟪d, z⟫ ^ 2 := by
    have hsplit :=
      inner_sq_add_norm_sq_orthogonalComplement_starProjection (d := d) (x := z) hd
    nlinarith [hsplit, hz_norm]
  have hscaled_sq_eq : ‖c⁻¹ • u‖ ^ 2 = (c⁻¹) ^ 2 * ‖u‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc_pos)]
    ring
  have hs_sq : s ^ 2 = 1 - ‖c⁻¹ • u‖ ^ 2 := by
    rw [hs, Real.sq_sqrt]
    have hu_sq_le : ‖u‖ ^ 2 ≤ c ^ 2 := by
      simpa [hu, hc_sq] using
        norm_sq_orthogonalComplement_starProjection_le_cap_radius_sq
          (d := d) (z := z) hd hα_left hz
    have hu_le_c : ‖u‖ ≤ c := by
      exact (sq_le_sq₀ (norm_nonneg _) (le_of_lt hc_pos)).mp hu_sq_le
    have hscaled_norm_le : ‖c⁻¹ • u‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc_pos)]
      have hmul := mul_le_mul_of_nonneg_left hu_le_c (inv_nonneg.mpr hc_pos.le)
      simpa [inv_mul_cancel₀ hc_pos.ne'] using hmul
    nlinarith [hscaled_norm_le, norm_nonneg (c⁻¹ • u)]
  have hscaled_mem : c⁻¹ • u ∈ (ℝ ∙ d)ᗮ := by
    exact Submodule.smul_mem _ _ hu_mem
  have hd_mem_double : d ∈ ((ℝ ∙ d)ᗮ)ᗮ := by
    exact (ℝ ∙ d).le_orthogonal_orthogonal (Submodule.mem_span_singleton_self d)
  have hproj_candidate :
      ((ℝ ∙ d)ᗮ).starProjection (c⁻¹ • u + s • d) = c⁻¹ • u := by
    refine Submodule.eq_starProjection_of_mem_orthogonal' ?_ ?_ rfl
    · exact hscaled_mem
    · exact Submodule.smul_mem _ _ hd_mem_double
  have hinner_candidate : ⟪d, c⁻¹ • u + s • d⟫ = s := by
    rw [inner_add_right, inner_smul_right, inner_smul_right, Submodule.inner_right_of_mem_orthogonal
      (Submodule.mem_span_singleton_self d) hu_mem, mul_zero, zero_add, real_inner_self_eq_norm_sq,
      hd]
    ring
  have hscaled_mul : (1 - α ^ 2) * ‖c⁻¹ • u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [hscaled_sq_eq, ← hc_sq]
    field_simp [hc_pos.ne']
  have haxis_sq : α ^ 2 + (1 - α ^ 2) * s ^ 2 = ⟪d, z⟫ ^ 2 := by
    nlinarith [hs_sq, hu_sq_eq, hscaled_mul]
  have haxis : Real.sqrt (α ^ 2 + (1 - α ^ 2) * s ^ 2) = ⟪d, z⟫ := by
    have harg_nonneg : 0 ≤ α ^ 2 + (1 - α ^ 2) * s ^ 2 := by
      rw [haxis_sq]
      exact sq_nonneg ⟪d, z⟫
    refine sq_eq_sq₀ (Real.sqrt_nonneg _) hz_inner_nonneg |>.mp ?_
    rw [Real.sq_sqrt harg_nonneg]
    exact haxis_sq
  -- Reconstruct the cap point from its orthogonal component and its `d`-coordinate.
  calc
    sphericalCapContract d α (sphericalCapContractPreimageCandidate d z α) =
        sphericalCapContract d α (c⁻¹ • u + s • d) := by
          simp [sphericalCapContractPreimageCandidate, hc, hu, hs]
    _ = c • ((ℝ ∙ d)ᗮ).starProjection (c⁻¹ • u + s • d) +
          Real.sqrt (α ^ 2 + (1 - α ^ 2) * ⟪d, c⁻¹ • u + s • d⟫ ^ 2) • d := by
            rfl
    _ = c • (c⁻¹ • u) + Real.sqrt (α ^ 2 + (1 - α ^ 2) * s ^ 2) • d := by
          rw [hproj_candidate, hinner_candidate]
    _ = u + Real.sqrt (α ^ 2 + (1 - α ^ 2) * s ^ 2) • d := by
          rw [smul_smul, mul_inv_cancel₀ hc_pos.ne', one_smul]
    _ = u + ⟪d, z⟫ • d := by rw [haxis]
    _ = z := by
          simpa [hu, Submodule.starProjection_unit_singleton ℝ hd z, add_comm, add_left_comm,
            add_assoc] using
            (Submodule.starProjection_add_starProjection_orthogonal (K := ℝ ∙ d) z)

/-- Helper for Proposition 3.49: for `α < 1`, every cap point has an explicit preimage in the
hemisphere under the contraction map. -/
private lemma sphericalCapContract_preimage_of_mem {d z : E} (hd : ‖d‖ = 1) {α : ℝ}
    (hα_left : 0 ≤ α) (hα_right : α < 1) (hz : z ∈ sphericalCap d α) :
    ∃ x ∈ sphericalCap d 0, sphericalCapContract d α x = z := by
  -- The strict branch now uses the named candidate so the hemisphere proof and evaluation proof
  -- remain transport-stable.
  refine ⟨sphericalCapContractPreimageCandidate d z α, ?_, ?_⟩
  · exact candidate_preimage_mem_sphericalCap_zero (d := d) (z := z) hd hα_left hα_right hz
  · exact sphericalCapContract_candidate_preimage (d := d) (z := z) hd hα_left hα_right hz

/-- Helper for Proposition 3.49: every cap point lies in the image of the hemisphere under the
contraction map. -/
private lemma sphericalCap_subset_contract_image_hemisphere {d : E} (hd : ‖d‖ = 1) {α : ℝ}
    (hα_left : 0 ≤ α) (hα_right : α ≤ 1) :
    sphericalCap d α ⊆ sphericalCapContract d α '' sphericalCap d 0 := by
  intro z hz
  -- Route correction: the image inclusion only needs a preimage construction, not an exact-image
  -- theorem for the whole contraction map.
  rcases eq_or_lt_of_le hα_right with hα_eq | hα_lt
  · subst hα_eq
    refine ⟨d, ?_, ?_⟩
    · rw [mem_sphericalCap_iff_norm]
      refine ⟨hd, ?_⟩
      rw [real_inner_self_eq_norm_sq, hd]
      positivity
    · -- At the endpoint `α = 1`, the cap collapses to the single point `d`.
      rw [eq_direction_of_mem_sphericalCap_one (d := d) (z := z) hd hz]
      simp [sphericalCapContract, sphericalCapScale, hd, Submodule.starProjection_orthogonalComplement_singleton_eq_zero]
  · rcases sphericalCapContract_preimage_of_mem (d := d) (z := z) hd hα_left hα_lt hz with
      ⟨x, hx, hcontract⟩
    exact ⟨x, hx, hcontract⟩

/-- Helper for Proposition 3.49: the ENNReal Lipschitz factor `√(1 - α²)` is exactly the surface
measure exponent `(1 - α²)^(sphereDim / 2)`. -/
private lemma sphericalCapScale_ennreal_rpow {α : ℝ} (hα_left : 0 ≤ α) (hα_right : α ≤ 1) :
    ((Real.toNNReal (sphericalCapScale α) : ENNReal) ^ sphereRank) =
      ENNReal.ofReal (Real.rpow (1 - α ^ 2) (sphereDim / 2)) := by
  have hbase_nonneg : 0 ≤ 1 - α ^ 2 := by
    nlinarith [sq_nonneg α, hα_left, hα_right]
  calc
    ((Real.toNNReal (sphericalCapScale α) : ENNReal) ^ sphereRank) =
        ENNReal.ofReal (sphericalCapScale α) ^ sphereRank := by
          have hcoerce :
              ((Real.toNNReal (sphericalCapScale α) : ENNReal)) =
                ENNReal.ofReal (sphericalCapScale α) := by
            exact ENNReal.ofNNReal_toNNReal _
          rw [hcoerce]
    _ = ENNReal.ofReal ((sphericalCapScale α) ^ sphereRank) := by
          symm
          exact ENNReal.ofReal_pow (Real.sqrt_nonneg _) _
    _ = ENNReal.ofReal (Real.rpow (1 - α ^ 2) (sphereDim / 2)) := by
          congr 1
          rw [sphericalCapScale, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
            ← Real.rpow_mul hbase_nonneg]
          have hexp : (1 / 2 : ℝ) * ↑sphereRank = sphereDim / 2 := by
            change (1 / 2 : ℝ) * ↑sphereRank = ↑sphereRank / 2
            ring
          rw [hexp]
          change Real.rpow (1 - α ^ 2) (sphereDim / 2) =
            Real.rpow (1 - α ^ 2) (sphereDim / 2)
          rfl

/-- Proposition 3.49 at the intrinsic owner level: the canonical Euclidean surface measure
`μHE[sphereRank]` of a spherical cap of the unit sphere is bounded by the measure of the
corresponding hemisphere times `(1 - α^2)^(sphereDim / 2)` for every `α ∈ [0, 1]`. The
Kelley-specific lower bound `1 / 2 ≤ α` belongs only to a later specialization, not to the
source-facing spherical-cap estimate itself. No extra lower bound on `Module.finrank ℝ E`
belongs to the public cap estimate: once `‖d‖ = 1`, the statement already makes sense and stays
valid even in the one-dimensional case. Specializing `E = EuclideanSpace ℝ (Fin n)` recovers the
textbook `ℝⁿ` formulation used in the Kelley-method cut-count argument. The raw Hausdorff measure
`μH[sphereDim]` is only the scaled bridge/view behind this canonical surface-measure owner. -/
-- Proof sketch: rotate `d` to a fixed unit vector by an orthogonal isometry, express the cap as a
-- graph over the Euclidean ball of radius `√(1 - α^2)`, and compare the resulting surface
-- integral with the hemisphere case after the scaling `y = √(1 - α^2) z`.
theorem euclideanHausdorffMeasure_sphericalCap_le_hemisphere_mul_rpow
    {d : E} (hd : ‖d‖ = 1) {α : ℝ} (hα_left : 0 ≤ α) (hα_right : α ≤ 1) :
    μHE[sphereRank] (sphericalCap d α) ≤
      μHE[sphereRank] (sphericalCap d 0) *
        ENNReal.ofReal (Real.rpow (1 - α ^ 2) (sphereDim / 2)) := by
  have himage_h :
      μH[sphereDim] (sphericalCapContract d α '' sphericalCap d 0) ≤
        ((Real.toNNReal (sphericalCapScale α) : ENNReal) ^ sphereRank) *
          μH[sphereDim] (sphericalCap d 0) := by
    -- The contraction controls the cap measure through the standard Hausdorff image estimate.
    simpa [mul_comm] using
      (sphericalCapContract_lipschitz (d := d) hd hα_left hα_right).hausdorffMeasure_image_le
        (d := sphereDim) (by positivity) (s := sphericalCap d 0)
  have hcap_h :
      μH[sphereDim] (sphericalCap d α) ≤
        ((Real.toNNReal (sphericalCapScale α) : ENNReal) ^ sphereRank) *
          μH[sphereDim] (sphericalCap d 0) := by
    -- The cap sits inside the image of the hemisphere, so monotonicity reduces to the image bound.
    exact le_trans
      (measure_mono
        (sphericalCap_subset_contract_image_hemisphere (d := d) hd hα_left hα_right))
      himage_h
  have hcap_h' :
      μH[sphereDim] (sphericalCap d α) ≤
        μH[sphereDim] (sphericalCap d 0) *
          ENNReal.ofReal (Real.rpow (1 - α ^ 2) (sphereDim / 2)) := by
    rw [sphericalCapScale_ennreal_rpow hα_left hα_right] at hcap_h
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcap_h
  -- Rewriting `μHE` back to its scaled Hausdorff form leaves exactly the contraction factor.
  simp_rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply]
  rw [ENNReal.smul_def, smul_eq_mul]
  rw [ENNReal.smul_def, smul_eq_mul]
  calc
    _ ≤ _ * (μH[sphereDim] (sphericalCap d 0) *
          ENNReal.ofReal (Real.rpow (1 - α ^ 2) (sphereDim / 2))) := by
            exact mul_le_mul_right hcap_h' _
    _ = _ := by ac_rfl

end FiniteDimensional

/-! ### Theorem_3_49 (from Chap03) -/
noncomputable section

universe u

variable {n : ℕ}

open EuclideanSpace

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Theorem 3.49 lies in the chapter's feasibility-with-separation-oracle lower-bound domain.

Sampled owner-style declarations:
- `FeasibilityProblemWithSeparationOracle` and `SeparationOracleAnswer` in `Definition_3_49`, the
  source-facing owner of the feasible set together with its oracle access;
- `(interior S).Nonempty` in `Definition_3_50`, the canonical owner predicate for the textbook
  interior-ball assumption;
- `DeterministicValueOracleMethod.oracleTranscript` and
  `DeterministicValueOracleMethod.SolvesLinftyLipschitzProblemClassWithin` in
  `Chap01/Theorem_1_3_9`, the chapter's owner pattern for transcript recursion and bounded-call
  oracle solvability.

Best owner abstraction:
- source-facing: existence of a hard instance directly on
  `FeasibilityProblemWithSeparationOracle (EuclideanSpace ℝ (Fin n))`;
- core/canonical: the generic transcript-based method owner `SeparationOracleAlgorithm X`
  together with `FeasibilityProblemWithSeparationOracle`, `SeparationOracleAnswer`, the
  feasibility-problem coercion to `Set`, the membership view `x ∈ problem`, the interior owner
  `(interior (problem : Set E)).Nonempty`, and the canonical terminal output shape `Option E`;
- bridge/view: the observable-reply projection `SeparationOracleAnswer.oracleReply`,
  `SeparationOracleOutput.IsCorrect`, and `SeparationOracleAlgorithm.SolvesWithin`.

Primitive data:
- the feasibility owner
  `problem : FeasibilityProblemWithSeparationOracle (EuclideanSpace ℝ (Fin n))`;
- the transcript-based query/output rules of a deterministic black-box algorithm on an ambient
  query type `X`, observing replies in `Option X`.

Derived API:
- the observable reply extracted from a proof-carrying oracle answer;
- oracle transcripts;
- output correctness;
- solvability within `k` calls;
- the hard-instance conjunction in the final existence theorem.

This file therefore keeps the hard-instance payload as a direct existential conjunction on the
existing feasibility owner, rather than introducing a second public hardness wrapper around the
same data. -/

namespace SeparationOracleOutput

/-- A terminal output `some x` is a proposed feasible point, while `none` is the certificate that
the feasible set misses `B∞(0, ε)`. It is correct when it satisfies the corresponding textbook
condition. -/
def IsCorrect
    (output : Option E)
    (problem : FeasibilityProblemWithSeparationOracle E) (ε : ℝ) : Prop :=
  match output with
  | some x => x ∈ problem
  | none => (problem : Set E) ∩ linftyClosedBall ε = ∅

/-- A candidate point output is correct exactly when the proposed point is feasible. -/
@[simp] theorem isCorrect_some_iff
    (problem : FeasibilityProblemWithSeparationOracle E) (ε : ℝ) (x : E) :
    SeparationOracleOutput.IsCorrect (some x) problem ε ↔ x ∈ problem :=
  Iff.rfl

/-- A `none` output is correct exactly when the feasible set is disjoint from the textbook ball
`B∞(0, ε)`. -/
@[simp] theorem isCorrect_none_iff
    (problem : FeasibilityProblemWithSeparationOracle E) (ε : ℝ) :
    SeparationOracleOutput.IsCorrect (none : Option E) problem ε ↔
      (problem : Set E) ∩ linftyClosedBall ε = ∅ :=
  Iff.rfl

end SeparationOracleOutput

/-- A deterministic separation-oracle algorithm chooses each new query from the previous oracle
transcript and, after finitely many calls, returns either a candidate feasible point or a
certificate that the feasible set misses `B∞(0, ε)`. The transcript records only the black-box
observable reply: `none` for a certified feasible query point and `some g` for a separating vector
`g`. -/
structure SeparationOracleAlgorithm (X : Type u) where
  /-- The next query point as a function of the observable oracle transcript accumulated so far. -/
  query : List (X × Option X) → X
  /-- The terminal output computed from the same transcript. -/
  output : List (X × Option X) → Option X

namespace SeparationOracleAlgorithm

variable {X : Type u}

local notation "Transcript" => List (X × Option X)

/-- The length-`k` oracle transcript generated by repeatedly querying the problem's separation
oracle according to the algorithm's deterministic query rule, recording only the observable
black-box replies. -/
def oracleTranscript
    (algorithm : SeparationOracleAlgorithm X)
    (oracle : X → Option X) : ℕ → Transcript
  | 0 => []
  | k + 1 =>
      let transcript := algorithm.oracleTranscript oracle k
      let x := algorithm.query transcript
      transcript ++ [(x, oracle x)]

/-- An algorithm solves the feasibility problem within `k` oracle calls when its output after the
length-`k` transcript is a correct feasible point or a correct no-point-in-ball certificate. -/
def SolvesWithin
    (algorithm : SeparationOracleAlgorithm E)
    (problem : FeasibilityProblemWithSeparationOracle E)
    (ε : ℝ) (k : ℕ) : Prop :=
  SeparationOracleOutput.IsCorrect
    (algorithm.output
      (algorithm.oracleTranscript (fun x ↦ (problem.oracle x).oracleReply) k))
    problem ε

end SeparationOracleAlgorithm

-- Proof sketch: fix an oracle budget `k` below the logarithmic threshold and let an arbitrary
-- deterministic separation-oracle algorithm interact with the resisting-oracle box construction
-- inside `B∞(0, R)`. After `k` calls, the answers are still compatible with a box whose Euclidean
-- inradius is at least `(R / 2) * exp (-k / n)`, hence still larger than `ε`. Using the interior
-- ball assumption, choose a feasible set contained in the remaining uncertainty region so that the
-- algorithm cannot distinguish a genuine feasible point from the alternative that the feasible set
-- misses `B∞(0, ε)`. Therefore no algorithm can produce a correct output within `k` calls on that
-- hard instance.
/-- Theorem 3.49: for every oracle budget below `n log (R / (2 ε))`, there exists a feasibility
problem with separation oracle, whose feasible set has nonempty interior and is contained in the
textbook ball `B∞(0, R)`, on which no deterministic separation-oracle algorithm can correctly
output either a feasible point or a certificate that the feasible set misses `B∞(0, ε)` within
that many oracle calls. -/
-- Proof sketch: construct a resisting-oracle hard instance whose feasible set remains compatible
-- with the transcript after `k` queries; this yields an instance whose feasible set has nonempty
-- interior, lies in `B∞(0, R)`, and defeats every deterministic separation-oracle algorithm of
-- depth `k`.
theorem exists_hard_feasibility_problem_for_short_separation_oracle_algorithms
    (m : ℕ) {R ε : ℝ} (hε : 0 < ε) {k : ℕ}
    (hk : (k : ℝ) < (m : ℝ) * Real.log (R / (2 * ε))) :
    ∃ problem : FeasibilityProblemWithSeparationOracle (EuclideanSpace ℝ (Fin m)),
      (interior (problem : Set (EuclideanSpace ℝ (Fin m)))).Nonempty ∧
      (problem : Set (EuclideanSpace ℝ (Fin m))) ⊆ linftyClosedBall R ∧
      ∀ algorithm : SeparationOracleAlgorithm (EuclideanSpace ℝ (Fin m)),
        ¬ SeparationOracleAlgorithm.SolvesWithin algorithm problem ε k := sorry

end
