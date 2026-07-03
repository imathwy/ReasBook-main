

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_3_32 (from Chap03) -/
universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Corollary 3.32 is a `bridge/view` reformulation in the chapter convex-analysis API. The
`core/canonical` owner theorem is
`isMinOn_iff_exists_subgradient_neg_mem_normal_cone` from Theorem 3.31, and the textbook
feasible-displacement inequality is the owner normal-cone membership criterion `mem_normal_cone`.
This file keeps only the source-facing variational-inequality restatement. -/
recall effective_domain
recall IsProperExtendedRealFunction
recall is_convex_function
recall subdifferential
recall normal_cone
recall mem_normal_cone
recall isMinOn_iff_exists_subgradient_neg_mem_normal_cone

-- Proof sketch: replace the constrained problem by the extended-real objective obtained by adding
-- the indicator of `C`, so minimization on `C` becomes unconstrained minimization on `E`. Under the
-- qualification `ri(dom f) ∩ ri(C) ≠ ∅`, apply the convex subdifferential sum rule together with
-- the identification of the indicator subdifferential with the normal cone. Fermat's criterion for
-- the constrained objective then gives `0 ∈ ∂f(xStar) + N_C(xStar)`, which is equivalent to the
-- existence of a subgradient whose pairing with every feasible displacement `x - xStar` is
-- nonnegative, and the converse runs the same implications in reverse.
/-- Corollary 3.32: for a proper convex extended-real-valued function on a finite-dimensional real
normed space and a convex feasible set `C` satisfying `ri(dom f) ∩ ri(C) ≠ ∅`, a feasible point
`xStar` minimizes `f` on `C` if and only if there exists a subgradient at `xStar` whose pairing
with every feasible displacement `x - xStar` is nonnegative. -/
theorem isMinOn_iff_exists_subgradient_nonneg_on_convex_set
    {f : E → EReal} (hf : IsProperExtendedRealFunction f) (hconv : is_convex_function f)
    {C : Set E} (hC : Convex ℝ C)
    (hri : (intrinsicInterior ℝ (effective_domain f) ∩ intrinsicInterior ℝ C).Nonempty)
    {xStar : E} (hxStar : xStar ∈ C) :
    IsMinOn f C xStar ↔
      ∃ g : Module.Dual ℝ E,
        g ∈ subdifferential f xStar ∧ ∀ x ∈ C, 0 ≤ g (x - xStar) := by
  rw [isMinOn_iff_exists_subgradient_neg_mem_normal_cone (f := f) hf.ne_bot hconv hC hri hxStar]
  constructor
  · rintro ⟨g, hg, hgcone⟩
    refine ⟨g, hg, ?_⟩
    simpa using (mem_normal_cone C hxStar (-g)).1 hgcone
  · rintro ⟨g, hg, hgineq⟩
    refine ⟨g, hg, ?_⟩
    exact (mem_normal_cone C hxStar (-g)).2 (by simpa using hgineq)

end

/-! ### Proposition_3_32 (from Chap03) -/
open scoped BigOperators Pointwise
open InnerProductSpace
open Metric

/- Proposition 3.32 is a `source-facing` computation for the owner objective
`fermatWeberObjective`. The `core/canonical` owner is the chapter subdifferential
`subdifferentialAt`, and the Euclidean bridge/view owner is `euclideanSubdifferentialAt`. The
supporting declarations are the finite-sum rule
`subdifferentialAt_finset_sum_eq_sum_subdifferentialAt`, the affine Euclidean-norm formula
`euclidean_subdifferentialAt_affine_l2_norm_eq_piecewise`, and the scalar-composition rule
`subdifferentialAt_comp_eq_smul_subdifferentialAt`. The weighted single-site distance term is
therefore only a derived view, not a second public owner abstraction. -/

section

variable {m d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

recall fermatWeberObjective
recall euclideanSubdifferentialAt
recall euclidean_subdifferentialAt_affine_l2_norm_eq_piecewise
recall subdifferentialAt_comp_eq_smul_subdifferentialAt
recall subdifferentialAt_finset_sum_eq_sum_subdifferentialAt

-- Proof sketch: rewrite the weighted one-site distance `y ↦ ω * dist y a` using `dist_eq_norm`
-- into `y ↦ ω * ‖y - a‖`, then obtain its Euclidean
-- subdifferential from the affine `ℓ₂` formula and the scalar-composition rule for the
-- nonnegative factor `ω`.
private theorem euclidean_subdifferentialAt_weighted_dist_eq_piecewise
    (ω : ℝ) (hω : 0 ≤ ω) (a x : E) :
    euclideanSubdifferentialAt (fun y : E ↦ ω * dist y a) x =
      if x = a then
        closedBall (0 : E) ω
      else
        {ω • ((‖x - a‖)⁻¹ • (x - a))} := by
  sorry

-- Proof sketch: rewrite `fermatWeberObjective ω a` as the finite sum of the weighted one-site
-- terms `fun y ↦ ω i * dist y (a i)` using `fermatWeberObjective_apply`. Apply the owner
-- finite-sum rule for subdifferentials, then transport each summand through the private
-- one-site bridge above.
/-- Proposition 3.32: the vector-side subdifferential of the Fermat-Weber objective
`x ↦ ∑ i, ω_i ‖x - a_i‖₂` is the finite Minkowski sum of the single-term subdifferentials, so each
summand contributes the normalized vector `ω_i (x - a_i) / ‖x - a_i‖₂` away from its site and the
closed Euclidean ball of radius `ω_i` at its site; this remains valid for nonnegative weights,
with `ω_i = 0` giving the singleton `{0}` in both cases. -/
theorem euclidean_subdifferentialAt_fermatWeberObjective_eq_finset_sum_piecewise
    (ω : Fin m → ℝ) (hω : ∀ i, 0 ≤ ω i) (a : Fin m → E) (x : E) :
    euclideanSubdifferentialAt (fermatWeberObjective ω a) x =
      ∑ i : Fin m,
        if x = a i then
          closedBall (0 : E) (ω i)
        else
          {ω i • ((‖x - a i‖)⁻¹ • (x - a i))} := sorry

end
