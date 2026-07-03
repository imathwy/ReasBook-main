

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_18 (from Chap03) -/
universe u

open InnerProductSpace (toDual toDual_apply_apply)
open scoped Gradient RealInnerProductSpace

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Definition 3.18 is `source-facing`, but its owner notions already exist upstream: the dual
normal cone `normal_cone` from Definition 3.3 and the composite stationary predicate
`is_stationary_point` from Definition 3.17. This file therefore keeps only the constrained
specialization together with the Euclidean `bridge/view` theorem that rewrites owner
normal-cone membership into the textbook variational inequality. -/

recall is_stationary_point
recall normal_cone

/-- Definition 3.18: constrained stationarity is the specialization of the composite stationary
predicate from Definition 3.17 to the indicator term `δ_C`. -/
def is_stationary_point_on (f : E → ℝ) (C : Set E) (x : E) : Prop :=
  is_stationary_point (fun y ↦ (f y : EReal)) (extendedIndicator C) x

private theorem neg_gradient_mem_normal_cone_iff (f : E → ℝ) (C : Set E) (x : E) :
    (-toDual ℝ E (∇ f x) : Module.Dual ℝ E) ∈ normal_cone C x ↔
      x ∈ C ∧ ∀ y ∈ C, ⟪∇ f x, y - x⟫ ≥ (0 : ℝ) := by
  constructor
  · intro h
    by_cases hx : x ∈ C
    · refine ⟨hx, fun y hy ↦ ?_⟩
      have hcone := (mem_normal_cone C hx _).1 h
      simpa [toDual_apply_apply, inner_neg_left, neg_nonpos] using hcone y hy
    · exfalso
      simp [normal_cone_eq_empty_of_not_mem C hx] at h
  · rintro ⟨hx, hcone⟩
    refine (mem_normal_cone C hx _).2 fun y hy ↦ ?_
    simpa [toDual_apply_apply, inner_neg_left, neg_nonpos] using hcone y hy

/-- Unfolding constrained stationarity gives differentiability of `f` at `x` together with
membership of `-∇ f(x)` in the owner normal cone of `C` at `x`, transported by
`toDual`. -/
@[simp] theorem is_stationary_point_on_iff
    (f : E → ℝ) (C : Set E) (x : E) :
    is_stationary_point_on f C x ↔
      DifferentiableAt ℝ f x ∧
        (-toDual ℝ E (∇ f x) : Module.Dual ℝ E) ∈ normal_cone C x := by
  simp [is_stationary_point_on, is_stationary_point_iff,
    subdifferential_extended_indicator_eq_normal_cone, is_differentiable_at, finite_domain]

-- Proof sketch: unfold `is_stationary_point_on` through the owner predicate from Definition 3.17,
-- then rewrite owner normal-cone membership using `normal_cone` and `toDual_apply_apply`. The
-- condition `⟪-gradient f x, y - x⟫ ≤ 0` is equivalent to `⟪gradient f x, y - x⟫ ≥ 0` by
-- `inner_neg_left`.
/-- A constrained stationary point is equivalently a feasible differentiable point satisfying the
first-order variational inequality on every feasible displacement. -/
theorem is_stationary_point_on_iff_forall_inner_nonneg (f : E → ℝ) (C : Set E) (x : E) :
    is_stationary_point_on f C x ↔
      DifferentiableAt ℝ f x ∧ x ∈ C ∧ ∀ y ∈ C, ⟪∇ f x, y - x⟫ ≥ (0 : ℝ) := by
  rw [is_stationary_point_on_iff, neg_gradient_mem_normal_cone_iff]

end

/-! ### Proposition_3_18 (from Chap03) -/
section

open WithLp (toLp)

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 3.18 is a `bridge/view` corollary in the chapter Euclidean subdifferential API.
Its source-facing coordinate description is already owned upstream by
`l1CoordinateSubgradientVectors`, together with the derived API
`sign_vector_mem_l1CoordinateSubgradientVectors`. The present item only transports that canonical
member through Proposition 3.17's owner-set identification
`subdifferentialAt_l1_norm_eq_coordinatewise_sign_constraints`. -/

-- Proof sketch: rewrite the target subdifferential through Proposition 3.17 and then use the
-- upstream owner-view lemma `sign_vector_mem_l1CoordinateSubgradientVectors`.
/-- Proposition 3.18: for `f(x) = ∑ i, |x i|` on `ℝ^n`, the coordinatewise sign vector `sgn(x)`
viewed in the dual via the Euclidean identification belongs to the subdifferential `∂ f(x)`. -/
theorem sign_vector_mem_subdifferentialAt_l1_norm
    (x : E) :
    toLp 2 (sgn x) ∈ euclideanSubdifferentialAt (fun y : E ↦ ‖toLp 1 fun i ↦ y i‖) x := by
  simpa [subdifferentialAt_l1_norm_eq_coordinatewise_sign_constraints] using
    sign_vector_mem_l1CoordinateSubgradientVectors x

end

/-! ### Theorem_3_18 (from Chap03) -/
open Bornology
open scoped BigOperators Pointwise

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 3.18 is `source-facing` in the chapter subdifferential API. The owner notions
`effective_domain`, `is_convex_function`, `subdifferential`, `intrinsicInterior ℝ`, and
`strongDualSubdifferential` already live upstream, so this file contributes only the
relative-interior qualification for the existing finite-sum rule. Under the qualification
hypothesis, nonemptiness of every effective domain is already forced, so the only primitive
codomain restriction in the main theorem is that no summand takes the value `⊥`. -/
recall effective_domain
recall is_convex_function
recall subdifferential
recall strongDualSubdifferential
recall strongDualSubdifferential_eq_image_subdifferential

-- Proof sketch: the inclusion `⊇` is the weak sum rule obtained by summing subgradient
-- inequalities. For `⊆`, use Rockafellar's conjugate sum theorem under the qualification
-- `(\⋂ i, ri(dom fᵢ)).Nonempty`, choose an optimal decomposition of a conjugate subgradient of the
-- sum, and apply Fenchel--Young equality termwise to show that each component lies in the
-- corresponding subdifferential. The relative-interior qualification already implies every
-- `effective_domain (f i)` is nonempty, so only the no-`⊥` half of properness is primitive data.
/-- Theorem 3.18: if a finite family of convex extended-real-valued functions never takes the
value `-∞` and has nonempty intersection of the relative interiors of its effective domains, then
the subdifferential of the pointwise sum equals the pointwise sum of the individual
subdifferentials at every point. Here the relative interior hypothesis is rendered by
`intrinsicInterior ℝ`. -/
theorem subdifferential_finset_sum_eq_sum_subdifferential_of_nonempty_iInter_relativeInterior
    {m : ℕ} (f : Fin m → E → EReal) (x : E)
    (h_ne_bot : ∀ i : Fin m, ∀ y : E, f i y ≠ ⊥)
    (hconvex : ∀ i : Fin m, is_convex_function (f i))
    (hqual : (⋂ i : Fin m, intrinsicInterior ℝ (effective_domain (f i))).Nonempty) :
    subdifferential (fun y ↦ ∑ i : Fin m, f i y) x =
      ∑ i : Fin m, subdifferential (f i) x := sorry

private theorem image_finset_sum
    {m : ℕ} (f : Fin m → Set (Module.Dual ℝ E)) :
    (LinearMap.toContinuousLinearMap : (Module.Dual ℝ E) ≃ₗ[ℝ] StrongDual ℝ E) ''
        (∑ i : Fin m, f i) =
      ∑ i : Fin m,
        ((LinearMap.toContinuousLinearMap : (Module.Dual ℝ E) ≃ₗ[ℝ] StrongDual ℝ E) '' f i) := by
  induction m with
  | zero =>
      ext g
      simp
  | succ m ihm =>
      simp [Fin.sum_univ_succ, ihm, Set.image_add]

/-- The continuous-dual bridge/view of Theorem 3.18. -/
theorem
    strongDualSubdifferential_finset_sum_eq_sum_strongDualSubdifferential_of_nonempty_iInter_relativeInterior
    {m : ℕ} (f : Fin m → E → EReal) (x : E)
    (h_ne_bot : ∀ i : Fin m, ∀ y : E, f i y ≠ ⊥)
    (hconvex : ∀ i : Fin m, is_convex_function (f i))
    (hqual : (⋂ i : Fin m, intrinsicInterior ℝ (effective_domain (f i))).Nonempty) :
    strongDualSubdifferential (fun y ↦ ∑ i : Fin m, f i y) x =
      ∑ i : Fin m, strongDualSubdifferential (f i) x := by
  let e : (Module.Dual ℝ E) ≃ₗ[ℝ] StrongDual ℝ E := LinearMap.toContinuousLinearMap
  calc
    strongDualSubdifferential (fun y ↦ ∑ i : Fin m, f i y) x =
        e '' subdifferential (fun y ↦ ∑ i : Fin m, f i y) x :=
      strongDualSubdifferential_eq_image_subdifferential _ _
    _ =
        e '' ∑ i : Fin m, subdifferential (f i) x := by
      rw [subdifferential_finset_sum_eq_sum_subdifferential_of_nonempty_iInter_relativeInterior
        f x h_ne_bot hconvex hqual]
    _ =
        ∑ i : Fin m, e '' subdifferential (f i) x :=
      image_finset_sum (fun i ↦ subdifferential (f i) x)
    _ = ∑ i : Fin m, strongDualSubdifferential (f i) x := by
      have himage :
          (fun i : Fin m ↦ e '' subdifferential (f i) x) =
            fun i : Fin m ↦ strongDualSubdifferential (f i) x := by
        funext i
        simpa [e] using (strongDualSubdifferential_eq_image_subdifferential (f i) x).symm
      simp [himage]

end
