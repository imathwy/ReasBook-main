

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_17 (from Chap03) -/
universe u

open InnerProductSpace (toDual)
open scoped Gradient

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Definition 3.17 is `source-facing`. In this finite-dimensional convex subdifferential domain,
the chapter owner abstractions are `is_differentiable_at` for extended-real differentiability and
`subdifferential` for the nonsmooth term. The vector `-∇ f(x)` enters only through the canonical
Riesz functional `-toDual ℝ E (∇ (fun y ↦ (f y).toReal) x)`, viewed in the owner
`subdifferential g x`; the continuous-dual set `strongDualSubdifferential` is therefore only a
derived `bridge/view`, not primitive public data here. This file keeps only that source-facing
predicate and its atomic owner-style specification theorem, with no parallel wrapper around the
upstream owners. -/
recall is_differentiable_at
recall subdifferential

/-- Definition 3.17: the stationarity condition for the composite objective `f + g` says that
`f` is differentiable at `x` in the sense of Definition 3.10 and the continuous-dual vector
represented by the negative gradient `-∇ f(x)` belongs to the owner subdifferential `∂ g(x)`. In
the textbook setting, `f` is proper, `g` is proper convex, and `dom(g) ⊆ interior (dom(f))`. -/
def is_stationary_point (f g : E → EReal) (x : E) : Prop :=
  is_differentiable_at f x ∧
    (-toDual ℝ E (∇ (fun y ↦ (f y).toReal) x) : Module.Dual ℝ E) ∈ subdifferential g x

/-- Unfolding `is_stationary_point` gives the chapter differentiability condition for `f` at `x`
together with membership of the negative gradient in the owner subdifferential of `g` at `x`. -/
@[simp] theorem is_stationary_point_iff {f g : E → EReal} {x : E} :
    is_stationary_point f g x ↔
      is_differentiable_at f x ∧
        (-toDual ℝ E (∇ (fun y ↦ (f y).toReal) x) : Module.Dual ℝ E) ∈ subdifferential g x :=
  Iff.rfl

end

/-! ### Proposition_3_17 (from Chap03) -/
open WithLp (toLp)
open scoped BigOperators

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 3.17 is a `bridge/view` item in the chapter Euclidean subdifferential API. The
owner abstraction is `subdifferentialAt` from Theorem 3.4, and its canonical vector-side bridge is
`euclideanSubdifferentialAt`. The only source-facing content here is the coordinate sign-cube
description of that owner set for the `ℓ₁` norm, now written through mathlib's canonical
`WithLp 1` norm on finite products, so the theorem should use the bridge directly rather than
re-expand the `toDualMap` preimage by hand. -/

recall euclideanSubdifferentialAt
recall PiLp.norm_eq_of_L1

/-- The coordinatewise sign cube describing the vector-side subgradients of the `ℓ₁` norm at
`x`. -/
def l1CoordinateSubgradientVectors (x : E) : Set E :=
  (fun z : E ↦ fun i ↦ z i) ⁻¹'
    Set.pi Set.univ (fun i ↦ if x i = 0 then Set.Icc (-1 : ℝ) 1 else {Real.sign (x i)})

/-- Membership in `l1CoordinateSubgradientVectors x` means matching the coordinatewise sign on the
nonzero coordinates of `x` and staying in `[-1, 1]` on the zero coordinates. -/
@[simp] theorem mem_l1CoordinateSubgradientVectors_iff
    {x z : E} :
    z ∈ l1CoordinateSubgradientVectors x ↔
      (∀ i, x i ≠ 0 → z i = Real.sign (x i)) ∧
        ∀ i, x i = 0 → |z i| ≤ 1 := by
  constructor
  · intro hz
    have hz' : ∀ i, z i ∈ if x i = 0 then Set.Icc (-1 : ℝ) 1 else {Real.sign (x i)} := by
      simpa [l1CoordinateSubgradientVectors] using hz
    refine ⟨?_, ?_⟩
    · intro i hxi
      simpa [hxi] using hz' i
    · intro i hxi
      simpa [Set.mem_Icc, abs_le, hxi] using hz' i
  · rintro ⟨hsign, hzero⟩
    have hz' : ∀ i, z i ∈ if x i = 0 then Set.Icc (-1 : ℝ) 1 else {Real.sign (x i)} := by
      intro i
      by_cases hxi : x i = 0
      · simpa [Set.mem_Icc, abs_le, hxi] using hzero i hxi
      · simp [hxi, hsign i hxi]
    simp [l1CoordinateSubgradientVectors, hz']

/-- The canonical coordinatewise sign vector belongs to the coordinate description of the `ℓ₁`
subdifferential. -/
theorem sign_vector_mem_l1CoordinateSubgradientVectors (x : E) :
    toLp 2 (sgn x) ∈ l1CoordinateSubgradientVectors x := by
  rw [mem_l1CoordinateSubgradientVectors_iff]
  refine ⟨?_, ?_⟩
  · intro i hxi
    rcases lt_or_gt_of_ne hxi with h_neg | h_pos
    · simp [sgn_apply, not_le_of_gt h_neg, Real.sign_of_neg h_neg]
    · simp [sgn_apply, h_pos.le, Real.sign_of_pos h_pos]
  · intro i hxi
    simp [sgn_apply, hxi]

-- Proof sketch: write the `ℓ₁` norm on `ℝ^n` as the finite sum of the coordinate functions
-- `y ↦ |y i|`, apply the finite-dimensional sum rule for subdifferentials, and use the
-- one-dimensional computation `euclidean_subdifferentialAt_abs_eq_piecewise` for `t ↦ |t|` on
-- each
-- coordinate. The resulting statement is expressed directly through the chapter bridge
-- `euclideanSubdifferentialAt`, with the objective written via the canonical `WithLp 1` norm on
-- finite products.
/-- Proposition 3.17: for the `ℓ₁` norm
`f(x) = ‖toLp 1 (fun i ↦ x i)‖ = ∑ i, |x i|` on `ℝ^n = EuclideanSpace ℝ (Fin n)`, the
Euclidean/vector-side subdifferential consists exactly of the vectors in
`l1CoordinateSubgradientVectors x`, i.e. the vectors whose coordinates equal `Real.sign (x i)` on
the nonzero coordinates of `x` and lie in `[-1, 1]` on the zero coordinates. -/
theorem subdifferentialAt_l1_norm_eq_coordinatewise_sign_constraints
    (x : E) :
    euclideanSubdifferentialAt (fun y : E ↦ ‖toLp 1 fun i ↦ y i‖) x =
      l1CoordinateSubgradientVectors x := sorry

end

/-! ### Theorem_3_17 (from Chap03) -/
open scoped BigOperators Pointwise

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 3.17 is a `bridge/view` item in the chapter convex-analysis API. Its owner abstraction
is still the chapter strong-dual finite-sum rule from `Theorem_3_18`; this file keeps only the
real-valued everywhere-finite specialization `subdifferentialAt`, rather than a parallel local
sum-rule API. -/
recall subdifferentialAt
recall is_convex_function_iff_convexOn_toReal
recall
  strongDualSubdifferential_finset_sum_eq_sum_strongDualSubdifferential_of_nonempty_iInter_relativeInterior

-- Proof sketch: specialize the strong-dual finite-sum rule from Theorem 3.18 to the
-- extended-real coercions `y ↦ (f i y : EReal)`. Real-valued convexity gives the no-`⊥`
-- hypothesis and convexity of each coercion, while the effective domain of every summand is all
-- of `E`, so the relative-interior qualification is automatic.
/-- Theorem 3.17: for a finite family of real-valued convex functions on `E`, the subdifferential
at `x` of the pointwise sum is the pointwise sum of the individual subdifferentials at `x`. -/
theorem subdifferentialAt_finset_sum_eq_sum_subdifferentialAt
    {m : ℕ} (f : Fin m → E → ℝ) (x : E)
    (hconvex : ∀ i : Fin m, ConvexOn ℝ Set.univ (f i)) :
    subdifferentialAt (fun y ↦ ∑ i : Fin m, f i y) x =
      ∑ i : Fin m, subdifferentialAt (f i) x := by
  let F : Fin m → E → EReal := fun i y ↦ (f i y : EReal)
  have h_ne_bot : ∀ i : Fin m, ∀ y : E, F i y ≠ ⊥ := by
    intro i y
    simp [F]
  have hconvexF : ∀ i : Fin m, is_convex_function (F i) := by
    intro i
    refine (is_convex_function_iff_convexOn_toReal ?_).2 ?_
    · intro y hy
      simp [F]
    · simpa [F, effective_domain] using hconvex i
  have hqual : (⋂ i : Fin m, intrinsicInterior ℝ (effective_domain (F i))).Nonempty := by
    refine ⟨x, ?_⟩
    simp [F, effective_domain]
  have hsum :
      (fun y ↦ ((∑ i : Fin m, f i y : ℝ) : EReal)) = fun y ↦ ∑ i : Fin m, F i y := by
    funext y
    change Real.toEReal (∑ i : Fin m, f i y) =
      ∑ i : Fin m, Real.toEReal (f i y)
    exact
      map_sum (⟨⟨Real.toEReal, EReal.coe_zero⟩, EReal.coe_add⟩ : ℝ →+ EReal)
        (fun i : Fin m ↦ f i y) Finset.univ
  unfold subdifferentialAt
  rw [hsum]
  simpa [F] using
    strongDualSubdifferential_finset_sum_eq_sum_strongDualSubdifferential_of_nonempty_iInter_relativeInterior
      F x h_ne_bot hconvexF hqual

end
