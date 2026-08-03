import Integer.Chapters.Chap01.section_1_7.ch1_sec1_7_exercise_1_20
import Integer.Chapters.Chap06.section_6_2.ch6_sec6_2_theorem_6_5
import Integer.Chapters.Chap06.section_6_2_2.ch6_sec6_2_2_lattice_free

open scoped BigOperators

-- This example specializes the Section 6.2 corner/intersection-cut owner API from
-- `ch6_sec6_2_theorem_6_5` to split sets, while reusing the chapter's canonical lattice-free
-- owners from Theorem 6.18.

noncomputable section

section Example69

variable {n p k : ℕ}

/-- The split linear form `πx` on `ℝ^p`. -/
def split_linear_form
    (π : Fin p → ℤ)
    (x : Fin p → ℝ) : ℝ :=
  ∑ i : Fin p, (π i : ℝ) * x i

/-- The split linear form `πx` on `ℝ^n`, using only the first `p` coordinates. -/
def split_prefix_linear_form
    (hpn : p ≤ n)
    (π : Fin p → ℤ)
    (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin p, (π i : ℝ) * x (Fin.castLE hpn i)

/-- The strip `K = {x ∈ ℝ^p : π₀ ≤ πx ≤ π₀ + 1}` cut out by an integral split pair
`(π, π₀)`. -/
def split_slab
    (π : Fin p → ℤ)
    (π0 : ℤ) : Set (Fin p → ℝ) :=
  {x | (π0 : ℝ) ≤ split_linear_form π x ∧ split_linear_form π x ≤ (π0 : ℝ) + 1}

/-- Membership in `split_slab π π0` is exactly the displayed double inequality
`π₀ ≤ πx ≤ π₀ + 1`. -/
theorem mem_split_slab_iff
    (π : Fin p → ℤ)
    (π0 : ℤ)
    (x : Fin p → ℝ) :
    x ∈ split_slab π π0 ↔
      (π0 : ℝ) ≤ split_linear_form π x ∧ split_linear_form π x ≤ (π0 : ℝ) + 1 :=
  Iff.rfl

/-- The split set `C = K × ℝ^(n - p)` written directly in `ℝ^n` by using the split inequality on
the first `p` coordinates. -/
def split_set
    (hpn : p ≤ n)
    (π : Fin p → ℤ)
    (π0 : ℤ) : Set (Fin n → ℝ) :=
  {x | (π0 : ℝ) ≤ split_prefix_linear_form hpn π x ∧
      split_prefix_linear_form hpn π x ≤ (π0 : ℝ) + 1}

/-- Membership in `split_set hpn π π0` is exactly the displayed split inequality on the first
`p` coordinates. -/
theorem mem_split_set_iff
    (hpn : p ≤ n)
    (π : Fin p → ℤ)
    (π0 : ℤ)
    (x : Fin n → ℝ) :
    x ∈ split_set hpn π π0 ↔
      (π0 : ℝ) ≤ split_prefix_linear_form hpn π x ∧
        split_prefix_linear_form hpn π x ≤ (π0 : ℝ) + 1 :=
  Iff.rfl

/-- The quantity `ε = π x̄ - π₀` attached to a point `x̄` lying strictly between the two split
hyperplanes. -/
def split_epsilon
    (hpn : p ≤ n)
    (π : Fin p → ℤ)
    (π0 : ℤ)
    (xbar : Fin n → ℝ) : ℝ :=
  split_prefix_linear_form hpn π xbar - (π0 : ℝ)

/-- `split_epsilon hpn π π0 xbar` unfolds to `π x̄ - π₀`. -/
theorem split_epsilon_def
    (hpn : p ≤ n)
    (π : Fin p → ℤ)
    (π0 : ℤ)
    (xbar : Fin n → ℝ) :
    split_epsilon hpn π π0 xbar =
      split_prefix_linear_form hpn π xbar - (π0 : ℝ) :=
  rfl

/-- Example 6.9 (1). The strip
`K = {x ∈ ℝ^p : π₀ ≤ πx ≤ π₀ + 1}` is convex. -/
theorem example_6_9_split_slab_convex
    (π : Fin p → ℤ)
    (π0 : ℤ) :
    Convex ℝ (split_slab π π0) := sorry

/-- Example 6.9 (2). The strip
`K = {x ∈ ℝ^p : π₀ ≤ πx ≤ π₀ + 1}` is `ℤ^p`-free. -/
theorem example_6_9_split_slab_is_lattice_free
    (π : Fin p → ℤ)
    (π0 : ℤ) :
    is_lattice_free (split_slab π π0) := sorry

/-- Example 6.9 (3). If each boundary hyperplane of the strip contains an integral point, then
the strip is maximal lattice-free. In particular, the source's relative-primality hypothesis on
the entries of `π` implies these boundary-point assumptions by Exercise 1.20. -/
theorem example_6_9_split_slab_is_maximal_of_boundary_integer_points
    (π : Fin p → ℤ)
    (π0 : ℤ)
    (hlower : ∃ z : Fin p → ℤ, split_linear_form π (Int.cast ∘ z) = (π0 : ℝ))
    (hupper :
      ∃ z : Fin p → ℤ, split_linear_form π (Int.cast ∘ z) = (π0 : ℝ) + 1) :
    is_maximal_lattice_free (split_slab π π0) := sorry

/-- Example 6.9 (3), source-facing form. If the coefficients of `π` are relatively prime, then
Exercise 1.20 supplies integral points on both boundary hyperplanes, so the split slab is maximal
lattice-free. -/
theorem example_6_9_split_slab_is_maximal_of_coprime_coefficients
    (π : Fin p → ℤ)
    (π0 : ℤ)
    (hcoprime : (Ideal.span (Set.range π) : Ideal ℤ) = ⊤) :
    is_maximal_lattice_free (split_slab π π0) := by
  have hp : 0 < p := by
    cases p with
    | zero =>
        simp at hcoprime
    | succ p =>
        exact Nat.succ_pos p
  refine example_6_9_split_slab_is_maximal_of_boundary_integer_points π π0 ?_ ?_
  · obtain ⟨z, hz⟩ := integer_points_on_coprime_hyperplane hp π hcoprime π0
    refine ⟨z, ?_⟩
    have hz' : split_linear_form π (Int.cast ∘ z) = ((π0 : ℤ) : ℝ) := by
      change ∑ i : Fin p, (π i : ℝ) * (z i : ℝ) = (π0 : ℝ)
      exact_mod_cast hz
    simpa using hz'
  · obtain ⟨z, hz⟩ := integer_points_on_coprime_hyperplane hp π hcoprime (π0 + 1)
    refine ⟨z, ?_⟩
    have hz' : split_linear_form π (Int.cast ∘ z) = ((π0 + 1 : ℤ) : ℝ) := by
      change ∑ i : Fin p, (π i : ℝ) * (z i : ℝ) = ((π0 + 1 : ℤ) : ℝ)
      exact_mod_cast hz
    simpa using hz'

/-- Example 6.9 (4). The split set
`C = {x ∈ ℝ^n : π₀ ≤ ∑_{j=1}^p π_j x_j ≤ π₀ + 1}` is convex. -/
theorem example_6_9_split_set_convex
    (hpn : p ≤ n)
    (π : Fin p → ℤ)
    (π0 : ℤ) :
    Convex ℝ (split_set hpn π π0) := sorry

/-- Example 6.9 (5). The interior of the split set contains no point of
`ℤ^p × ℝ^(n - p)`. -/
theorem example_6_9_split_set_interior_disjoint_mixed_integer_prefix_lattice
    (hpn : p ≤ n)
    (π : Fin p → ℤ)
    (π0 : ℤ) :
    Disjoint (interior (split_set hpn π π0)) (mixed_integer_prefix_lattice hpn) := sorry

/-- Canonical bridge form of Example 6.9 (5): the split set is free of
`mixed_integer_prefix_lattice hpn`. -/
theorem split_set_is_free_of_mixed_integer_prefix_lattice
    (hpn : p ≤ n)
    (π : Fin p → ℤ)
    (π0 : ℤ) :
    is_free_of (mixed_integer_prefix_lattice hpn) (split_set hpn π π0) := by
  simpa [is_free_of] using
    example_6_9_split_set_interior_disjoint_mixed_integer_prefix_lattice hpn π π0

/-- Example 6.9 (6). If one of the first `p` coordinates of `x̄` is nonintegral, then there is a
split pair `(π, π₀)` for which `x̄` lies strictly between the two split hyperplanes. -/
theorem example_6_9_exists_split_around_fractional_prefix_coordinate
    (hpn : p ≤ n)
    (xbar : Fin n → ℝ)
    (hfrac :
      ∃ i : Fin p, xbar (Fin.castLE hpn i) ∉ Set.range (Int.cast : ℤ → ℝ)) :
    ∃ π : Fin p → ℤ, ∃ π0 : ℤ,
      (π0 : ℝ) < split_prefix_linear_form hpn π xbar ∧
        split_prefix_linear_form hpn π xbar < (π0 : ℝ) + 1 := sorry

/-- Example 6.9 (7). If `x̄` lies strictly between the two split hyperplanes, then it belongs to
the interior of the split set. -/
theorem example_6_9_point_between_split_hyperplanes_mem_interior
    (hpn : p ≤ n)
    (π : Fin p → ℤ)
    (π0 : ℤ)
    (xbar : Fin n → ℝ)
    (hinside :
      (π0 : ℝ) < split_prefix_linear_form hpn π xbar ∧
        split_prefix_linear_form hpn π xbar < (π0 : ℝ) + 1) :
    xbar ∈ interior (split_set hpn π π0) := sorry

/-- Example 6.9 (8). With `ε = π x̄ - π₀`, the strict split inequalities imply `0 < ε < 1`. -/
theorem example_6_9_split_epsilon_mem_Ioo
    (hpn : p ≤ n)
    (π : Fin p → ℤ)
    (π0 : ℤ)
    (xbar : Fin n → ℝ)
    (hinside :
      (π0 : ℝ) < split_prefix_linear_form hpn π xbar ∧
        split_prefix_linear_form hpn π xbar < (π0 : ℝ) + 1) :
    split_epsilon hpn π π0 xbar ∈ Set.Ioo (0 : ℝ) 1 := sorry

/-- Example 6.9 (9). For a point `x̄` in the interior of the split set, the ray-intersection
parameter `α_j` has the explicit split formula
`-ε / (π r̄^j)` when `π r̄^j < 0`, `(1 - ε) / (π r̄^j)` when `π r̄^j > 0`, and `∞`
otherwise. -/
theorem example_6_9_split_ray_parameter_eq_piecewise
    (hpn : p ≤ n)
    (π : Fin p → ℤ)
    (π0 : ℤ)
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (hε : split_epsilon hpn π π0 xbar ∈ Set.Ioo (0 : ℝ) 1)
    (j : Fin k) :
    IntersectionCut.ray_intersection_parameter (split_set hpn π π0) xbar rays j =
      if hneg : split_prefix_linear_form hpn π (rays j) < 0 then
        ENNReal.ofReal
          ((-split_epsilon hpn π π0 xbar) / split_prefix_linear_form hpn π (rays j))
      else if hpos : 0 < split_prefix_linear_form hpn π (rays j) then
        ENNReal.ofReal
          ((1 - split_epsilon hpn π π0 xbar) / split_prefix_linear_form hpn π (rays j))
      else
        ⊤ := sorry

/-- Example 6.9 (10). If the `j`th ray is not parallel to the split hyperplanes, then `α_j` is
the largest nonnegative parameter `α` for which the half-line `x̄ + α r̄^j` stays in the split
set. -/
theorem example_6_9_split_ray_parameter_is_greatest_of_nonparallel
    (hpn : p ≤ n)
    (π : Fin p → ℤ)
    (π0 : ℤ)
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (hε : split_epsilon hpn π π0 xbar ∈ Set.Ioo (0 : ℝ) 1)
    (j : Fin k)
    (hj : split_prefix_linear_form hpn π (rays j) ≠ 0) :
    IsGreatest
      {α : ℝ | 0 ≤ α ∧ xbar + α • rays j ∈ split_set hpn π π0}
      (IntersectionCut.ray_intersection_parameter (split_set hpn π π0) xbar rays j).toReal := sorry

/-- Example 6.9 (11). If the `j`th ray is parallel to the split hyperplanes, then `α_j = +∞`. -/
theorem example_6_9_split_ray_parameter_eq_top_of_parallel
    (hpn : p ≤ n)
    (π : Fin p → ℤ)
    (π0 : ℤ)
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (hε : split_epsilon hpn π π0 xbar ∈ Set.Ioo (0 : ℝ) 1)
    (j : Fin k)
    (hparallel : split_prefix_linear_form hpn π (rays j) = 0) :
    IntersectionCut.ray_intersection_parameter (split_set hpn π π0) xbar rays j = ⊤ := sorry

/-- Example 6.9 (12). The Section 6.2 intersection cut specialized to the split set is the
inequality `∑_{j ∈ N} x_j / α_j ≥ 1`, where `α_j` is the split ray-intersection parameter of
`split_set hpn π π0`. -/
theorem example_6_9_mem_split_intersection_cut_iff
    (hpn : p ≤ n)
    (π : Fin p → ℤ)
    (π0 : ℤ)
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (x : Fin k → ℝ) :
    1 ≤ IntersectionCut.intersection_cut_coeff (split_set hpn π π0) xbar rays ⬝ᵥ x ↔
      1 ≤ ∑ j : Fin k,
        x j /
          (IntersectionCut.ray_intersection_parameter
            (split_set hpn π π0) xbar rays j).toReal := sorry

end Example69
