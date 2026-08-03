import Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_1
import Integer.Chapters.Chap07.section_7_7.ch7_sec7_7_exercise_7_19
import Integer.Chapters.Chap10.section_10_3.ch10_sec10_3_1_lemma_10_7

-- Declarations for this item will be appended below by the statement pipeline.

-- This exercise reuses the Chapter 7 stable-set and odd-cycle owners
-- `stableSetIndicator`, `is_valid_inequality`, `CycleSupport`, `odd_cycle_inequality_rhs`, and
-- `fractional_stable_set_polytope`, while keeping the source-facing cone owner on arbitrary
-- vertex types and bridging the `Fin n` specialization to the canonical Section 10.3 owner
-- `N(FRAC(G))`.

open scoped LovaszSchrijverNotation

section Exercise_10_14

variable {V : Type}
variable (G : SimpleGraph V)

/-- The homogenized cone over `FRAC(G)` consists of the vectors `(x₀, x)` with
`0 ≤ x_v ≤ x₀` for every vertex and `x_u + x_v ≤ x₀` on every graph edge. -/
def fractional_stable_set_cone : Set (Option V → ℝ) :=
  {z |
    0 ≤ z none ∧
      (∀ v : V, 0 ≤ z (some v) ∧ z (some v) ≤ z none) ∧
        ∀ ⦃u v : V⦄, G.Adj u v → z (some u) + z (some v) ≤ z none}

/-- Membership in `fractional_stable_set_cone G` is exactly the homogenized
`FRAC(G)` inequality system. -/
theorem mem_fractional_stable_set_cone_iff
    (z : Option V → ℝ) :
    z ∈ fractional_stable_set_cone G ↔
      0 ≤ z none ∧
        (∀ v : V, 0 ≤ z (some v) ∧ z (some v) ≤ z none) ∧
          ∀ ⦃u v : V⦄, G.Adj u v → z (some u) + z (some v) ≤ z none :=
  Iff.rfl

/-- A point of `FRAC(G)` gives the normalized homogenized vector `(1, x)` in
`fractional_stable_set_cone G`. -/
theorem homogenized_point_mem_fractional_stable_set_cone
    {x : V → ℝ}
    (hx : x ∈ FRAC(G)) :
    (fun i ↦ match i with
      | none => 1
      | some v => x v) ∈ fractional_stable_set_cone G := by
  rw [mem_fractional_stable_set_polytope_iff] at hx
  rcases hx with ⟨hx_box, hx_edge⟩
  rw [mem_fractional_stable_set_cone_iff]
  refine ⟨zero_le_one, ?_⟩
  refine ⟨?_, ?_⟩
  · intro v
    simpa using hx_box v
  · intro u v huv
    simpa using hx_edge huv

/-- A normalized point of `fractional_stable_set_cone G` dehomogenizes to a point of `FRAC(G)`.
-/
theorem mem_fractional_stable_set_polytope_of_mem_fractional_stable_set_cone
    {z : Option V → ℝ}
    (hz : z ∈ fractional_stable_set_cone G)
    (hz₀ : z none = 1) :
    (fun v ↦ z (some v)) ∈ FRAC(G) := by
  rw [mem_fractional_stable_set_cone_iff] at hz
  rcases hz with ⟨-, hz_box, hz_edge⟩
  rw [mem_fractional_stable_set_polytope_iff]
  refine ⟨?_, ?_⟩
  · intro v
    exact ⟨(hz_box v).1, by simpa [hz₀] using (hz_box v).2⟩
  · intro u v huv
    simpa [hz₀] using hz_edge huv

/-- The Lovász-Schrijver relaxation `N(FRAC(G))` consists of the vectors `x : V → ℝ` for which
there exists a symmetric matrix `Y` indexed by `Option V` with `Y none none = 1`,
`Y e₀ = diag(Y)`, and whose `v`-columns `Y e_v` together with the difference columns
`Y (e₀ - e_v)` all lie in the homogenized cone over `FRAC(G)`. -/
def lovasz_schrijver_n_frac_relaxation : Set (V → ℝ) :=
  {x | ∃ Y : Matrix (Option V) (Option V) ℝ,
      Y.IsSymm ∧
      Y none none = 1 ∧
      (∀ i : Option V, Y i none = Y i i) ∧
      (∀ v : V, (fun i : Option V ↦ Y i (some v)) ∈ fractional_stable_set_cone G) ∧
      (∀ v : V, (fun i : Option V ↦ Y i none - Y i (some v)) ∈ fractional_stable_set_cone G) ∧
      ∀ v : V, x v = Y (some v) none}

/-- Membership in `lovasz_schrijver_n_frac_relaxation G` is exactly the existence of a symmetric
matrix witness with the diagonal/first-column relation and the cone constraints defining
`N(FRAC(G))`. -/
theorem mem_lovasz_schrijver_n_frac_relaxation_iff
    (x : V → ℝ) :
    x ∈ lovasz_schrijver_n_frac_relaxation G ↔
      ∃ Y : Matrix (Option V) (Option V) ℝ,
        Y.IsSymm ∧
        Y none none = 1 ∧
        (∀ i : Option V, Y i none = Y i i) ∧
        (∀ v : V, (fun i : Option V ↦ Y i (some v)) ∈ fractional_stable_set_cone G) ∧
        (∀ v : V, (fun i : Option V ↦ Y i none - Y i (some v)) ∈ fractional_stable_set_cone G) ∧
        ∀ v : V, x v = Y (some v) none :=
  Iff.rfl

/-- For graphs already presented on `Fin n`, the source-facing `Option`-indexed definition of
`N(FRAC(G))` agrees with the canonical Section 10.3 Lovász-Schrijver owner. -/
theorem lovasz_schrijver_n_frac_relaxation_eq_lovasz_schrijver_N
    {n : ℕ} (G : SimpleGraph (Fin n)) :
    lovasz_schrijver_n_frac_relaxation G = N(FRAC(G)) := by
  sorry

/-- For graphs on `Fin n`, membership in the local source-facing `Option`-indexed owner is exactly
membership in the canonical Section 10.3 relaxation `N(FRAC(G))`. -/
theorem mem_lovasz_schrijver_n_frac_relaxation_iff_mem_lovasz_schrijver_N
    {n : ℕ} (G : SimpleGraph (Fin n)) {x : Fin n → ℝ} :
    x ∈ lovasz_schrijver_n_frac_relaxation G ↔ x ∈ N(FRAC(G)) := by
  rw [lovasz_schrijver_n_frac_relaxation_eq_lovasz_schrijver_N G]

section Validity

variable [Fintype V]

/-- Exercise 10.14. If `C` is an odd cycle support contained in `G`, then the odd-cycle
inequality `∑_{j ∈ V(C)} x_j ≤ (|C| - 1) / 2` is valid for `N(FRAC(G))`. -/
theorem odd_cycle_inequality_valid_for_lovasz_schrijver_n_frac
    (C : CycleSupport V)
    (hC : C.IsContainedIn G)
    (hodd : Odd C.length) :
    is_valid_inequality
      (lovasz_schrijver_n_frac_relaxation G)
      (stableSetIndicator C.vertexFinset)
      (odd_cycle_inequality_rhs C) := sorry

/-- For graphs on `Fin n`, Exercise 10.14 can be stated directly on the canonical Section 10.3
Lovász-Schrijver relaxation `N(FRAC(G))`. -/
theorem odd_cycle_inequality_valid_for_lovasz_schrijver_N_frac
    {n : ℕ} (G : SimpleGraph (Fin n))
    (C : CycleSupport (Fin n))
    (hC : C.IsContainedIn G)
    (hodd : Odd C.length) :
    is_valid_inequality
      (N(FRAC(G)))
      (stableSetIndicator C.vertexFinset)
      (odd_cycle_inequality_rhs C) := by
  simpa [lovasz_schrijver_n_frac_relaxation_eq_lovasz_schrijver_N G] using
    odd_cycle_inequality_valid_for_lovasz_schrijver_n_frac G C hC hodd

end Validity

end Exercise_10_14
