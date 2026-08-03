import Integer.Chapters.Chap07.section_7_4.ch7_sec7_4_theorem_7_18
import Integer.Chapters.Chap08.section_8_2.ch8_sec8_2_theorem_8_2

open scoped BigOperators

-- Declarations for this item will be appended below by the statement pipeline.

section Remark813

variable {α : Type*} [Fintype α]

/-- The binary master coefficients are the `0`-`1` multipliers whose total mass is `1`. -/
def binary_master_weights (lam : α → ℝ) : Prop :=
  (∑ a, lam a) = 1 ∧ ∀ a, lam a = 0 ∨ lam a = 1

/-- `binary_master_weights lam` unfolds to the convexity equation together with the `0`-`1`
restriction on every multiplier. -/
theorem binary_master_weights_iff {lam : α → ℝ} :
    binary_master_weights lam ↔
      (∑ a, lam a) = 1 ∧ ∀ a, lam a = 0 ∨ lam a = 1 :=
  Iff.rfl

/-- A family of binary master coefficients has a unique active multiplier. -/
theorem existsUnique_eq_one_of_binary_master_weights {lam : α → ℝ}
    (hbin : binary_master_weights lam) :
    ∃! a, lam a = 1 := by
  sorry

/-- Binary master weights are Dantzig-Wolfe coefficients once all ray variables vanish. -/
theorem dantzig_wolfe_coefficients_of_binary_master_weights
    {K H : ℕ} {lam : Fin K → ℝ} {mu : Fin H → ℝ}
    (hbin : binary_master_weights lam)
    (hmu : ∀ h, mu h = 0) :
    dantzig_wolfe_coefficients lam mu := by
  rcases hbin with ⟨hsum, h01⟩
  refine ⟨hsum, ?_, ?_⟩
  · intro k
    rcases h01 k with hzero | hone <;> linarith
  · intro h
    simp [hmu h]

/-- With binary master coefficients, the projected point is exactly one of the listed generators. -/
theorem sum_smul_eq_generator_of_binary_master_weights
    {β : Type*} [AddCommMonoid β] [Module ℝ β]
    (v : α → β) {lam : α → ℝ}
    (hbin : binary_master_weights lam) :
    ∃ a, (∑ b, lam b • v b) = v a := by
  sorry

variable {p K H : ℕ}

/-- Remark 8.13 (1). In the pure-integer case, if the Dantzig-Wolfe ray variables vanish and the
master multipliers are binary, then the projected point is one of the original generators. -/
theorem dantzig_wolfe_point_eq_generator_of_binary_master_weights
    (v : Fin K → Fin p → ℝ)
    (r : Fin H → Fin p → ℝ)
    {lam : Fin K → ℝ}
    {mu : Fin H → ℝ}
    (hbin : binary_master_weights lam)
    (hmu : ∀ h, mu h = 0) :
    ∃ k, dantzig_wolfe_point v r lam mu = v k := by
  sorry

/-- The projection of the traveling-salesman binary master is the set of Hamiltonian-tour
incidence vectors. -/
def traveling_salesman_binary_master_projection (n : ℕ) :
    Set (complete_graph_edges n → ℝ) :=
  {x |
    ∃ lam : Equiv.Perm (Fin n) → ℝ,
      binary_master_weights lam ∧
        x = ∑ σ, lam σ • hamiltonian_tour_incidence_vector σ}

/-- Membership in `traveling_salesman_binary_master_projection n` is exactly the existence of a
binary multiplier family summing to `1` whose weighted sum equals `x`. -/
theorem mem_traveling_salesman_binary_master_projection_iff
    {n : ℕ} {x : complete_graph_edges n → ℝ} :
    x ∈ traveling_salesman_binary_master_projection n ↔
      ∃ lam : Equiv.Perm (Fin n) → ℝ,
        binary_master_weights lam ∧
          x = ∑ σ, lam σ • hamiltonian_tour_incidence_vector σ :=
  Iff.rfl

/-- Remark 8.13 (2). Replacing the traveling-salesman master multipliers by binary variables makes
the projection equal to the set of Hamiltonian-tour incidence vectors. -/
theorem traveling_salesman_binary_master_projection_eq_tour_range
    (n : ℕ) :
    traveling_salesman_binary_master_projection n =
      Set.range (fun σ : Equiv.Perm (Fin n) ↦ hamiltonian_tour_incidence_vector σ) := by
  sorry

/-- The convex hull of the traveling-salesman binary master projection is the traveling salesman
polytope. -/
theorem convexHull_traveling_salesman_binary_master_projection_eq_travelingSalesmanPolytope
    (n : ℕ) :
    convexHull ℝ (traveling_salesman_binary_master_projection n) =
      travelingSalesmanPolytope n := by
  rw [traveling_salesman_binary_master_projection_eq_tour_range,
    travelingSalesmanPolytope_eq_convexHull]

end Remark813
