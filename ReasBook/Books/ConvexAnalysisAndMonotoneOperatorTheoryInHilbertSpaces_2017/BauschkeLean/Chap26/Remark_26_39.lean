import BauschkeLean.Chap26.Proposition_26_38
import BauschkeLean.Chap29.Example_29_19

open Filter
open ContinuousLinearMap
open ERealFunction
open scoped InnerProductSpace Pointwise SetValuedOperator Topology

noncomputable section

universe u v

namespace SetValuedOperator

-- Semantic recall/local precedent: `lean_leansearch` only surfaced generic orthogonal-projection
-- owners, so this remark is formalized through the verified local graph-projection theorem
-- `starProjection_graph_eq_sub_adjoint_inverse_one_add_comp_adjoint` from Example 29.19 together
-- with the Chapter 26 orbit owner `IsCompositeDouglasRachfordOrbit`.

section

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- The explicit correction operator `R = L^* (Id + L L^*)⁻¹` used in Remark 26.39. -/
def composite_douglas_rachford_graph_correction (L : H →L[ℝ] K) : K →L[ℝ] H :=
  L.adjoint.comp (1 + L.comp L.adjoint).inverse

/-- Remark 26.39 (1): the graph-projection formula from Example 29.19 can be rewritten in the
source form `(x, y) ↦ (x - R (L x - y), L (x - R (L x - y)))`, where
`R = L^* (Id + L L^*)⁻¹`. -/
theorem graph_projection_formula_eq_graph_correction_formula
    (L : H →L[ℝ] K) (x : H) (y : K) :
    (x - L.adjoint ((1 + L.comp L.adjoint).inverse (L x - y)),
      y + (1 + L.comp L.adjoint).inverse (L x - y)) =
      (x - composite_douglas_rachford_graph_correction L (L x - y),
        L (x - composite_douglas_rachford_graph_correction L (L x - y))) := sorry

/-- The Proposition 26.38 graph-projection primal update equals the explicit `R`-update from
Remark 26.39. -/
theorem inverse_one_add_adjoint_comp_eq_sub_graph_correction
    (L : H →L[ℝ] K) (x : H) (y : K) :
    (1 + L.adjoint.comp L).inverse (x + L.adjoint y) =
      x - composite_douglas_rachford_graph_correction L (L x - y) := sorry

/-- The explicit recursion `(26.113)` from Remark 26.39 determines a canonical
`IsCompositeDouglasRachfordOrbit` for Proposition 26.38. -/
theorem isCompositeDouglasRachfordOrbit_of_graph_correction
    (z : H) (A : SetValuedOperator H H) (r : K) (B : SetValuedOperator K K)
    (L : H →L[ℝ] K) (γ : PosReal) (lam : ℕ → ℝ) (s0 : H) (t0 : K)
    {x : ℕ → H} {y : ℕ → K} {u : ℕ → H} {v : ℕ → K} {p : ℕ → H} {q : ℕ → K}
    {s : ℕ → H} {t : ℕ → K}
    (s_zero : s 0 = s0)
    (t_zero : t 0 = t0)
    (x_mem : ∀ n : ℕ, x n ∈ J[((γ : ℝ) • A)] (s n + (γ : ℝ) • z))
    (y_mem : ∀ n : ℕ, y n ∈ ({r} : Set K) + J[((γ : ℝ) • B)] (t n - r))
    (u_eq : ∀ n : ℕ, u n = ((γ : ℝ)⁻¹ : ℝ) • (s n - x n))
    (v_eq : ∀ n : ℕ, v n = ((γ : ℝ)⁻¹ : ℝ) • (t n - y n))
    (p_eq_sub_graph_correction :
      ∀ n : ℕ,
        p n =
          (2 : ℝ) • x n - s n -
            composite_douglas_rachford_graph_correction L
              (L ((2 : ℝ) • x n - s n) - (2 : ℝ) • y n + t n))
    (q_eq : ∀ n : ℕ, q n = L (p n))
    (s_succ_eq : ∀ n : ℕ, s (n + 1) = s n + lam n • (p n - x n))
    (t_succ_eq : ∀ n : ℕ, t (n + 1) = t n + lam n • (q n - y n)) :
    IsCompositeDouglasRachfordOrbit z A r B L γ lam s0 t0 x y u v p q s t := by
  refine
    ⟨s_zero, t_zero, x_mem, y_mem, u_eq, v_eq, ?_, q_eq, s_succ_eq, t_succ_eq⟩
  intro n
  rw [inverse_one_add_adjoint_comp_eq_sub_graph_correction]
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using p_eq_sub_graph_correction n

namespace IsCompositeDouglasRachfordOrbit

variable
    {z : H} {A : SetValuedOperator H H} {r : K} {B : SetValuedOperator K K}
    {L : H →L[ℝ] K} {γ : PosReal} {lam : ℕ → ℝ} {s0 : H} {t0 : K}
    {x : ℕ → H} {y : ℕ → K} {u : ℕ → H} {v : ℕ → K} {p : ℕ → H} {q : ℕ → K}
    {s : ℕ → H} {t : ℕ → K}

/-- The Proposition 26.38 orbit step is exactly the explicit correction rule `(26.113)` from
Remark 26.39, with `R = L^* (Id + L L^*)⁻¹`. -/
theorem p_eq_sub_graph_correction
    (hOrbit : IsCompositeDouglasRachfordOrbit z A r B L γ lam s0 t0 x y u v p q s t)
    (n : ℕ) :
    p n =
      (2 : ℝ) • x n - s n -
        composite_douglas_rachford_graph_correction L
          (L ((2 : ℝ) • x n - s n) - (2 : ℝ) • y n + t n) := sorry

end IsCompositeDouglasRachfordOrbit

/-- Remark 26.39 (2): the primal weak-convergence conclusion of Proposition 26.38 still holds
when the public recursion is written in the replacement form `(26.113)`. -/
theorem compositeDouglasRachford_primal_tendsto_weakly_of_graph_correction
    (z : H) (A : SetValuedOperator H H) (r : K) (B : SetValuedOperator K K)
    (L : H →L[ℝ] K) (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hP : (composite_primal_inclusion_solution_set z A r B L).Nonempty)
    (lam : ℕ → ℝ) (hlam : ∀ n, lam n ∈ Set.Icc (0 : ℝ) 2)
    (hdiv :
      Tendsto
        (fun N ↦
          Finset.sum (Finset.range N)
            (fun n ↦ lam n * (2 - lam n)))
        atTop atTop)
    (γ : PosReal) (s0 : H) (t0 : K)
    {x : ℕ → H} {y : ℕ → K} {u : ℕ → H} {v : ℕ → K} {p : ℕ → H} {q : ℕ → K}
    {s : ℕ → H} {t : ℕ → K}
    (s_zero : s 0 = s0)
    (t_zero : t 0 = t0)
    (x_mem : ∀ n : ℕ, x n ∈ J[((γ : ℝ) • A)] (s n + (γ : ℝ) • z))
    (y_mem : ∀ n : ℕ, y n ∈ ({r} : Set K) + J[((γ : ℝ) • B)] (t n - r))
    (u_eq : ∀ n : ℕ, u n = ((γ : ℝ)⁻¹ : ℝ) • (s n - x n))
    (v_eq : ∀ n : ℕ, v n = ((γ : ℝ)⁻¹ : ℝ) • (t n - y n))
    (p_eq_sub_graph_correction :
      ∀ n : ℕ,
        p n =
          (2 : ℝ) • x n - s n -
            composite_douglas_rachford_graph_correction L
              (L ((2 : ℝ) • x n - s n) - (2 : ℝ) • y n + t n))
    (q_eq : ∀ n : ℕ, q n = L (p n))
    (s_succ_eq : ∀ n : ℕ, s (n + 1) = s n + lam n • (p n - x n))
    (t_succ_eq : ∀ n : ℕ, t (n + 1) = t n + lam n • (q n - y n)) :
    ∃ xbar ∈ composite_primal_inclusion_solution_set z A r B L,
      Tendsto (fun n ↦ toWeakSpace ℝ H (x n)) atTop (𝓝 (toWeakSpace ℝ H xbar)) := by
  have hOrbit : IsCompositeDouglasRachfordOrbit z A r B L γ lam s0 t0 x y u v p q s t :=
    isCompositeDouglasRachfordOrbit_of_graph_correction
      z A r B L γ lam s0 t0 s_zero t_zero x_mem y_mem u_eq v_eq
      p_eq_sub_graph_correction q_eq s_succ_eq t_succ_eq
  exact
    compositeDouglasRachford_primal_tendsto_weakly_to_composite_primal_solution
      z A r B L hA hB hP lam hlam hdiv γ s0 t0 hOrbit

/-- Remark 26.39 (3): the dual weak-convergence conclusion of Proposition 26.38 also remains
valid when the recursion is written in the replacement form `(26.113)`. -/
theorem compositeDouglasRachford_dual_tendsto_weakly_of_graph_correction
    (z : H) (A : SetValuedOperator H H) (r : K) (B : SetValuedOperator K K)
    (L : H →L[ℝ] K) (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hP : (composite_primal_inclusion_solution_set z A r B L).Nonempty)
    (lam : ℕ → ℝ) (hlam : ∀ n, lam n ∈ Set.Icc (0 : ℝ) 2)
    (hdiv :
      Tendsto
        (fun N ↦
          Finset.sum (Finset.range N)
            (fun n ↦ lam n * (2 - lam n)))
        atTop atTop)
    (γ : PosReal) (s0 : H) (t0 : K)
    {x : ℕ → H} {y : ℕ → K} {u : ℕ → H} {v : ℕ → K} {p : ℕ → H} {q : ℕ → K}
    {s : ℕ → H} {t : ℕ → K}
    (s_zero : s 0 = s0)
    (t_zero : t 0 = t0)
    (x_mem : ∀ n : ℕ, x n ∈ J[((γ : ℝ) • A)] (s n + (γ : ℝ) • z))
    (y_mem : ∀ n : ℕ, y n ∈ ({r} : Set K) + J[((γ : ℝ) • B)] (t n - r))
    (u_eq : ∀ n : ℕ, u n = ((γ : ℝ)⁻¹ : ℝ) • (s n - x n))
    (v_eq : ∀ n : ℕ, v n = ((γ : ℝ)⁻¹ : ℝ) • (t n - y n))
    (p_eq_sub_graph_correction :
      ∀ n : ℕ,
        p n =
          (2 : ℝ) • x n - s n -
            composite_douglas_rachford_graph_correction L
              (L ((2 : ℝ) • x n - s n) - (2 : ℝ) • y n + t n))
    (q_eq : ∀ n : ℕ, q n = L (p n))
    (s_succ_eq : ∀ n : ℕ, s (n + 1) = s n + lam n • (p n - x n))
    (t_succ_eq : ∀ n : ℕ, t (n + 1) = t n + lam n • (q n - y n)) :
    ∃ vbar ∈ composite_dual_inclusion_solution_set z A r B L,
      Tendsto (fun n ↦ toWeakSpace ℝ K (v n)) atTop (𝓝 (toWeakSpace ℝ K vbar)) := by
  have hOrbit : IsCompositeDouglasRachfordOrbit z A r B L γ lam s0 t0 x y u v p q s t :=
    isCompositeDouglasRachfordOrbit_of_graph_correction
      z A r B L γ lam s0 t0 s_zero t_zero x_mem y_mem u_eq v_eq
      p_eq_sub_graph_correction q_eq s_succ_eq t_succ_eq
  exact
    compositeDouglasRachford_dual_tendsto_weakly_to_composite_dual_solution
      z A r B L hA hB hP lam hlam hdiv γ s0 t0 hOrbit

end

end SetValuedOperator
