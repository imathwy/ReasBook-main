import BauschkeLean.Chap20.Definition_20_20
import BauschkeLean.Chap26.Problem_26_28
import BauschkeLean.Chap26.Proposition_26_33

open Filter
open ERealFunction
open scoped InnerProductSpace Pointwise SetValuedOperator Topology

universe u v

namespace SetValuedOperator

noncomputable section

-- Semantic recall/local precedent: `lean_leansearch` did not surface a composite-inclusion
-- Douglas--Rachford owner, so this item follows the verified Chapter 26 owners
-- `composite_primal_inclusion_solution_set`, `composite_dual_inclusion_solution_set`,
-- `composite_kuhn_tucker_points`, `resolventMap`, and `toWeakSpace`; the source operator
-- `Q = (Id + L^* L)⁻¹` is realized by the canonical inverse `(1 + L.adjoint.comp L).inverse`.

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- An orbit `x`, `y`, `u`, `v`, `p`, `q`, `s`, `t` satisfies the composite Douglas--Rachford
recursion `(26.108)` from Proposition 26.38, where the source operator
`Q = (Id + L^* L)⁻¹` is realized by `(1 + L.adjoint.comp L).inverse`. -/
structure IsCompositeDouglasRachfordOrbit
    (z : H) (A : SetValuedOperator H H) (r : K) (B : SetValuedOperator K K)
    (L : H →L[ℝ] K) (γ : PosReal) (lam : ℕ → ℝ) (s0 : H) (t0 : K)
    (x : ℕ → H) (y : ℕ → K) (u : ℕ → H) (v : ℕ → K) (p : ℕ → H) (q : ℕ → K)
    (s : ℕ → H) (t : ℕ → K) : Prop where
  /-- The `s`-sequence starts from the prescribed initial point `s₀`. -/
  s_zero : s 0 = s0
  /-- The `t`-sequence starts from the prescribed initial point `t₀`. -/
  t_zero : t 0 = t0
  /-- The primal resolvent step is `xₙ ∈ J_{γ A}(sₙ + γ z)`. -/
  x_mem : ∀ n : ℕ, x n ∈ J[((γ : ℝ) • A)] (s n + (γ : ℝ) • z)
  /-- The translated codomain resolvent step is `yₙ ∈ r + J_{γ B}(tₙ - r)`. -/
  y_mem : ∀ n : ℕ, y n ∈ ({r} : Set K) + J[((γ : ℝ) • B)] (t n - r)
  /-- The primal residual is `uₙ = γ⁻¹ (sₙ - xₙ)`. -/
  u_eq : ∀ n : ℕ, u n = ((γ : ℝ)⁻¹ : ℝ) • (s n - x n)
  /-- The dual residual is `vₙ = γ⁻¹ (tₙ - yₙ)`. -/
  v_eq : ∀ n : ℕ, v n = ((γ : ℝ)⁻¹ : ℝ) • (t n - y n)
  /-- The graph-projection primal step is
  `pₙ = Q(2 xₙ - sₙ + L^*(2 yₙ - tₙ))`
  with `Q = (Id + L^* L)⁻¹`. -/
  p_eq :
      ∀ n : ℕ,
        p n =
          (1 + L.adjoint.comp L).inverse
            ((2 : ℝ) • x n - s n + L.adjoint ((2 : ℝ) • y n - t n))
  /-- The graph-projection codomain step is `qₙ = L pₙ`. -/
  q_eq : ∀ n : ℕ, q n = L (p n)
  /-- The relaxed primal update is `sₙ₊₁ = sₙ + λₙ (pₙ - xₙ)`. -/
  s_succ_eq : ∀ n : ℕ, s (n + 1) = s n + lam n • (p n - x n)
  /-- The relaxed codomain update is `tₙ₊₁ = tₙ + λₙ (qₙ - yₙ)`. -/
  t_succ_eq : ∀ n : ℕ, t (n + 1) = t n + lam n • (q n - y n)

/-- Companion bridge for Proposition 26.38: the source recursion `(26.108)` is the coordinate
form of a product-space Douglas--Rachford orbit, so the primal and dual residual sequences
converge weakly to a Kuhn--Tucker pair for the composite inclusion problem. -/
theorem compositeDouglasRachford_primal_dual_tendsto_weakly_to_composite_kuhn_tucker_point
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
    (hOrbit : IsCompositeDouglasRachfordOrbit z A r B L γ lam s0 t0 x y u v p q s t) :
    ∃ xbar vbar,
      (xbar, vbar) ∈ composite_kuhn_tucker_points z A r B L ∧
      Tendsto (fun n ↦ toWeakSpace ℝ H (x n)) atTop (𝓝 (toWeakSpace ℝ H xbar)) ∧
      Tendsto (fun n ↦ toWeakSpace ℝ K (v n)) atTop (𝓝 (toWeakSpace ℝ K vbar)) := sorry

/-- Proposition 26.38 (1): in the composite inclusion setting of Problem 26.28, assume `A` and
`B` are maximally monotone, the primal solution set is nonempty, and the relaxation parameters
`λₙ` satisfy the Douglas--Rachford hypotheses from Theorem 26.11. Then every orbit satisfying the
source recursion `(26.108)` has its primal sequence `xₙ` converging weakly to a point of
`composite_primal_inclusion_solution_set z A r B L`. -/
theorem compositeDouglasRachford_primal_tendsto_weakly_to_composite_primal_solution
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
    (hOrbit : IsCompositeDouglasRachfordOrbit z A r B L γ lam s0 t0 x y u v p q s t) :
    ∃ xbar ∈ composite_primal_inclusion_solution_set z A r B L,
      Tendsto (fun n ↦ toWeakSpace ℝ H (x n)) atTop (𝓝 (toWeakSpace ℝ H xbar)) := by
  obtain ⟨xbar, vbar, hkt, hx, hv⟩ :=
    compositeDouglasRachford_primal_dual_tendsto_weakly_to_composite_kuhn_tucker_point
      z A r B L hA hB hP lam hlam hdiv γ s0 t0 hOrbit
  have hsol :
      (xbar, vbar) ∈
        composite_primal_inclusion_solution_set z A r B L ×ˢ
          composite_dual_inclusion_solution_set z A r B L :=
    composite_kuhn_tucker_points_subset_product_solution_sets z A r B L hkt
  exact ⟨xbar, hsol.1, hx⟩

/-- Proposition 26.38 (2): under the same assumptions and recursion `(26.108)`, the dual
residual sequence `vₙ` converges weakly to a point of
`composite_dual_inclusion_solution_set z A r B L`. -/
theorem compositeDouglasRachford_dual_tendsto_weakly_to_composite_dual_solution
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
    (hOrbit : IsCompositeDouglasRachfordOrbit z A r B L γ lam s0 t0 x y u v p q s t) :
    ∃ vbar ∈ composite_dual_inclusion_solution_set z A r B L,
      Tendsto (fun n ↦ toWeakSpace ℝ K (v n)) atTop (𝓝 (toWeakSpace ℝ K vbar)) := by
  obtain ⟨xbar, vbar, hkt, hx, hv⟩ :=
    compositeDouglasRachford_primal_dual_tendsto_weakly_to_composite_kuhn_tucker_point
      z A r B L hA hB hP lam hlam hdiv γ s0 t0 hOrbit
  have hsol :
      (xbar, vbar) ∈
        composite_primal_inclusion_solution_set z A r B L ×ˢ
          composite_dual_inclusion_solution_set z A r B L :=
    composite_kuhn_tucker_points_subset_product_solution_sets z A r B L hkt
  exact ⟨vbar, hsol.2, hv⟩

end

end SetValuedOperator
