import BauschkeLean.Chap22.Definition_22_1
import BauschkeLean.Chap23.Corollary_23_11
import BauschkeLean.Chap26.Proposition_26_1

open Filter
open ERealFunction
open scoped InnerProductSpace Pointwise Set SetValuedOperator Topology

universe u

namespace SetValuedOperator

-- Semantic recall note: `lean_leansearch` did not surface a monotone-operator owner for the
-- Peaceman--Rachford recursion, so this file keeps the source-facing orbit structure and bridges
-- it to the verified Chapter 26 owner `reflectedResolventComposition`.

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Proposition 26.13: the scaled residual pairing rewrites to the textbook
resolvent pairing after collecting the quadratic term `‖p - q‖²`. -/
private theorem scaledResidual_pairing_add_eq
    {x y p q : H} (γ : PosReal) :
    ‖p - q‖ ^ 2 +
        (γ : ℝ) * ⟪p - q, (γ : ℝ)⁻¹ • ((x - p) - (y - q))⟫_ℝ =
      ⟪x - y, p - q⟫_ℝ := by
  -- First cancel the scalar pair `γ * γ⁻¹`, then collapse the residual term exactly as in the
  -- resolvent inequality from Chapter 23.
  have hγinv : (γ : ℝ) * (γ : ℝ)⁻¹ = 1 := by
    field_simp [γ.2.ne']
  let d : H := p - q
  have hresid : (x - p) - (y - q) = (x - y) - d := by
    dsimp [d]
    abel_nf
  calc
    ‖p - q‖ ^ 2 + (γ : ℝ) * ⟪p - q, (γ : ℝ)⁻¹ • ((x - p) - (y - q))⟫_ℝ
        = ‖d‖ ^ 2 + (γ : ℝ) * ⟪d, (γ : ℝ)⁻¹ • ((x - y) - d)⟫_ℝ := by
            simp [d, hresid]
    _ = ‖d‖ ^ 2 + ⟪d, (x - y) - d⟫_ℝ := by
          rw [real_inner_smul_right, ← mul_assoc, hγinv, one_mul]
    _ = ‖d‖ ^ 2 + (⟪d, x - y⟫_ℝ - ‖d‖ ^ 2) := by
          rw [inner_sub_right, real_inner_self_eq_norm_sq]
    _ = ⟪d, x - y⟫_ℝ := by
          ring
    _ = ⟪x - y, d⟫_ℝ := by
          rw [real_inner_comm]
    _ = ⟪x - y, p - q⟫_ℝ := by
          simp [d]

/-- Helper for Proposition 26.13: uniform monotonicity yields the scaled resolvent inequality for
the canonical resolvent points of `A`. -/
private theorem scaledResolventMap_ineq
    {A : SetValuedOperator H H} {hA : Maximal IsMonotone A} {φ : NNReal → EReal}
    (hUniform : A.IsUniformlyMonotone φ) (γ : PosReal) (x y : H) :
    let p := resolventMap A hA γ x
    let q := resolventMap A hA γ y
    ((‖p - q‖ ^ 2 : ℝ) : EReal) + ((γ : ℝ) : EReal) * φ ‖p - q‖₊ ≤
      (⟪x - y, p - q⟫_ℝ : EReal) := by
  let p := resolventMap A hA γ x
  let q := resolventMap A hA γ y
  have hp : p ∈ J[((γ : ℝ) • A)] x := by
    rw [resolvent_smul_eq_singleton_resolventMap_of_maximal A hA γ x]
    simp [p]
  have hq : q ∈ J[((γ : ℝ) • A)] y := by
    rw [resolvent_smul_eq_singleton_resolventMap_of_maximal A hA γ y]
    simp [q]
  have hp_graph : ((p, (γ : ℝ)⁻¹ • (x - p)) : H × H) ∈ gra A :=
    (mem_resolvent_smul_iff_mem_graph A γ x p).1 hp
  have hq_graph : ((q, (γ : ℝ)⁻¹ • (y - q)) : H × H) ∈ gra A :=
    (mem_resolvent_smul_iff_mem_graph A γ y q).1 hq
  rw [mem_graph] at hp_graph hq_graph
  have hmono :
      φ ‖p - q‖₊ ≤
        (⟪p - q, (γ : ℝ)⁻¹ • ((x - p) - (y - q))⟫_ℝ : EReal) := by
    -- Rewrite the two graph values into one scaled residual difference.
    simpa [sub_eq_add_neg, smul_sub] using hUniform.ineq hp_graph hq_graph
  have hscaled :
      ((γ : ℝ) : EReal) * φ ‖p - q‖₊ ≤
        ((γ : ℝ) : EReal) *
          (⟪p - q, (γ : ℝ)⁻¹ • ((x - p) - (y - q))⟫_ℝ : EReal) := by
    exact mul_le_mul_of_nonneg_left hmono (by exact_mod_cast γ.2.le)
  have hnorm_nonneg :
      (0 : EReal) ≤ ((‖p - q‖ ^ 2 : ℝ) : EReal) := by
    exact_mod_cast sq_nonneg ‖p - q‖
  have hrewrite :
      ((‖p - q‖ ^ 2 : ℝ) : EReal) +
          ((γ : ℝ) : EReal) *
            (⟪p - q, (γ : ℝ)⁻¹ • ((x - p) - (y - q))⟫_ℝ : EReal) =
        (⟪x - y, p - q⟫_ℝ : EReal) := by
    exact_mod_cast scaledResidual_pairing_add_eq (γ := γ) (x := x) (y := y) (p := p) (q := q)
  -- Add the quadratic correction and rewrite the right-hand side into the source pairing.
  calc
    ((‖p - q‖ ^ 2 : ℝ) : EReal) + ((γ : ℝ) : EReal) * φ ‖p - q‖₊
        ≤ ((‖p - q‖ ^ 2 : ℝ) : EReal) +
            ((γ : ℝ) : EReal) *
              (⟪p - q, (γ : ℝ)⁻¹ • ((x - p) - (y - q))⟫_ℝ : EReal) := by
          simpa [add_assoc, add_left_comm, add_comm] using
            add_le_add_left hscaled (((‖p - q‖ ^ 2 : ℝ) : EReal))
    _ = (⟪x - y, p - q⟫_ℝ : EReal) := hrewrite

/-- Helper for Proposition 26.13: the scaled resolvent inequality also has a real-valued form
after converting the modulus term with `EReal.toReal`. -/
private theorem scaledResolventMap_toReal_ineq
    {A : SetValuedOperator H H} {hA : Maximal IsMonotone A} {φ : NNReal → EReal}
    (hUniform : A.IsUniformlyMonotone φ) (γ : PosReal) (x y : H) :
    let p := resolventMap A hA γ x
    let q := resolventMap A hA γ y
    ‖p - q‖ ^ 2 + (γ : ℝ) * (φ ‖p - q‖₊).toReal ≤ ⟪x - y, p - q⟫_ℝ := by
  let p := resolventMap A hA γ x
  let q := resolventMap A hA γ y
  have hineqE :
      ((‖p - q‖ ^ 2 : ℝ) : EReal) + ((γ : ℝ) : EReal) * φ ‖p - q‖₊ ≤
        (⟪x - y, p - q⟫_ℝ : EReal) := by
    simpa [p, q] using scaledResolventMap_ineq (A := A) (hA := hA) hUniform γ x y
  have hφ_nonneg : (0 : EReal) ≤ φ ‖p - q‖₊ := by
    rw [← (hUniform.modulus_eq_zero_iff 0).2 rfl]
    exact hUniform.modulusMonotone bot_le
  have hφ_bot : φ ‖p - q‖₊ ≠ ⊥ := by
    intro hbot
    rw [hbot] at hφ_nonneg
    simp at hφ_nonneg
  have hφ_top : φ ‖p - q‖₊ ≠ ⊤ := by
    intro htop
    have hγ_posE : (0 : EReal) < ((γ : ℝ) : EReal) := by
      exact_mod_cast γ.2
    have hmul_top : ((γ : ℝ) : EReal) * (⊤ : EReal) = ⊤ := by
      exact EReal.mul_top_of_pos hγ_posE
    have hadd_top : ((‖p - q‖ ^ 2 : ℝ) : EReal) + (⊤ : EReal) = ⊤ := by
      exact EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)
    have hleft_top :
        ((‖p - q‖ ^ 2 : ℝ) : EReal) + ((γ : ℝ) : EReal) * φ ‖p - q‖₊ = ⊤ := by
      rw [htop]
      rw [hmul_top, hadd_top]
    have : (⊤ : EReal) ≤ (⟪x - y, p - q⟫_ℝ : EReal) := by
      have hineqE' := hineqE
      rw [hleft_top] at hineqE'
      simpa using hineqE'
    simpa using this
  have hineqReal :
      (φ ‖p - q‖₊).toReal ≤
        ⟪p - q, (γ : ℝ)⁻¹ • ((x - p) - (y - q))⟫_ℝ := by
    have hpart :
        φ ‖p - q‖₊ ≤
          (⟪p - q, (γ : ℝ)⁻¹ • ((x - p) - (y - q))⟫_ℝ : EReal) := by
      have hp : p ∈ J[((γ : ℝ) • A)] x := by
        rw [resolvent_smul_eq_singleton_resolventMap_of_maximal A hA γ x]
        simp [p]
      have hq : q ∈ J[((γ : ℝ) • A)] y := by
        rw [resolvent_smul_eq_singleton_resolventMap_of_maximal A hA γ y]
        simp [q]
      have hp_graph : ((p, (γ : ℝ)⁻¹ • (x - p)) : H × H) ∈ gra A :=
        (mem_resolvent_smul_iff_mem_graph A γ x p).1 hp
      have hq_graph : ((q, (γ : ℝ)⁻¹ • (y - q)) : H × H) ∈ gra A :=
        (mem_resolvent_smul_iff_mem_graph A γ y q).1 hq
      rw [mem_graph] at hp_graph hq_graph
      simpa [sub_eq_add_neg, smul_sub] using hUniform.ineq hp_graph hq_graph
    simpa using EReal.toReal_le_toReal hpart hφ_bot (by simp)
  have hrewrite :
      (γ : ℝ) * ⟪p - q, (γ : ℝ)⁻¹ • ((x - p) - (y - q))⟫_ℝ =
        ⟪x - y, p - q⟫_ℝ - ‖p - q‖ ^ 2 := by
    nlinarith [scaledResidual_pairing_add_eq (γ := γ) (x := x) (y := y) (p := p) (q := q)]
  have hscaled := mul_le_mul_of_nonneg_left hineqReal γ.2.le
  nlinarith [hrewrite, hscaled]

/-- An orbit `x, z, y` satisfies the Peaceman--Rachford recursion `(26.51)` with operator pair
`(A, B)`, step `γ`, and initial point `y0`. -/
structure IsPeacemanRachfordOrbit
    (A B : SetValuedOperator H H) (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (γ : PosReal) (y0 : H) (x z y : ℕ → H) : Prop where
  /-- The orbit starts from the prescribed point `y0`. -/
  y_zero : y 0 = y0
  /-- The first backward step is `x_n = J_{γ B} y_n`, realized by `resolventMap B γ`. -/
  x_eq : ∀ n : ℕ, x n = resolventMap B hB γ (y n)
  /-- The second backward step is `z_n = J_{γ A}(2 x_n - y_n)`, realized by `resolventMap A γ`.
  -/
  z_eq : ∀ n : ℕ, z n = resolventMap A hA γ ((2 : ℝ) • x n - y n)
  /-- The reflected-resolvent update is `y_{n+1} = y_n + 2 (z_n - x_n)`. -/
  y_succ_eq : ∀ n : ℕ, y (n + 1) = y n + (2 : ℝ) • (z n - x n)

namespace IsPeacemanRachfordOrbit

/-- A Peaceman--Rachford orbit iterates the reflected-resolvent composition
`R_{γ A} ∘ R_{γ B}` on the `y`-sequence. -/
theorem y_succ_eq_reflectedResolventComposition
    {A B : SetValuedOperator H H} {hA : Maximal IsMonotone A} {hB : Maximal IsMonotone B}
    {γ : PosReal} {y0 : H} {x z y : ℕ → H}
    (hOrbit : IsPeacemanRachfordOrbit A B hA hB γ y0 x z y) :
    ∀ n : ℕ, y (n + 1) = reflectedResolventComposition A B hA hB γ (y n) := by
  intro n
  -- Expand the source recursion once and match it against the canonical reflected composition.
  rw [reflectedResolventComposition_apply]
  rw [hOrbit.y_succ_eq n, hOrbit.z_eq n, hOrbit.x_eq n]
  simp [sub_eq_add_neg, two_smul, add_assoc, add_left_comm, add_comm]

/-- A Peaceman--Rachford orbit is the forward iterate of
`reflectedResolventComposition A B hA hB γ` from `y0`. -/
theorem y_eq_iterate_reflectedResolventComposition
    {A B : SetValuedOperator H H} {hA : Maximal IsMonotone A} {hB : Maximal IsMonotone B}
    {γ : PosReal} {y0 : H} {x z y : ℕ → H}
    (hOrbit : IsPeacemanRachfordOrbit A B hA hB γ y0 x z y) :
    ∀ n : ℕ, y n = (reflectedResolventComposition A B hA hB γ)^[n] y0 := by
  intro n
  induction n with
  | zero =>
      -- The initial point agrees with the zeroth iterate by definition.
      simpa using hOrbit.y_zero
  | succ n hn =>
      -- Rewrite the next step with the canonical reflected operator, then use the induction
      -- hypothesis for the current iterate.
      rw [hOrbit.y_succ_eq_reflectedResolventComposition n, hn, Function.iterate_succ_apply']

/-- The `x`-sequence of a Peaceman--Rachford orbit is obtained by applying `J_{γ B}` to the
canonical reflected-resolvent iterate. -/
theorem x_eq_resolvent_iterate_reflectedResolventComposition
    {A B : SetValuedOperator H H} {hA : Maximal IsMonotone A} {hB : Maximal IsMonotone B}
    {γ : PosReal} {y0 : H} {x z y : ℕ → H}
    (hOrbit : IsPeacemanRachfordOrbit A B hA hB γ y0 x z y) :
    ∀ n : ℕ,
      x n = resolventMap B hB γ ((reflectedResolventComposition A B hA hB γ)^[n] y0) := by
  intro n
  -- The shadow sequence is exactly the resolvent of the canonical reflected iterate.
  rw [hOrbit.x_eq n, hOrbit.y_eq_iterate_reflectedResolventComposition n]

/-- Helper for Proposition 26.13: every primal solution has a reflected-resolvent fixed point whose
`B`-resolvent shadow is exactly that solution. -/
theorem fixedPointWithResolventShadow_of_mem_primalInclusionSolution
    {A B : SetValuedOperator H H} {hA : Maximal IsMonotone A} {hB : Maximal IsMonotone B}
    (γ : PosReal) {x : H} (hx : x ∈ primal_inclusion_solution_set A B) :
    ∃ y ∈ Function.fixedPoints (reflectedResolventComposition A B hA hB γ),
      resolventMap B hB γ y = x := by
  -- Unpack the image characterization from Proposition 26.1 and read off the witnessing fixed
  -- point directly.
  rw [primal_inclusion_solution_set_eq_image_resolvent_fixedPoints_reflectedResolventComposition
    A B hA hB γ] at hx
  rcases hx with ⟨y, hy, rfl⟩
  exact ⟨y, hy, rfl⟩

end IsPeacemanRachfordOrbit

/-- Proposition 26.13: let `A` and `B` be maximally monotone operators on a real Hilbert space.
Assume `B` is uniformly monotone, let `γ ∈ ℝ_{++}`, and let `xbar` be a solution of `0 ∈ A x + B x`,
formalized by `xbar ∈ primal_inclusion_solution_set A B`.
If `x`, `z`, and `y` satisfy the Peaceman--Rachford recursion `(26.51)` from `y0`, then `x_n`
converges strongly to `xbar`. -/
theorem peacemanRachford_tendsto_to_solution_of_uniformlyMonotone
    (A B : SetValuedOperator H H) (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    {φ : NNReal → EReal} (hB_uniform : B.IsUniformlyMonotone φ) (γ : PosReal) (xbar : H)
    (hxbar : xbar ∈ primal_inclusion_solution_set A B) (y0 : H) {x z y : ℕ → H}
    (hOrbit : IsPeacemanRachfordOrbit A B hA hB γ y0 x z y) :
    Tendsto x atTop (𝓝 xbar) := by
  -- Route correction: compare the Peaceman--Rachford orbit to a fixed point chosen from `hxbar`,
  -- then use the textbook square-drop inequality to force the modulus term to vanish.
  obtain ⟨yFix, hyFix, hJfix⟩ :=
    IsPeacemanRachfordOrbit.fixedPointWithResolventShadow_of_mem_primalInclusionSolution
      (A := A) (B := B) (hA := hA) (hB := hB) γ hxbar
  have hAfix :
      resolventMap A hA γ ((2 : ℝ) • xbar - yFix) = xbar := by
    have hyFix' :=
      (mem_fixedPoints_reflectedResolventComposition_iff_resolventMap_eq
        A B hA hB γ yFix).1 hyFix
    simpa [hJfix] using hyFix'
  let d : ℕ → ℝ := fun n ↦ ‖y n - yFix‖ ^ 2
  have hstep :
      ∀ n : ℕ,
        d (n + 1) + (4 : ℝ) * (γ : ℝ) * (φ ‖x n - xbar‖₊).toReal ≤ d n := by
    intro n
    have hreflect :=
      (reflected_resolvent_smul_nonexpansive_of_toSetValuedOperator_eq
        A hA γ (resolventMap A hA γ) (resolventMap_toSetValuedOperator_eq A hA γ)).dist_le_mul
          ((2 : ℝ) • x n - y n) ((2 : ℝ) • xbar - yFix)
    have hnorm :
        ‖y (n + 1) - yFix‖ ≤ ‖((2 : ℝ) • x n - y n) - ((2 : ℝ) • xbar - yFix)‖ := by
      -- Rewrite both reflected points into the orbit update and the fixed-point comparison value.
      have hleft_eval :
          (2 : ℝ) • resolventMap A hA γ ((2 : ℝ) • x n - y n) - ((2 : ℝ) • x n - y n) =
            y (n + 1) := by
        calc
          (2 : ℝ) • resolventMap A hA γ ((2 : ℝ) • x n - y n) - ((2 : ℝ) • x n - y n)
              = (2 : ℝ) • z n - ((2 : ℝ) • x n - y n) := by rw [hOrbit.z_eq n]
          _ = y n + (2 : ℝ) • (z n - x n) := by
                rw [smul_sub]
                abel_nf
          _ = y (n + 1) := by rw [hOrbit.y_succ_eq n]
      have hright_eval :
          (2 : ℝ) • resolventMap A hA γ ((2 : ℝ) • xbar - yFix) - ((2 : ℝ) • xbar - yFix) =
            yFix := by
        rw [hAfix]
        abel_nf
      have hreflect' := hreflect
      rw [dist_eq_norm, hleft_eval, hright_eval, dist_eq_norm] at hreflect'
      simpa using hreflect'
    have hnorm_sq :
        d (n + 1) ≤ d n - 4 * ⟪y n - yFix, x n - xbar⟫_ℝ + 4 * ‖x n - xbar‖ ^ 2 := by
      have hsq : ‖y (n + 1) - yFix‖ ^ 2 ≤
          ‖((2 : ℝ) • x n - y n) - ((2 : ℝ) • xbar - yFix)‖ ^ 2 := by
        exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hnorm
      have hexpand :
          ‖((2 : ℝ) • x n - y n) - ((2 : ℝ) • xbar - yFix)‖ ^ 2 =
            d n - 4 * ⟪y n - yFix, x n - xbar⟫_ℝ + 4 * ‖x n - xbar‖ ^ 2 := by
        have htmp :
            ‖(y n - yFix) - (2 : ℝ) • (x n - xbar)‖ ^ 2 =
              ‖y n - yFix‖ ^ 2 -
                2 * ⟪y n - yFix, (2 : ℝ) • (x n - xbar)⟫_ℝ +
                ‖(2 : ℝ) • (x n - xbar)‖ ^ 2 := by
          simpa [sub_eq_add_neg] using
            norm_sub_sq_real (y n - yFix) ((2 : ℝ) • (x n - xbar))
        have hsub :
            ((2 : ℝ) • x n - y n) - ((2 : ℝ) • xbar - yFix) =
              -((y n - yFix) - (2 : ℝ) • (x n - xbar)) := by
          simp [sub_eq_add_neg, two_smul, add_assoc, add_left_comm, add_comm]
        have hinner_two :
            ⟪y n - yFix, (2 : ℝ) • (x n - xbar)⟫_ℝ =
              2 * ⟪y n - yFix, x n - xbar⟫_ℝ := by
          rw [real_inner_smul_right]
        have hnorm_two :
            ‖(2 : ℝ) • (x n - xbar)‖ ^ 2 = 4 * ‖x n - xbar‖ ^ 2 := by
          rw [norm_smul, Real.norm_ofNat, pow_two]
          ring
        calc
          ‖((2 : ℝ) • x n - y n) - ((2 : ℝ) • xbar - yFix)‖ ^ 2
              = ‖(y n - yFix) - (2 : ℝ) • (x n - xbar)‖ ^ 2 := by
                  rw [hsub, norm_neg]
          _ = d n - 4 * ⟪y n - yFix, x n - xbar⟫_ℝ + 4 * ‖x n - xbar‖ ^ 2 := by
                rw [htmp, hinner_two, hnorm_two]
                simp [d]
                ring
      linarith
    have hresolvent :
        ‖x n - xbar‖ ^ 2 + (γ : ℝ) * (φ ‖x n - xbar‖₊).toReal ≤
          ⟪y n - yFix, x n - xbar⟫_ℝ := by
      simpa [hOrbit.x_eq n, hJfix] using
        scaledResolventMap_toReal_ineq (A := B) (hA := hB) hB_uniform γ (y n) yFix
    nlinarith
  have hanti : Antitone d := by
    refine antitone_nat_of_succ_le ?_
    intro n
    have hφ_nonneg : 0 ≤ (φ ‖x n - xbar‖₊).toReal := by
      have : (0 : EReal) ≤ φ ‖x n - xbar‖₊ := by
        rw [← (hB_uniform.modulus_eq_zero_iff 0).2 rfl]
        exact hB_uniform.modulusMonotone bot_le
      exact EReal.toReal_nonneg this
    have hterm_nonneg : 0 ≤ (4 : ℝ) * (γ : ℝ) * (φ ‖x n - xbar‖₊).toReal := by
      nlinarith [γ.2, hφ_nonneg]
    have hle : d (n + 1) ≤ d n := by
      linarith [hstep n, hterm_nonneg]
    exact hle
  obtain ⟨ℓ, hℓ⟩ :
      ∃ ℓ : ℝ, Tendsto d atTop (𝓝 ℓ) := by
    have hboundedBelow : BddBelow (Set.range d) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨n, rfl⟩
      positivity
    exact ⟨sInf (Set.range d), tendsto_atTop_ciInf hanti hboundedBelow⟩
  have hℓsucc : Tendsto (fun n ↦ d (n + 1)) atTop (𝓝 ℓ) := by
    simpa [Function.comp] using (Filter.tendsto_add_atTop_iff_nat 1).2 hℓ
  have hdiff_tendsto :
      Tendsto (fun n ↦ d n - d (n + 1)) atTop (𝓝 (0 : ℝ)) := by
    simpa using hℓ.sub hℓsucc
  have hφ_toReal_tendsto :
      Tendsto (fun n ↦ (φ ‖x n - xbar‖₊).toReal) atTop (𝓝 (0 : ℝ)) := by
    have hnonneg :
        ∀ n : ℕ, 0 ≤ (φ ‖x n - xbar‖₊).toReal := by
      intro n
      have hφ_nonneg : (0 : EReal) ≤ φ ‖x n - xbar‖₊ := by
        rw [← (hB_uniform.modulus_eq_zero_iff 0).2 rfl]
        exact hB_uniform.modulusMonotone bot_le
      exact EReal.toReal_nonneg hφ_nonneg
    have hupper :
        ∀ n : ℕ,
          (φ ‖x n - xbar‖₊).toReal ≤ (d n - d (n + 1)) / ((4 : ℝ) * (γ : ℝ)) := by
      intro n
      have hγpos : 0 < (4 : ℝ) * (γ : ℝ) := by
        nlinarith [γ.2]
      have hmul_le :
          ((4 : ℝ) * (γ : ℝ)) * (φ ‖x n - xbar‖₊).toReal ≤ d n - d (n + 1) := by
        linarith [hstep n]
      exact (le_div_iff₀ hγpos).2 <| by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hmul_le
    have hscaled :
        Tendsto (fun n ↦ (d n - d (n + 1)) / ((4 : ℝ) * (γ : ℝ))) atTop (𝓝 (0 : ℝ)) := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        hdiff_tendsto.const_mul (((4 : ℝ) * (γ : ℝ))⁻¹)
    refine squeeze_zero' (Eventually.of_forall hnonneg) ?_ hscaled
    exact Eventually.of_forall hupper
  have hnorm_tendsto_zero : Tendsto (fun n ↦ ‖x n - xbar‖) atTop (𝓝 (0 : ℝ)) := by
    by_contra hnot
    rw [Metric.tendsto_atTop] at hnot
    push Not at hnot
    rcases hnot with ⟨ε, hε, hbad⟩
    let εNN : NNReal := ⟨ε, hε.le⟩
    obtain ⟨n₀, -, hn₀⟩ := hbad 0
    have hε_le : εNN ≤ ‖x n₀ - xbar‖₊ := by
      simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using hn₀
    have hineqE :
        ((‖x n₀ - xbar‖ ^ 2 : ℝ) : EReal) + ((γ : ℝ) : EReal) * φ ‖x n₀ - xbar‖₊ ≤
          (⟪y n₀ - yFix, x n₀ - xbar⟫_ℝ : EReal) := by
      simpa [hOrbit.x_eq n₀, hJfix] using
        scaledResolventMap_ineq (A := B) (hA := hB) hB_uniform γ (y n₀) yFix
    have hnorm_nonneg :
        (0 : EReal) ≤ ((‖x n₀ - xbar‖ ^ 2 : ℝ) : EReal) := by
      exact_mod_cast sq_nonneg ‖x n₀ - xbar‖
    have hφ_nonneg : (0 : EReal) ≤ φ εNN := by
      rw [← (hB_uniform.modulus_eq_zero_iff 0).2 rfl]
      exact hB_uniform.modulusMonotone bot_le
    have hφ_eps_le :
        ((γ : ℝ) : EReal) * φ εNN ≤ (⟪y n₀ - yFix, x n₀ - xbar⟫_ℝ : EReal) := by
      have hmono :
          ((γ : ℝ) : EReal) * φ εNN ≤ ((γ : ℝ) : EReal) * φ ‖x n₀ - xbar‖₊ := by
        exact mul_le_mul_of_nonneg_left (hB_uniform.modulusMonotone hε_le)
          (by exact_mod_cast γ.2.le)
      have hdrop :
          ((γ : ℝ) : EReal) * φ ‖x n₀ - xbar‖₊ ≤
            ((‖x n₀ - xbar‖ ^ 2 : ℝ) : EReal) +
              ((γ : ℝ) : EReal) * φ ‖x n₀ - xbar‖₊ := by
        exact le_add_of_nonneg_left hnorm_nonneg
      exact le_trans hmono (le_trans hdrop hineqE)
    have hφ_eps_top : φ εNN ≠ ⊤ := by
      intro htop
      have hγ_posE : (0 : EReal) < ((γ : ℝ) : EReal) := by
        exact_mod_cast γ.2
      have hmul_top : ((γ : ℝ) : EReal) * (⊤ : EReal) = ⊤ := by
        exact EReal.mul_top_of_pos hγ_posE
      rw [htop, hmul_top] at hφ_eps_le
      simpa using hφ_eps_le
    have hφ_eps_ne_zero : φ εNN ≠ 0 := by
      intro hzero
      have hε_zero : εNN = 0 := (hB_uniform.modulus_eq_zero_iff εNN).1 hzero
      exact (ne_of_gt hε) <| by
        simpa [εNN] using congrArg (fun r : NNReal ↦ (r : ℝ)) hε_zero
    have hφ_eps_pos :
        0 < (φ εNN).toReal := by
      have hφ_eps_posE : (0 : EReal) < φ εNN :=
        lt_of_le_of_ne hφ_nonneg (Ne.symm hφ_eps_ne_zero)
      simpa using EReal.toReal_pos hφ_eps_posE hφ_eps_top
    have hfrequently :
        ∃ᶠ n in atTop, (φ εNN).toReal ≤ (φ ‖x n - xbar‖₊).toReal := by
      rw [Filter.frequently_atTop]
      intro N
      obtain ⟨n, hnN, hn⟩ := hbad N
      have hεn_le : εNN ≤ ‖x n - xbar‖₊ := by
        simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using hn
      have hφn_nonneg : (0 : EReal) ≤ φ ‖x n - xbar‖₊ := by
        rw [← (hB_uniform.modulus_eq_zero_iff 0).2 rfl]
        exact hB_uniform.modulusMonotone bot_le
      have hφn_top : φ ‖x n - xbar‖₊ ≠ ⊤ := by
        intro htop
        have hineqEn :
            ((‖x n - xbar‖ ^ 2 : ℝ) : EReal) + ((γ : ℝ) : EReal) * φ ‖x n - xbar‖₊ ≤
              (⟪y n - yFix, x n - xbar⟫_ℝ : EReal) := by
          simpa [hOrbit.x_eq n, hJfix] using
            scaledResolventMap_ineq (A := B) (hA := hB) hB_uniform γ (y n) yFix
        have hγ_posE : (0 : EReal) < ((γ : ℝ) : EReal) := by
          exact_mod_cast γ.2
        have hmul_top : ((γ : ℝ) : EReal) * (⊤ : EReal) = ⊤ := by
          exact EReal.mul_top_of_pos hγ_posE
        have hadd_top : ((‖x n - xbar‖ ^ 2 : ℝ) : EReal) + (⊤ : EReal) = ⊤ := by
          exact EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)
        have hineqEn' := hineqEn
        rw [htop, hmul_top, hadd_top] at hineqEn'
        simpa using hineqEn'
      have hφn_bot : φ ‖x n - xbar‖₊ ≠ ⊥ := by
        intro hbot
        rw [hbot] at hφn_nonneg
        simp at hφn_nonneg
      refine ⟨n, hnN, ?_⟩
      exact EReal.toReal_le_toReal (hB_uniform.modulusMonotone hεn_le) (by
        intro hbot
        rw [hbot] at hφ_nonneg
        simp at hφ_nonneg) hφn_top
    rcases (Metric.tendsto_atTop.1 hφ_toReal_tendsto) ((φ εNN).toReal / 2) (by linarith)
      with ⟨N, hN⟩
    obtain ⟨n, hnN, hnlower⟩ := (Filter.frequently_atTop.1 hfrequently) N
    have hclose := hN n hnN
    have hφn_nonneg_real : 0 ≤ (φ ‖x n - xbar‖₊).toReal := by
      have hφn_nonneg : (0 : EReal) ≤ φ ‖x n - xbar‖₊ := by
        rw [← (hB_uniform.modulus_eq_zero_iff 0).2 rfl]
        exact hB_uniform.modulusMonotone bot_le
      exact EReal.toReal_nonneg hφn_nonneg
    have hclose' : (φ ‖x n - xbar‖₊).toReal < (φ εNN).toReal / 2 := by
      simpa [Real.dist_eq, abs_of_nonneg hφn_nonneg_real] using hclose
    linarith
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa using hnorm_tendsto_zero

end SetValuedOperator
