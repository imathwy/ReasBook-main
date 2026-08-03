import BauschkeLean.Chap01.Text_1_0_11
import BauschkeLean.Chap02.Lemma_2_41
import BauschkeLean.Chap05.Theorem_5_5
import BauschkeLean.Chap20.Definition_20_20
import BauschkeLean.Chap20.Proposition_20_44
import BauschkeLean.Chap23.Example_23_40
import BauschkeLean.Chap23.Proposition_23_30

open Filter
open scoped InnerProductSpace Pointwise SetValuedOperator Topology

universe u

namespace SetValuedOperator

-- Semantic recall: `lean_leansearch` surfaced the ambient orthogonal-complement/projection API
-- but no direct owner for Spingarn's method, so this file keeps the source-facing solution/orbit
-- surface and uses the canonical partial-inverse owner `A₍V₎` only for the zero-set bridge.
--
-- Source/core/bridge triage:
-- - `source-facing`: `IsSpingarnPartialInverseSolution`,
--   `IsSpingarnPartialInverseOrbit`, and Theorem 26.9 itself.
-- - `core/canonical`: the Chapter 20 partial inverse `A₍V₎`, its zero set `(A₍V₎).zeros`, and
--   the Chapter 23 resolvent owner `J[A]`.
-- - `bridge/view`: the solution/zero-set equivalence and the orbit/resolvent step theorem below.

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A pair `(x, u)` solves Spingarn's partial-inverse inclusion problem for `A` and `V` when
`x ∈ V`, `u ∈ Vᗮ`, and `u ∈ A x`. -/
def IsSpingarnPartialInverseSolution
    (A : SetValuedOperator H H) (V : Submodule ℝ H) (x u : H) : Prop :=
  x ∈ V ∧ u ∈ Vᗮ ∧ u ∈ A x

/-- A source solution of Spingarn's inclusion problem is exactly a `V`/`Vᗮ` decomposition of a
zero of the partial inverse `A₍V₎`. -/
theorem isSpingarnPartialInverseSolution_iff_mem_zeros_partialInverse
    {A : SetValuedOperator H H} (V : Submodule ℝ H) [V.HasOrthogonalProjection] {x u : H} :
    IsSpingarnPartialInverseSolution A V x u ↔
      x ∈ V ∧ u ∈ Vᗮ ∧ x + u ∈ (A₍V₎).zeros := by
  constructor
  · rintro ⟨hx, hu, hAu⟩
    refine ⟨hx, hu, ?_⟩
    -- Rewrite the partial-inverse zero condition into graph membership for `A`.
    rw [mem_zeros_partialInverse_iff_projection_mem_graph, mem_graph]
    -- The orthogonal projections of `x + u` recover the source decomposition.
    have hxproj : V.starProjection (x + u) = x := by
      refine V.eq_starProjection_of_mem_orthogonal hx ?_
      simpa using hu
    have huproj : Vᗮ.starProjection (x + u) = u := by
      refine (Vᗮ).eq_starProjection_of_mem_orthogonal hu ?_
      simpa using V.le_orthogonal_orthogonal hx
    simpa [hxproj, huproj] using hAu
  · rintro ⟨hx, hu, hzero⟩
    refine ⟨hx, hu, ?_⟩
    -- Convert the canonical zero-set condition back to the original graph condition.
    rw [mem_zeros_partialInverse_iff_projection_mem_graph, mem_graph] at hzero
    have hxproj : V.starProjection (x + u) = x := by
      refine V.eq_starProjection_of_mem_orthogonal hx ?_
      simpa using hu
    have huproj : Vᗮ.starProjection (x + u) = u := by
      refine (Vᗮ).eq_starProjection_of_mem_orthogonal hu ?_
      simpa using V.le_orthogonal_orthogonal hx
    simpa [hxproj, huproj] using hzero

namespace IsSpingarnPartialInverseSolution

/-- A source solution yields a zero of the canonical partial inverse `A₍V₎`. -/
theorem add_mem_zeros_partialInverse
    {A : SetValuedOperator H H} {V : Submodule ℝ H} [V.HasOrthogonalProjection] {x u : H}
    (h : IsSpingarnPartialInverseSolution A V x u) :
    x + u ∈ (A₍V₎).zeros :=
  (isSpingarnPartialInverseSolution_iff_mem_zeros_partialInverse V).1 h |>.2.2

/-- Once the source side conditions `x ∈ V` and `u ∈ Vᗮ` are fixed, solving Spingarn's inclusion
problem is equivalent to `x + u` being a zero of the partial inverse `A₍V₎`. -/
theorem iff_add_mem_zeros_partialInverse
    {A : SetValuedOperator H H} (V : Submodule ℝ H) [V.HasOrthogonalProjection] {x u : H}
    (hx : x ∈ V) (hu : u ∈ Vᗮ) :
    IsSpingarnPartialInverseSolution A V x u ↔ x + u ∈ (A₍V₎).zeros := by
  rw [isSpingarnPartialInverseSolution_iff_mem_zeros_partialInverse V]
  constructor
  · rintro ⟨_, _, hzero⟩
    exact hzero
  · intro hzero
    exact ⟨hx, hu, hzero⟩

end IsSpingarnPartialInverseSolution

/-- An orbit satisfies Spingarn's recursion when it starts from `x0 ∈ V` and `u0 ∈ Vᗮ` and, for
every `n`, chooses `y n` and `v n` so that `v n = x n + u n - y n` and `v n ∈ A (y n)`
(equivalently, `y n ∈ J[A] (x n + u n)`), and updates by
`x (n + 1) = P_V (y n)` and `u (n + 1) = P_{Vᗮ} (v n)`. -/
structure IsSpingarnPartialInverseOrbit
    (A : SetValuedOperator H H) (V : Submodule ℝ H) [V.HasOrthogonalProjection]
    (x0 u0 : H) (x u y v : ℕ → H) : Prop where
  /-- The initial primal iterate belongs to `V`. -/
  x0_mem : x0 ∈ V
  /-- The initial dual iterate belongs to `Vᗮ`. -/
  u0_mem : u0 ∈ Vᗮ
  /-- The primal orbit starts at the prescribed `x0`. -/
  x_zero : x 0 = x0
  /-- The dual orbit starts at the prescribed `u0`. -/
  u_zero : u 0 = u0
  /-- The residual is `v n = x n + u n - y n`. -/
  v_eq : ∀ n : ℕ, v n = x n + u n - y n
  /-- Equivalently to the resolvent step, each residual belongs to `A (y n)`. -/
  v_mem : ∀ n : ℕ, v n ∈ A (y n)
  /-- The next primal iterate is the projection of `y n` onto `V`. -/
  x_succ_eq : ∀ n : ℕ, x (n + 1) = V.starProjection (y n)
  /-- The next dual iterate is the projection of `v n` onto `Vᗮ`. -/
  u_succ_eq : ∀ n : ℕ, u (n + 1) = Vᗮ.starProjection (v n)

namespace IsSpingarnPartialInverseOrbit

omit [CompleteSpace H] in
/-- Each source residual step is equivalently a resolvent step `y n ∈ J[A] (x n + u n)`. -/
theorem y_mem_resolvent
    {A : SetValuedOperator H H} {V : Submodule ℝ H} [V.HasOrthogonalProjection]
    {x0 u0 : H} {x u y v : ℕ → H}
    (hOrbit : IsSpingarnPartialInverseOrbit A V x0 u0 x u y v) (n : ℕ) :
    y n ∈ J[A] (x n + u n) := by
  have hy :
      y n ∈ J[((1 : ℝ) • A)] (x n + u n) := by
    refine
      (mem_resolvent_smul_iff_sub_mem_smul A (1 : ERealFunction.PosReal) (x n + u n) (y n)).2 ?_
    simpa [hOrbit.v_eq n]
      using hOrbit.v_mem n
  simpa using hy

end IsSpingarnPartialInverseOrbit

/-- Helper for Theorem 26.9: each Spingarn iterate is the corresponding orthogonal projection of
the summed orbit `x n + u n`. -/
theorem spingarnOrbit_projection_eq
    {A : SetValuedOperator H H} {V : Submodule ℝ H} [V.HasOrthogonalProjection]
    {x0 u0 : H} {x u y v : ℕ → H}
    (hOrbit : IsSpingarnPartialInverseOrbit A V x0 u0 x u y v) (n : ℕ) :
    x n = V.starProjection (x n + u n) ∧ u n = Vᗮ.starProjection (x n + u n) := by
  -- First record that the recursion keeps the primal iterates in `V`.
  have hx_mem : ∀ n : ℕ, x n ∈ V := by
    intro n
    induction n with
    | zero =>
        simpa [hOrbit.x_zero] using hOrbit.x0_mem
    | succ n ihn =>
        simpa [hOrbit.x_succ_eq n] using V.starProjection_apply_mem (y n)
  -- The same recursion keeps the dual iterates in `Vᗮ`.
  have hu_mem : ∀ n : ℕ, u n ∈ Vᗮ := by
    intro n
    induction n with
    | zero =>
        simpa [hOrbit.u_zero] using hOrbit.u0_mem
    | succ n ihn =>
        simpa [hOrbit.u_succ_eq n] using Vᗮ.starProjection_apply_mem (v n)
  constructor
  · -- Since `(x n + u n) - x n = u n ∈ Vᗮ`, the `V`-projection is exactly `x n`.
    symm
    refine V.eq_starProjection_of_mem_orthogonal (hx_mem n) ?_
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hu_mem n
  · -- Since `(x n + u n) - u n = x n ∈ (Vᗮ)ᗮ`, the `Vᗮ`-projection is exactly `u n`.
    symm
    refine (Vᗮ).eq_starProjection_of_mem_orthogonal (hu_mem n) ?_
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      V.le_orthogonal_orthogonal (hx_mem n)

/-- Helper for Theorem 26.9: the summed orbit `x n + u n` satisfies the source bridge identity
`P_V z_{n+1} + P_{Vᗮ}(z_n - z_{n+1}) = y_n`. -/
theorem spingarnBridge_eq_resolventPoint
    {A : SetValuedOperator H H} {V : Submodule ℝ H} [V.HasOrthogonalProjection]
    {x0 u0 : H} {x u y v : ℕ → H}
    (hOrbit : IsSpingarnPartialInverseOrbit A V x0 u0 x u y v) (n : ℕ) :
    V.starProjection (x (n + 1) + u (n + 1)) +
        Vᗮ.starProjection ((x n + u n) - (x (n + 1) + u (n + 1))) =
      y n := by
  have hzproj_n := spingarnOrbit_projection_eq (A := A) (V := V) hOrbit n
  have hzproj_succ := spingarnOrbit_projection_eq (A := A) (V := V) hOrbit (n + 1)
  have hx_mem_n : x n ∈ V := by
    rw [hzproj_n.1]
    exact V.starProjection_apply_mem (x n + u n)
  have hu_mem_n : u n ∈ Vᗮ := by
    rw [hzproj_n.2]
    exact Vᗮ.starProjection_apply_mem (x n + u n)
  have hx_zero : Vᗮ.starProjection (x n) = 0 := by
    refine (Vᗮ).eq_starProjection_of_mem_orthogonal ?_ ?_
    · simp
    · simpa using V.le_orthogonal_orthogonal hx_mem_n
  have hu_diff : u n - u (n + 1) = Vᗮ.starProjection (y n) := by
    -- Project the residual identity `v n = x n + u n - y n` onto `Vᗮ`.
    rw [hOrbit.u_succ_eq, hOrbit.v_eq n, ContinuousLinearMap.map_sub, ContinuousLinearMap.map_add,
      hx_zero, Submodule.starProjection_eq_self_iff.mpr hu_mem_n]
    abel_nf
  have hVsucc : V.starProjection (x (n + 1) + u (n + 1)) = x (n + 1) := by
    simpa using hzproj_succ.1.symm
  have hOrthSub :
      Vᗮ.starProjection ((x n + u n) - (x (n + 1) + u (n + 1))) = u n - u (n + 1) := by
    rw [ContinuousLinearMap.map_sub, ← hzproj_n.2, ← hzproj_succ.2]
  -- Assemble the `V`- and `Vᗮ`-components back into `y n`.
  calc
    V.starProjection (x (n + 1) + u (n + 1)) +
        Vᗮ.starProjection ((x n + u n) - (x (n + 1) + u (n + 1)))
        = x (n + 1) + (u n - u (n + 1)) := by
            rw [hVsucc, hOrthSub]
    _ = V.starProjection (y n) + Vᗮ.starProjection (y n) := by
          rw [hOrbit.x_succ_eq, hu_diff]
    _ = y n := by
          simpa using V.starProjection_add_starProjection_orthogonal (y n)

/-- Theorem 26.9: let `A : H → 2^H` be maximally monotone and let `V` be a closed linear
subspace, represented in Lean by `[V.HasOrthogonalProjection]`. If the problem
`find x ∈ V and u ∈ Vᗮ such that u ∈ A x` has a solution, and if `x` and `u` satisfy Spingarn's
recursion `(26.22)` from initial data `x0 ∈ V` and `u0 ∈ Vᗮ`, then there exists a solution
`(xLim, uLim)` of that problem such that `x n ⇀ xLim` and `u n ⇀ uLim`. -/
theorem exists_weakLimit_isSpingarnPartialInverseSolution_of_isSpingarnPartialInverseOrbit
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) (V : Submodule ℝ H)
    [V.HasOrthogonalProjection] (hsol : ∃ x u, IsSpingarnPartialInverseSolution A V x u)
    {x0 u0 : H} {x u y v : ℕ → H}
    (hOrbit : IsSpingarnPartialInverseOrbit A V x0 u0 x u y v) :
    ∃ xLim uLim, IsSpingarnPartialInverseSolution A V xLim uLim ∧
      Tendsto (fun n ↦ toWeakSpace ℝ H (x n)) atTop (𝓝 (toWeakSpace ℝ H xLim)) ∧
      Tendsto (fun n ↦ toWeakSpace ℝ H (u n)) atTop (𝓝 (toWeakSpace ℝ H uLim)) := by
  let z : ℕ → H := fun n ↦ x n + u n
  have hApartial : Maximal IsMonotone (A₍V₎) :=
    (partialInverse_isMaximallyMonotone_iff (A := A) (V := V)).2 hA
  have hzeros : (A₍V₎).zeros.Nonempty := by
    rcases hsol with ⟨xSol, uSol, hxuSol⟩
    exact ⟨xSol + uSol, IsSpingarnPartialInverseSolution.add_mem_zeros_partialInverse hxuSol⟩
  have hz_mem_resolvent : ∀ n : ℕ, z (n + 1) ∈ J[(A₍V₎)] (z n) := by
    intro n
    -- Proposition 23.30 turns the source bridge identity into the partial-inverse resolvent step.
    rw [mem_resolvent_partialInverse_iff_mem_resolvent]
    have hy :
        V.starProjection (x (n + 1) + u (n + 1)) +
            Vᗮ.starProjection ((x n + u n) - (x (n + 1) + u (n + 1))) ∈
          J[A] (x n + u n) := by
      rw [spingarnBridge_eq_resolventPoint (A := A) (V := V) hOrbit n]
      exact hOrbit.y_mem_resolvent n
    simpa [z, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hy
  have hz_eq_proximal :
      z = proximalPointSequence (A₍V₎) hApartial (1 : ERealFunction.PosReal) (x0 + u0) := by
    funext n
    induction n with
    | zero =>
        -- The summed orbit starts from the prescribed initial decomposition.
        simp [z, hOrbit.x_zero, hOrbit.u_zero]
    | succ n ihn =>
        have hzsucc_mem : z (n + 1) ∈ J[(A₍V₎)] (z n) := hz_mem_resolvent n
        have hzsucc_eq :
            z (n + 1) =
              resolventMap (A₍V₎) hApartial (1 : ERealFunction.PosReal) (z n) := by
          have hzsucc_mem' :
              z (n + 1) ∈ J[(((1 : ℝ) • (A₍V₎)) : SetValuedOperator H H)] (z n) := by
            simpa [resolvent_def, one_smul] using hzsucc_mem
          have hsingleton :
              J[(((1 : ℝ) • (A₍V₎)) : SetValuedOperator H H)] (z n) =
                ({resolventMap (A₍V₎) hApartial (1 : ERealFunction.PosReal) (z n)} : Set H) := by
            simpa using
              (resolvent_smul_eq_singleton_resolventMap_of_maximal
                (A₍V₎) hApartial (1 : ERealFunction.PosReal) (z n))
          rw [hsingleton] at hzsucc_mem'
          simpa using hzsucc_mem'
        calc
          z (n + 1) =
              resolventMap (A₍V₎) hApartial (1 : ERealFunction.PosReal) (z n) := hzsucc_eq
          _ =
              resolventMap (A₍V₎) hApartial (1 : ERealFunction.PosReal)
                (proximalPointSequence (A₍V₎) hApartial (1 : ERealFunction.PosReal) (x0 + u0) n) := by
                  rw [ihn]
          _ =
              proximalPointSequence (A₍V₎) hApartial (1 : ERealFunction.PosReal) (x0 + u0)
                (n + 1) := by
                  rw [proximalPointSequence_succ]
  rcases exists_weakLimit_mem_zeros_of_proximalPointSequence
      (A₍V₎) hApartial (1 : ERealFunction.PosReal) (x0 + u0) hzeros with
    ⟨zLim, hzLim_zero, hzLim_proximal⟩
  have hzLim :
      Tendsto (fun n ↦ toWeakSpace ℝ H (z n)) atTop (𝓝 (toWeakSpace ℝ H zLim)) := by
    -- Identify the summed orbit with the canonical proximal-point sequence.
    simpa [hz_eq_proximal] using hzLim_proximal
  have hx_proj : ∀ n : ℕ, x n = V.starProjection (z n) := by
    intro n
    simpa [z] using (spingarnOrbit_projection_eq (A := A) (V := V) hOrbit n).1
  have hu_proj : ∀ n : ℕ, u n = Vᗮ.starProjection (z n) := by
    intro n
    simpa [z] using (spingarnOrbit_projection_eq (A := A) (V := V) hOrbit n).2
  have hxLim_sol :
      IsSpingarnPartialInverseSolution A V (V.starProjection zLim) (Vᗮ.starProjection zLim) := by
    -- Convert the partial-inverse zero `zLim ∈ (A₍V₎).zeros` back into a source solution pair.
    rw [IsSpingarnPartialInverseSolution.iff_add_mem_zeros_partialInverse
      (A := A) (V := V) (x := V.starProjection zLim) (u := Vᗮ.starProjection zLim)
      (V.starProjection_apply_mem zLim) (Vᗮ.starProjection_apply_mem zLim)]
    simpa using hzLim_zero
  have hxLim :
      Tendsto (fun n ↦ toWeakSpace ℝ H (x n)) atTop
        (𝓝 (toWeakSpace ℝ H (V.starProjection zLim))) := by
    -- Weak convergence is preserved by the continuous affine projector onto `V`.
    simpa [hx_proj] using
      (continuousAffineMap_tendsto_toWeakSpace
        (T := V.starProjection.toContinuousAffineMap) hzLim)
  have huLim :
      Tendsto (fun n ↦ toWeakSpace ℝ H (u n)) atTop
        (𝓝 (toWeakSpace ℝ H (Vᗮ.starProjection zLim))) := by
    -- The same transport applies to the orthogonal-complement projector.
    simpa [hu_proj] using
      (continuousAffineMap_tendsto_toWeakSpace
        (T := Vᗮ.starProjection.toContinuousAffineMap) hzLim)
  exact ⟨V.starProjection zLim, Vᗮ.starProjection zLim, hxLim_sol, hxLim, huLim⟩

end SetValuedOperator
