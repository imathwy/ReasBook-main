import BauschkeLean.Chap26.Example_26_7
import BauschkeLean.Chap26.Proposition_26_4

open Filter
open scoped BigOperators InnerProductSpace Pointwise SetValuedOperator Topology

universe u

noncomputable section

namespace SetValuedOperator

-- Domain-style sampling:
-- - primary domain: weak sequential limits for finite families of maximally monotone operators on
--   a finite Hilbert direct sum
-- - inspected owners:
--   `SetValuedOperator.familyOperator`
--   `SetValuedOperator.mem_familyOperator_iff`
--   `SetValuedOperator.mem_zeros_normalCone_add_of_projection_residual_zero_of_tendsto_weakly_seq`
--   `SetValuedOperator.diagonalPoint_image_zeros_sum_eq_zeros_normalCone_add_familyOperator`
-- - owner abstraction: the product-space operator `familyOperator A` together with the diagonal
--   submodule bridge from Proposition 26.4
-- - primitive data: coordinatewise graph membership, weak limits, vanishing sum of the dual
--   sequence, and vanishing diagonal projection residuals
-- - derived API: the five source-facing Corollary 26.8 consequences below
--
-- Source/core/bridge triage:
-- - `source-facing`: the five coordinatewise consequences stated in Corollary 26.8
-- - `core/canonical`: `familyOperator A` on the finite Hilbert product together with Example 26.7
-- - `bridge/view`: Proposition 26.4 identifies the diagonal and its orthogonal complement with the
--   textbook finite-family conditions `x i = x j` and `∑ i, u i = 0`
--
-- Source note: item (iv) is split into an explicit convergence statement and the vanishing of the
-- limiting pairing.

variable {m : ℕ}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation "ProductSpace" => lp (fun _ : Fin m ↦ H) 2
local notation "Diagonal" => (diagonalSubmodule : Submodule ℝ ProductSpace)
local notation "DiagonalSet" =>
  (((diagonalSubmodule : Submodule ℝ ProductSpace) : Set ProductSpace))
local notation "DiagonalOrthogonal" => (((Diagonal : Submodule ℝ ProductSpace)ᗮ :
  Submodule ℝ ProductSpace))

private def lpFamily (w : Fin m → H) : ProductSpace :=
  (lpPiLpₗᵢ (fun _ : Fin m ↦ H) ℝ).symm (WithLp.toLp 2 w)

omit [CompleteSpace H] in
@[simp] private theorem lpFamily_apply (w : Fin m → H) (i : Fin m) :
    lpFamily w i = w i := by
  change ((lpPiLpₗᵢ (fun _ : Fin m ↦ H) ℝ).symm (WithLp.toLp 2 w)) i = w i
  rw [coe_lpPiLpₗᵢ_symm]

private def lpFamilySeq (w : Fin m → ℕ → H) : ℕ → ProductSpace :=
  fun n ↦ lpFamily (fun i ↦ w i n)

omit [CompleteSpace H] in
@[simp] private theorem inner_lpFamily_eq_sum (w z : Fin m → H) :
    ⟪lpFamily w, lpFamily z⟫_ℝ = ∑ i, ⟪w i, z i⟫_ℝ := by
  symm
  calc
    ∑ i, ⟪w i, z i⟫_ℝ
        = ∑ i, ⟪(lpPiLpₗᵢ (fun _ : Fin m ↦ H) ℝ (lpFamily w)) i,
            (lpPiLpₗᵢ (fun _ : Fin m ↦ H) ℝ (lpFamily z)) i⟫_ℝ := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simp [lpFamily]
    _ = ⟪lpPiLpₗᵢ (fun _ : Fin m ↦ H) ℝ (lpFamily w),
          lpPiLpₗᵢ (fun _ : Fin m ↦ H) ℝ (lpFamily z)⟫_ℝ := by
            symm
            rw [PiLp.inner_apply]
    _ = ⟪lpFamily w, lpFamily z⟫_ℝ := by
          exact
            (lpPiLpₗᵢ (fun _ : Fin m ↦ H) ℝ).inner_map_map (lpFamily w) (lpFamily z)

section

variable (A : Fin m → SetValuedOperator H H)
variable (hA : ∀ i, Maximal IsMonotone (A i))
variable (xSeq uSeq : Fin m → ℕ → H) (x u : Fin m → H)
variable (hgraph : ∀ i n, (xSeq i n, uSeq i n) ∈ gra (A i))
variable (hu_sum : Tendsto (fun n ↦ ∑ i, uSeq i n) atTop (𝓝 (0 : H)))
variable (hx : ∀ i, Tendsto (fun n ↦ toWeakSpace ℝ H (xSeq i n)) atTop (𝓝 (toWeakSpace ℝ H (x i))))
variable (hu : ∀ i, Tendsto (fun n ↦ toWeakSpace ℝ H (uSeq i n)) atTop (𝓝 (toWeakSpace ℝ H (u i))))
variable
  (hdiag :
    ∀ i,
      Tendsto
        (fun n ↦ (m : ℝ) • xSeq i n - ∑ j, xSeq j n)
        atTop (𝓝 (0 : H)))

omit [CompleteSpace H] in
/-- Helper for Corollary 26.8: strong coordinatewise convergence packages into strong convergence
of the associated finite Hilbert product sequence. -/
private theorem tendsto_lpFamily_of_coordinatewise
    {wSeq : Fin m → ℕ → H} {w : Fin m → H}
    (hw : ∀ i, Tendsto (fun n ↦ wSeq i n) atTop (𝓝 (w i))) :
    Tendsto (fun n ↦ lpFamilySeq wSeq n) atTop (𝓝 (lpFamily w)) := by
  have hlpFamily : Continuous fun v : Fin m → H ↦ lpFamily v := by
    -- Package the coordinate family through the canonical `WithLp`/`PiLp`/`lp` identifications.
    have htoLp : Continuous fun v : Fin m → H ↦ (WithLp.toLp 2 v : PiLp 2 (fun _ : Fin m ↦ H)) := by
      simpa [PiLp.coe_symm_continuousLinearEquiv] using
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m ↦ H)).symm.continuous
    change Continuous fun v : Fin m → H ↦
      (lpPiLpₗᵢ (fun _ : Fin m ↦ H) ℝ).symm (WithLp.toLp 2 v)
    exact (lpPiLpₗᵢ (fun _ : Fin m ↦ H) ℝ).symm.continuous.comp htoLp
  have hcoord :
      Tendsto (fun n ↦ fun i ↦ wSeq i n) atTop (𝓝 w) :=
    tendsto_pi_nhds.2 hw
  -- Apply the continuous product-space packaging map to the coordinatewise limit.
  simpa [lpFamilySeq] using (hlpFamily.tendsto w).comp hcoord

omit [CompleteSpace H] in
/-- Helper for Corollary 26.8: coordinatewise weak convergence packages into weak convergence in
the finite Hilbert product. -/
private theorem tendsto_toWeakSpace_lpFamily_of_coordinatewise
    {wSeq : Fin m → ℕ → H} {w : Fin m → H}
    (hw :
      ∀ i, Tendsto (fun n ↦ toWeakSpace ℝ H (wSeq i n)) atTop (𝓝 (toWeakSpace ℝ H (w i)))) :
    Tendsto (fun n ↦ toWeakSpace ℝ ProductSpace (lpFamilySeq wSeq n)) atTop
      (𝓝 (toWeakSpace ℝ ProductSpace (lpFamily w))) := by
  let lpFamilyCLM : (Fin m → H) →L[ℝ] ProductSpace :=
    ((lpPiLpₗᵢ (fun _ : Fin m ↦ H) ℝ).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m ↦ H)).symm.toContinuousLinearMap)
  let packToWeak : (Fin m → WeakSpace ℝ H) → WeakSpace ℝ ProductSpace :=
    fun z ↦
      toWeakSpace ℝ ProductSpace (lpFamily fun i ↦ (toWeakSpace ℝ H).symm (z i))
  have hpackToWeak : Continuous packToWeak := by
    rw [continuous_iff_forall_weakDual_apply]
    intro l
    let lPi : StrongDual ℝ (Fin m → H) := l.comp lpFamilyCLM
    have hcoordEval :
        ∀ i : Fin m,
          Continuous fun z : Fin m → WeakSpace ℝ H ↦
            StrongDual.toWeakDual (lPi.comp (ContinuousLinearMap.single ℝ (fun _ : Fin m ↦ H) i))
              ((toWeakSpace ℝ H).symm (z i)) := by
      intro i
      have hweakEval :
          Continuous fun z : WeakSpace ℝ H ↦
            StrongDual.toWeakDual (lPi.comp
              (ContinuousLinearMap.single ℝ (fun _ : Fin m ↦ H) i))
              ((toWeakSpace ℝ H).symm z) :=
        (continuous_iff_forall_weakDual_apply (f := fun z : WeakSpace ℝ H ↦ z)).1
          continuous_id
          (StrongDual.toWeakDual (lPi.comp
            (ContinuousLinearMap.single ℝ (fun _ : Fin m ↦ H) i)))
      exact hweakEval.comp (continuous_apply i)
    have hsum :
        Continuous fun z : Fin m → WeakSpace ℝ H ↦
          ∑ i, StrongDual.toWeakDual (lPi.comp
            (ContinuousLinearMap.single ℝ (fun _ : Fin m ↦ H) i))
            ((toWeakSpace ℝ H).symm (z i)) := by
      exact continuous_finset_sum _ fun i _ ↦ hcoordEval i
    -- Split every product functional into the finite sum of its coordinate functionals.
    refine hsum.congr ?_
    intro z
    simpa [packToWeak, lpFamilyCLM, lPi, StrongDual.toWeakDual_apply] using
      (ContinuousLinearMap.sum_comp_single
        (L := lPi) (v := fun i ↦ (toWeakSpace ℝ H).symm (z i)))
  have hcoord :
      Tendsto (fun n ↦ fun i ↦ toWeakSpace ℝ H (wSeq i n)) atTop
        (𝓝 fun i ↦ toWeakSpace ℝ H (w i)) :=
    tendsto_pi_nhds.2 hw
  -- Compose the coordinatewise weak limit with the continuous weak-space packaging map.
  simpa [packToWeak, lpFamilySeq] using
    (hpackToWeak.tendsto fun i ↦ toWeakSpace ℝ H (w i)).comp hcoord

/-- Helper for Corollary 26.8: the orthogonal residual of the primal product sequence tends
strongly to `0` once the source residuals `m xᵢₙ - ∑ⱼ xⱼₙ` do. -/
private theorem tendsto_diagonalOrthogonalProjection_lpFamilySeq_zero_of_residual
    {xSeq : Fin m → ℕ → H}
    (hdiag :
      ∀ i,
        Tendsto
          (fun n ↦ (m : ℝ) • xSeq i n - ∑ j, xSeq j n)
          atTop (𝓝 (0 : H))) :
    Tendsto
      (fun n ↦
        (((diagonalSubmodule : Submodule ℝ ProductSpace)ᗮ :
          Submodule ℝ ProductSpace).starProjection (lpFamilySeq xSeq n)))
      atTop (𝓝 (0 : ProductSpace)) := by
  have hcoord :
      ∀ i,
        Tendsto
          (fun n ↦ xSeq i n - (m : ℝ)⁻¹ • ∑ j, xSeq j n)
          atTop (𝓝 (0 : H)) := by
    intro i
    have hm_pos : 0 < m := lt_of_lt_of_le (Nat.succ_pos _) (Nat.succ_le_of_lt i.is_lt)
    have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm_pos)
    -- Rescale the source residual to recover the orthogonal-projection coordinate formula.
    simpa [smul_sub, inv_smul_smul₀ hm_ne] using (hdiag i).const_smul ((m : ℝ)⁻¹)
  have hfamily :
      Tendsto
        (fun n ↦
          lpFamily fun i ↦ xSeq i n - (m : ℝ)⁻¹ • ∑ j, xSeq j n)
        atTop (𝓝 (lpFamily fun _ : Fin m ↦ (0 : H))) :=
    tendsto_lpFamily_of_coordinatewise (m := m) (H := H) hcoord
  have hEq :
      (fun n ↦
        (((diagonalSubmodule : Submodule ℝ ProductSpace)ᗮ :
          Submodule ℝ ProductSpace).starProjection (lpFamilySeq xSeq n))) =
        fun n ↦ lpFamily fun i ↦ xSeq i n - (m : ℝ)⁻¹ • ∑ j, xSeq j n := by
    funext n
    ext i
    have hcoordEq :
        ((((diagonalSubmodule : Submodule ℝ ProductSpace)ᗮ :
            Submodule ℝ ProductSpace).starProjection (lpFamilySeq xSeq n)) i) =
          ((lpFamilySeq xSeq n -
            diagonalPoint ((m : ℝ)⁻¹ • ∑ j, lpFamilySeq xSeq n j)) : ProductSpace) i := by
      simpa using
        congrArg
          (fun z : ProductSpace ↦ z i)
          (starProjection_orthogonal_diagonalSubmodule_eq_sub_diagonalPoint_average
            (m := m) (H := H) (lpFamilySeq xSeq n))
    simpa [lpFamilySeq, Pi.sub_apply] using hcoordEq
  -- Rewrite the orthogonal projection with Proposition 26.4(4), then package the coordinates.
  rw [hEq]
  simpa using hfamily

/-- Helper for Corollary 26.8: the diagonal projection of the dual product sequence tends
strongly to `0` once the coordinate sum does. -/
private theorem tendsto_diagonalProjection_lpFamilySeq_zero_of_sum
    {uSeq : Fin m → ℕ → H}
    (hu_sum : Tendsto (fun n ↦ ∑ i, uSeq i n) atTop (𝓝 (0 : H))) :
    Tendsto
      (fun n ↦
        (diagonalSubmodule : Submodule ℝ ProductSpace).starProjection (lpFamilySeq uSeq n))
      atTop (𝓝 (0 : ProductSpace)) := by
  have hscaled :
      Tendsto
        (fun n ↦ (m : ℝ)⁻¹ • ∑ i, uSeq i n)
        atTop (𝓝 (0 : H)) := by
    -- Clause (3) of Proposition 26.4 rewrites the diagonal projection as a scaled total sum.
    simpa using hu_sum.const_smul ((m : ℝ)⁻¹)
  have hcoord :
      ∀ i : Fin m,
        Tendsto
          (fun n ↦ (m : ℝ)⁻¹ • ∑ j, uSeq j n)
          atTop (𝓝 (0 : H)) := by
    intro i
    simpa using hscaled
  have hfamily :
      Tendsto
        (fun n ↦ lpFamily fun _ : Fin m ↦ (m : ℝ)⁻¹ • ∑ i, uSeq i n)
        atTop (𝓝 (lpFamily fun _ : Fin m ↦ (0 : H))) :=
    tendsto_lpFamily_of_coordinatewise (m := m) (H := H) hcoord
  have hEq :
      (fun n ↦
        (diagonalSubmodule : Submodule ℝ ProductSpace).starProjection (lpFamilySeq uSeq n)) =
        fun n ↦ lpFamily fun _ : Fin m ↦ (m : ℝ)⁻¹ • ∑ i, uSeq i n := by
    funext n
    simpa [diagonalPoint, lpFamily, lpFamilySeq] using
      (starProjection_diagonalSubmodule_eq_diagonalPoint_average
        (m := m) (H := H) (lpFamilySeq uSeq n))
  -- Rewrite the diagonal projection with Proposition 26.4(3).
  -- Then use continuity of `diagonalPoint`.
  rw [hEq]
  simpa using hfamily

-- Proof route: specialize Example 26.7 to the product-space operator `familyOperator A` and the
-- submodule `diagonalSubmodule`. Proposition 26.4 supplies the bridge between the projection
-- residual hypotheses and the source finite-family equalities/sum conditions.
/-- Corollary 26.8: package the finite-family weak graph hypotheses into the product-space
conclusion supplied by Example 26.7 for `familyOperator A` and the diagonal submodule. -/
private theorem weak_graph_diagonal_residual_zero_familyOperator_core
    (hA : ∀ i, Maximal IsMonotone (A i))
    (hgraph : ∀ i n, (xSeq i n, uSeq i n) ∈ gra (A i))
    (hu_sum : Tendsto (fun n ↦ ∑ i, uSeq i n) atTop (𝓝 (0 : H)))
    (hx : ∀ i, Tendsto (fun n ↦ toWeakSpace ℝ H (xSeq i n)) atTop (𝓝 (toWeakSpace ℝ H (x i))))
    (hu : ∀ i, Tendsto (fun n ↦ toWeakSpace ℝ H (uSeq i n)) atTop (𝓝 (toWeakSpace ℝ H (u i))))
    (hdiag :
      ∀ i,
        Tendsto
          (fun n ↦ (m : ℝ) • xSeq i n - ∑ j, xSeq j n)
          atTop (𝓝 (0 : H))) :
    lpFamily x ∈ (Set.normalCone DiagonalSet + familyOperator A).zeros ∧
      (lpFamily x, lpFamily u) ∈
        (DiagonalSet ×ˢ (DiagonalOrthogonal : Set ProductSpace)) ∩ gra (familyOperator A) ∧
      Tendsto
        (fun n ↦ ⟪lpFamilySeq xSeq n, lpFamilySeq uSeq n⟫_ℝ)
        atTop (𝓝 (0 : ℝ)) ∧
      ⟪lpFamily x, lpFamily u⟫_ℝ = (0 : ℝ) := by
  have hfamilyA : Maximal IsMonotone (familyOperator A) :=
    familyOperator_maximal_of_maximal A hA
  have hgraphFamily :
      ∀ n, (lpFamilySeq xSeq n, lpFamilySeq uSeq n) ∈ gra (familyOperator A) := by
    intro n
    -- Package the coordinatewise graph hypotheses into the graph of the product operator.
    rw [SetValuedOperator.mem_graph]
    rw [mem_familyOperator_iff]
    intro i
    simpa [SetValuedOperator.mem_graph] using hgraph i n
  have hxFamily :
      Tendsto
        (fun n ↦ toWeakSpace ℝ ProductSpace (lpFamilySeq xSeq n))
        atTop (𝓝 (toWeakSpace ℝ ProductSpace (lpFamily x))) :=
    tendsto_toWeakSpace_lpFamily_of_coordinatewise (m := m) (H := H) hx
  have huFamily :
      Tendsto
        (fun n ↦ toWeakSpace ℝ ProductSpace (lpFamilySeq uSeq n))
        atTop (𝓝 (toWeakSpace ℝ ProductSpace (lpFamily u))) :=
    tendsto_toWeakSpace_lpFamily_of_coordinatewise (m := m) (H := H) hu
  have hxOrth :
      Tendsto
        (fun n ↦
          (((diagonalSubmodule : Submodule ℝ ProductSpace)ᗮ :
            Submodule ℝ ProductSpace).starProjection (lpFamilySeq xSeq n)))
        atTop (𝓝 (0 : ProductSpace)) :=
    tendsto_diagonalOrthogonalProjection_lpFamilySeq_zero_of_residual (m := m) (H := H) hdiag
  have huDiag :
      Tendsto
        (fun n ↦
          (diagonalSubmodule : Submodule ℝ ProductSpace).starProjection (lpFamilySeq uSeq n))
        atTop (𝓝 (0 : ProductSpace)) :=
    tendsto_diagonalProjection_lpFamilySeq_zero_of_sum (m := m) (H := H) hu_sum
  -- Apply Example 26.7 to the product operator and the diagonal submodule.
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using
      mem_zeros_normalCone_add_of_projection_residual_zero_of_tendsto_weakly_seq
        hfamilyA Diagonal hgraphFamily hxFamily huFamily hxOrth huDiag
  · simpa using
      mem_prod_orthogonal_inter_graph_of_projection_residual_zero_of_tendsto_weakly_seq
        hfamilyA Diagonal hgraphFamily hxFamily huFamily hxOrth huDiag
  · simpa using
      tendsto_inner_zero_of_projection_residual_zero_of_tendsto_weakly_seq
        hfamilyA Diagonal hgraphFamily hxFamily huFamily hxOrth huDiag
  · simpa using
      inner_eq_zero_of_projection_residual_zero_of_tendsto_weakly_seq
        hfamilyA Diagonal hgraphFamily hxFamily huFamily hxOrth huDiag

include hA xSeq uSeq x u hgraph hu_sum hx hu hdiag

/-- Consequence of Corollary 26.8: let `A : Fin m → H → 2^H` be maximally monotone, and let
`(xSeq i n, uSeq i n) ∈ gra (A i)` converge weakly to `(x i, u i)` with
`∑ i, uSeq i n → 0` and `(m : ℝ) • xSeq i n - ∑ j, xSeq j n → 0` for every `i`.
Then there exists `xZero ∈ zer (∑ i, A i)`, formalized as `xZero ∈ (∑ i, A i).zeros`,
such that `x i = xZero` for every `i`. The textbook also assumes `m ≥ 2`, but this
product-space formulation does not use that hypothesis in the Lean API. -/
theorem exists_common_limit_mem_zeros_sum_of_weak_graph_diagonal_residual_zero :
    ∃ xZero ∈ (∑ i, A i).zeros, ∀ i, x i = xZero := by
  obtain ⟨hxZero, -, -, -⟩ :=
    weak_graph_diagonal_residual_zero_familyOperator_core
      A xSeq uSeq x u hA hgraph hu_sum hx hu hdiag
  have hxdiag :
      lpFamily x ∈ diagonalPoint '' (∑ i, A i).zeros := by
    simpa [diagonalPoint_image_zeros_sum_eq_zeros_normalCone_add_familyOperator] using hxZero
  rcases hxdiag with ⟨xZero, hxZero, hxeq⟩
  refine ⟨xZero, hxZero, ?_⟩
  intro i
  have hcoord : diagonalPoint xZero i = lpFamily x i :=
    congrArg (fun z : ProductSpace ↦ z i) hxeq
  simpa using hcoord.symm

/-- Another consequence of Corollary 26.8: under the same hypotheses,
`∑ i, u i = 0`. -/
theorem sum_limit_eq_zero_of_weak_graph_diagonal_residual_zero :
    ∑ i, u i = (0 : H) := by
  obtain ⟨-, hpair, -, -⟩ :=
    weak_graph_diagonal_residual_zero_familyOperator_core
      A xSeq uSeq x u hA hgraph hu_sum hx hu hdiag
  have huorth : lpFamily u ∈ DiagonalOrthogonal := by
    exact hpair.1.2
  have huzero : lpFamily u ∈ sumZeroSubmodule := by
    simpa [diagonalSubmodule_orthogonal_eq_sumZeroSubmodule] using huorth
  simpa [sumZeroSubmodule] using huzero

/-- Another consequence of Corollary 26.8: each weak limit pair
`(x i, u i)` belongs to `gra (A i)`. Combined with Corollary 26.8 (1), this yields
`(xZero, u i) ∈ gra (A i)` for the common zero `xZero`. -/
theorem mem_graph_limit_of_weak_graph_diagonal_residual_zero :
    ∀ i, (x i, u i) ∈ gra (A i) := by
  obtain ⟨-, hpair, -, -⟩ :=
    weak_graph_diagonal_residual_zero_familyOperator_core
      A xSeq uSeq x u hA hgraph hu_sum hx hu hdiag
  have hfamily : lpFamily u ∈ familyOperator A (lpFamily x) := by
    simpa [SetValuedOperator.mem_graph] using hpair.2
  intro i
  have hi := (mem_familyOperator_iff A (lpFamily x) (lpFamily u)).1 hfamily i
  simpa [SetValuedOperator.mem_graph] using hi

/-- Another consequence of Corollary 26.8: the pairings
`∑ i, ⟪xSeq i n, uSeq i n⟫_ℝ` converge to `∑ i, ⟪x i, u i⟫_ℝ`. -/
theorem tendsto_sum_inner_limit_of_weak_graph_diagonal_residual_zero :
    Tendsto
      (fun n ↦ ∑ i, ⟪xSeq i n, uSeq i n⟫_ℝ)
      atTop (𝓝 (∑ i, ⟪x i, u i⟫_ℝ)) := by
  obtain ⟨-, -, htendsto, hinner_zero⟩ :=
    weak_graph_diagonal_residual_zero_familyOperator_core
      A xSeq uSeq x u hA hgraph hu_sum hx hu hdiag
  have hsum_zero :=
    show ∑ i, ⟪x i, u i⟫_ℝ = (0 : ℝ) by
      simpa using hinner_zero
  simpa [lpFamilySeq, hsum_zero] using htendsto

/-- Another consequence of Corollary 26.8: the limiting pairing vanishes:
`∑ i, ⟪x i, u i⟫_ℝ = 0`. Together with Corollary 26.8 (4), this gives the source conclusion
`∑ i, ⟪xSeq i n, uSeq i n⟫_ℝ → 0`. -/
theorem sum_inner_limit_eq_zero_of_weak_graph_diagonal_residual_zero :
    ∑ i, ⟪x i, u i⟫_ℝ = (0 : ℝ) := by
  obtain ⟨-, -, -, hinner_zero⟩ :=
    weak_graph_diagonal_residual_zero_familyOperator_core
      A xSeq uSeq x u hA hgraph hu_sum hx hu hdiag
  simpa using hinner_zero

end

end SetValuedOperator
