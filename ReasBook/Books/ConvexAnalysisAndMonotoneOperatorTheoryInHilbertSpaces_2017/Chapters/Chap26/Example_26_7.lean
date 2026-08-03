import BauschkeLean.Chap01.Text_1_0_11
import BauschkeLean.Chap03.Corollary_3_22
import BauschkeLean.Chap06.Definition_6_38
import BauschkeLean.Chap06.Example_6_43
import BauschkeLean.Chap20.Proposition_20_60

open EuclideanGeometry
open Filter
open scoped InnerProductSpace Pointwise Set SetValuedOperator Topology

universe u

namespace SetValuedOperator

/- Source/core/bridge triage:
- `source-facing`: Example 26.7 records the weak-limit consequences for a subspace `V`, its
  orthogonal complement `Vᗮ`, and the inclusion `0 ∈ N_V x + A x`.
- `core/canonical`: the owner abstractions are
  `Maximal.mem_prod_inter_graph_of_projection_residual_zero_of_tendsto_weakly_seq`,
  `Maximal.tendsto_inner_of_projection_residual_zero_of_tendsto_weakly_seq`, `gra A`,
  `N[(V : Set H)]`, and `A.zeros`.
- `bridge/view`: interpret `V` and `Vᗮ` as affine subspaces via `toAffineSubspace`, rewrite their
  metric projections as `starProjection`, and reuse the affine-subspace normal-cone owner from
  Example 6.43. -/

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

section Example267

variable {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) (V : Submodule ℝ H)
variable [V.HasOrthogonalProjection]
variable {xSeq uSeq : ℕ → H} {x u : H}
variable (hgraph : ∀ n, (xSeq n, uSeq n) ∈ gra A)
variable (hxSeq : Tendsto (fun n ↦ toWeakSpace ℝ H (xSeq n)) atTop (𝓝 (toWeakSpace ℝ H x)))
variable (huSeq : Tendsto (fun n ↦ toWeakSpace ℝ H (uSeq n)) atTop (𝓝 (toWeakSpace ℝ H u)))
variable (hxVorth : Tendsto (fun n ↦ Vᗮ.starProjection (xSeq n)) atTop (𝓝 (0 : H)))
variable (huV : Tendsto (fun n ↦ V.starProjection (uSeq n)) atTop (𝓝 (0 : H)))

omit [CompleteSpace H] in
private instance submodule_toAffineSubspace_nonempty (W : Submodule ℝ H) :
    Nonempty (Submodule.toAffineSubspace W) := by
  refine ⟨⟨0, ?_⟩⟩
  exact (Submodule.mem_toAffineSubspace).2 (by simp)

omit [CompleteSpace H] in
private instance submodule_toAffineSubspace_direction_hasOrthogonalProjection
    (W : Submodule ℝ H) [W.HasOrthogonalProjection] :
    (Submodule.toAffineSubspace W).direction.HasOrthogonalProjection := by
  simpa [Submodule.toAffineSubspace_direction] using
    (inferInstance : W.HasOrthogonalProjection)

omit [CompleteSpace H] in
private theorem coe_orthogonalProjection_toAffineSubspace_eq_starProjection
    (W : Submodule ℝ H) [W.HasOrthogonalProjection] (x : H) :
    (orthogonalProjection (Submodule.toAffineSubspace W) x : H) = W.starProjection x := by
  refine (coe_orthogonalProjection_eq_iff_mem).2 ?_
  constructor
  · exact (Submodule.mem_toAffineSubspace).2 (W.starProjection_apply_mem x)
  · rw [Submodule.toAffineSubspace_direction]
    exact W.sub_starProjection_mem_orthogonal x

include hA V hgraph hxSeq huSeq hxVorth huV

private theorem mem_and_tendsto_inner_of_submodule_projection_residual_zero_of_tendsto_weakly_seq
    : (x, u) ∈ ((V : Set H) ×ˢ (Vᗮ : Set H)) ∩ gra A ∧
        Tendsto (fun n ↦ ⟪xSeq n, uSeq n⟫_ℝ) atTop (𝓝 ⟪x, u⟫_ℝ) := by
  let C : AffineSubspace ℝ H := V.toAffineSubspace
  let D : AffineSubspace ℝ H := Vᗮ.toAffineSubspace
  have hC_nonempty : (C : Set H).Nonempty := by
    refine ⟨0, ?_⟩
    simp [C, Submodule.mem_toAffineSubspace]
  have hD_nonempty : (D : Set H).Nonempty := by
    refine ⟨0, ?_⟩
    simp [D, Submodule.mem_toAffineSubspace]
  have hC_closed : IsClosed (C : Set H) := by
    simpa [C, Submodule.mem_toAffineSubspace, Submodule.orthogonal_orthogonal] using
      (Vᗮ.isClosed_orthogonal : IsClosed (((Vᗮ)ᗮ : Submodule ℝ H) : Set H))
  have hD_closed : IsClosed (D : Set H) := by
    simpa [D, Submodule.mem_toAffineSubspace] using
      (V.isClosed_orthogonal : IsClosed ((Vᗮ : Submodule ℝ H) : Set H))
  have hCD : D.direction = C.directionᗮ := by
    simp [C, D, Submodule.toAffineSubspace_direction]
  letI : Nonempty C := nonempty_subtype.mpr hC_nonempty
  letI : Nonempty D := nonempty_subtype.mpr hD_nonempty
  letI : C.direction.HasOrthogonalProjection := by
    simpa [C, Submodule.toAffineSubspace_direction] using
      (inferInstance : V.HasOrthogonalProjection)
  letI : D.direction.HasOrthogonalProjection := by
    simpa [D, Submodule.toAffineSubspace_direction] using
      (inferInstance : (Vᗮ).HasOrthogonalProjection)
  have hCproj :
      Tendsto
        (fun n ↦
          xSeq n -
            P[(C : Set H),
              isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed C.convex] (xSeq n))
        atTop (𝓝 (0 : H)) := by
    have hEq :
        (fun n ↦
          xSeq n -
            P[(C : Set H),
              isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed C.convex] (xSeq n)) =
          fun n ↦ Vᗮ.starProjection (xSeq n) := by
      funext n
      rw [projectionPoint_eq_orthogonalProjection_of_nonempty_isClosed_affineSubspace
        hC_nonempty hC_closed]
      rw [show (orthogonalProjection C (xSeq n) : H) = V.starProjection (xSeq n) by
        simpa [C] using coe_orthogonalProjection_toAffineSubspace_eq_starProjection V (xSeq n)]
      simp
    simpa [hEq] using hxVorth
  have hDproj :
      Tendsto
        (fun n ↦
          uSeq n -
            P[(D : Set H),
              isChebyshev_of_nonempty_isClosed_convex hD_nonempty hD_closed D.convex] (uSeq n))
        atTop (𝓝 (0 : H)) := by
    have hEq :
        (fun n ↦
          uSeq n -
            P[(D : Set H),
              isChebyshev_of_nonempty_isClosed_convex hD_nonempty hD_closed D.convex] (uSeq n)) =
          fun n ↦ V.starProjection (uSeq n) := by
      funext n
      rw [projectionPoint_eq_orthogonalProjection_of_nonempty_isClosed_affineSubspace
        hD_nonempty hD_closed]
      rw [show (orthogonalProjection D (uSeq n) : H) = Vᗮ.starProjection (uSeq n) by
        simpa [D] using
          coe_orthogonalProjection_toAffineSubspace_eq_starProjection Vᗮ (uSeq n)]
      simp
    simpa [hEq] using huV
  refine ⟨?_, ?_⟩
  · have hmem :
        (x, u) ∈ ((C : Set H) ×ˢ (D : Set H)) ∩ gra A :=
      Maximal.mem_prod_inter_graph_of_projection_residual_zero_of_tendsto_weakly_seq
        hC_nonempty hC_closed hD_nonempty hD_closed hA hCD hgraph hxSeq huSeq hCproj hDproj
    simpa [C, D, Submodule.mem_toAffineSubspace] using hmem
  · exact
      Maximal.tendsto_inner_of_projection_residual_zero_of_tendsto_weakly_seq
        hC_nonempty hC_closed hD_nonempty hD_closed hA hCD hgraph hxSeq huSeq hCproj hDproj

/-- Example 26.7 (2): under the hypotheses of Example 26.7, the weak limit pair belongs to
`(V × Vᗮ) ∩ gra A`. -/
theorem mem_prod_orthogonal_inter_graph_of_projection_residual_zero_of_tendsto_weakly_seq
    : (x, u) ∈ ((V : Set H) ×ˢ (Vᗮ : Set H)) ∩ gra A := by
  exact
    (mem_and_tendsto_inner_of_submodule_projection_residual_zero_of_tendsto_weakly_seq
      hA V hgraph hxSeq huSeq hxVorth huV).1

/-- Example 26.7 (1): let `V` be a closed linear subspace of `H`, let `A : H → 2^H` be
maximally monotone, let `(xSeq n, uSeq n)` be a sequence in `gra A`, and let `(x, u) ∈ H × H`.
If `xSeq n ⇀ x`, `uSeq n ⇀ u`, `Vᗮ.starProjection (xSeq n) → 0`, and
`V.starProjection (uSeq n) → 0`, then
`x ∈ zer (N_V + A)`, formalized as `x ∈ (N[(V : Set H)] + A).zeros`. -/
theorem mem_zeros_normalCone_add_of_projection_residual_zero_of_tendsto_weakly_seq
    : x ∈ (N[(V : Set H)] + A).zeros := by
  obtain ⟨⟨hxV, huVorth⟩, hxu⟩ :=
    mem_prod_orthogonal_inter_graph_of_projection_residual_zero_of_tendsto_weakly_seq
      hA V hgraph hxSeq huSeq hxVorth huV
  rw [SetValuedOperator.mem_zeros_iff]
  refine Set.mem_add.2 ⟨-u, ?_, u, ?_, by simp⟩
  · have hxV' : x ∈ V := by simpa using hxV
    have huVorth' : u ∈ Vᗮ := by simpa using huVorth
    change -u ∈ N[(V : Set H)] x
    rw [show N[(V : Set H)] x = (Vᗮ : Set H) by
      simpa [Submodule.mem_toAffineSubspace, Submodule.toAffineSubspace_direction] using
        normalCone_affineSubspace_eq_direction_orthogonal_of_mem
          V.toAffineSubspace ((Submodule.mem_toAffineSubspace).2 hxV')]
    exact Vᗮ.neg_mem huVorth'
  · simpa [SetValuedOperator.mem_graph] using hxu

/-- Example 26.7 (3): under the hypotheses of Example 26.7, the weak limit pairing vanishes:
`⟪x, u⟫_ℝ = 0`. -/
theorem inner_eq_zero_of_projection_residual_zero_of_tendsto_weakly_seq
    : ⟪x, u⟫_ℝ = 0 := by
  obtain ⟨⟨hxV, huVorth⟩, _⟩ :=
    mem_prod_orthogonal_inter_graph_of_projection_residual_zero_of_tendsto_weakly_seq
      hA V hgraph hxSeq huSeq hxVorth huV
  exact Submodule.inner_right_of_mem_orthogonal hxV huVorth

/-- Example 26.7 (4): under the hypotheses of Example 26.7, the pairings converge to `0`:
`⟪xSeq n, uSeq n⟫_ℝ → 0`. -/
theorem tendsto_inner_zero_of_projection_residual_zero_of_tendsto_weakly_seq
    : Tendsto (fun n ↦ ⟪xSeq n, uSeq n⟫_ℝ) atTop (𝓝 (0 : ℝ)) := by
  have hinner :
      Tendsto (fun n ↦ ⟪xSeq n, uSeq n⟫_ℝ) atTop (𝓝 ⟪x, u⟫_ℝ) :=
    (mem_and_tendsto_inner_of_submodule_projection_residual_zero_of_tendsto_weakly_seq
      hA V hgraph hxSeq huSeq hxVorth huV).2
  have hzero :=
    inner_eq_zero_of_projection_residual_zero_of_tendsto_weakly_seq
      hA V hgraph hxSeq huSeq hxVorth huV
  simpa [hzero] using hinner

omit hA V hgraph hxSeq huSeq hxVorth huV

end Example267

end SetValuedOperator
