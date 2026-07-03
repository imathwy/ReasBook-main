import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_2_32 (from Chap02) -/
/- This item lies in the duality/operator-norm domain for separated source and target seminorms on
finite-dimensional real inner-product-space models, with the textbook `ℝⁿ → ℝᵐ` case treated as a
later Euclidean specialization.

Sampled owner-style declarations:
* `Seminorm.dualNorm`
* `Seminorm.dualNorm_apply`
* `Seminorm.inner_le_dualNorm_mul`
* `InnerProductSpace.toDual`
* `ContinuousLinearMap.opNorm`, the canonical ambient-norm owner for operator norms on continuous
  linear maps
* `operatorNorm_eq_sSup_dualPairing_unitSpheres` in `Chap06/Definition_6_3`
* `hessianOperatorToDual` in `Chap04/Text_4_2_3`, the project's intrinsic dual-valued operator
  owner
* `Matrix.toEuclideanLin`, the canonical bridge from matrices to owner linear maps

Owner abstraction:
* `Seminorm.primalDualOperatorNorm p d A` for `A : E →ₗ[ℝ] StrongDual ℝ F`

Primitive data:
* a source seminorm `p`
* a target seminorm `d`
* a linear map `A : E →ₗ[ℝ] StrongDual ℝ F`
* a finite-dimensional real normed-space structure on the source `E`
* the source-side separation hypothesis `[Seminorm.IsNorm p]`
* a finite-dimensional real inner-product-space structure on `F`
* the target-side separation hypothesis `[Seminorm.IsNorm d]`, needed for the transported dual
  norm on `StrongDual ℝ F`

Derived API:
* the defining supremum formula over the primal unit ball
* the two-ball dual-pairing formula
* the Euclidean bridge `A : E →ₗ[ℝ] F ↦ (InnerProductSpace.toDual ℝ F).toLinearMap.comp A`
* the ambient-norm companion owner `ContinuousLinearMap.opNorm` only in the special case where `p`
  and `d` are the ambient norms
* the finite-dimensional matrix realization via `A.toEuclideanLin`, composed with `toDual`, as a
  bridge/view, not as a second public owner

Source/core/bridge triage:
* source-facing: the textbook induced operator norm with source seminorm `p` and target dual norm
  `d*` on the finite-dimensional source/target setting where the displayed real supremum is honest
* core/canonical: the same owner on dual-valued maps `E →ₗ[ℝ] StrongDual ℝ F`
* bridge/view: the `F`-valued Euclidean realization obtained by composing with
  `InnerProductSpace.toDual`, together with the ambient-norm specialization to
  `ContinuousLinearMap.opNorm`
-/

noncomputable section

open InnerProductSpace
open scoped Matrix.Norms.L2Operator SeminormDualNorm

universe u v

namespace Seminorm

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable (p : Seminorm ℝ E) [IsNorm p]
variable (d : Seminorm ℝ F) [FiniteDimensional ℝ F] [IsNorm d]

/-- For separated finite-dimensional source and target seminorm geometries, the transported
`d*`-norm image of the closed `p`-unit ball is bounded above, so the operator-norm owner below is
an honest real supremum. -/
private theorem bddAbove_primalDualOperatorNormImage
    (A : E →ₗ[ℝ] StrongDual ℝ F) :
    BddAbove ((fun x : E ↦ ‖(toDual ℝ F).symm (A x)‖[d,*]) '' p.closedBall 0 1) := by
  obtain ⟨Cp, hCp_pos, hp_norm_le⟩ := p.exists_norm_le_mul
  obtain ⟨Cd, hCd_pos, hd_dual_le⟩ := d.exists_dualNorm_le_mul_norm
  refine ⟨Cd * (‖A.toContinuousLinearMap‖ * Cp), ?_⟩
  rintro z ⟨x, hx, rfl⟩
  have hx_norm : ‖x‖ ≤ Cp := by
    have hpx : p x ≤ 1 := by
      simpa [Seminorm.mem_closedBall_zero] using hx
    calc
      ‖x‖ ≤ Cp * p x := hp_norm_le x
      _ ≤ Cp * 1 := by
        gcongr
      _ = Cp := by
        ring
  calc
    ‖(toDual ℝ F).symm (A x)‖[d,*] ≤ Cd * ‖(toDual ℝ F).symm (A x)‖ := hd_dual_le _
    _ = Cd * ‖A x‖ := by rw [← (toDual ℝ F).symm.norm_map]
    _ ≤ Cd * (‖A.toContinuousLinearMap‖ * ‖x‖) := by
      gcongr
      simpa using A.toContinuousLinearMap.le_opNorm x
    _ ≤ Cd * (‖A.toContinuousLinearMap‖ * Cp) := by
      gcongr
    _ = Cd * (‖A.toContinuousLinearMap‖ * Cp) := rfl

/-- Definition 2.32: the `p`-to-`d*` induced operator norm of a dual-valued linear map `A`,
computed as the supremum of the transported `d*`-norm over the primal closed unit ball. The owner
lives on `E →ₗ[ℝ] StrongDual ℝ F`, with the concrete Euclidean realization `E →ₗ[ℝ] F` recovered
by composing with `toDual`. Under the finite-dimensional separated source/target hypotheses of the
textbook setting, this `ℝ`-valued supremum is the genuine induced operator norm; in the later
ambient-norm specialization it agrees with the ordinary operator norm. -/
def primalDualOperatorNorm (p : Seminorm ℝ E) [FiniteDimensional ℝ E] [p.IsNorm]
    (d : Seminorm ℝ F) [FiniteDimensional ℝ F] [d.IsNorm]
    (A : E →ₗ[ℝ] StrongDual ℝ F) : ℝ :=
  sSup ((fun x : E ↦ ‖(toDual ℝ F).symm (A x)‖[d,*]) '' p.closedBall 0 1)

end Seminorm

namespace SeminormOperatorNorm

/- Source-facing Lean notation for the `p`-to-`d*` induced operator norm. -/
scoped notation:max "‖" A "‖[" p " ⇀ " d ",*]" =>
  Seminorm.primalDualOperatorNorm p d A

end SeminormOperatorNorm

open scoped SeminormOperatorNorm

namespace Seminorm

section

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable (p : Seminorm ℝ E) [IsNorm p]
variable (d : Seminorm ℝ F) [FiniteDimensional ℝ F] [IsNorm d]

/-- Expanding `‖A‖[p ⇀ d,*]` gives its defining supremum over the primal closed unit ball. -/
theorem primalDualOperatorNorm_def (A : E →ₗ[ℝ] StrongDual ℝ F) :
    ‖A‖[p ⇀ d,*] =
      sSup ((fun x : E ↦ ‖(toDual ℝ F).symm (A x)‖[d,*]) '' {x | p x ≤ 1}) := by
  simp [primalDualOperatorNorm, p.closedBall_zero_eq]

end

section

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable (p : Seminorm ℝ E) [IsNorm p]
variable (d : Seminorm ℝ F) [FiniteDimensional ℝ F] [IsNorm d]

/-- Helper for Definition 2.32: the transported `d*`-norm of the slice `A x` is the support
function of the `d`-unit ball evaluated on that slice. -/
private theorem dualNorm_slice_eq_sSup_pairing
    (A : E →ₗ[ℝ] StrongDual ℝ F) (x : E) :
    ‖(toDual ℝ F).symm (A x)‖[d,*] =
      sSup ((fun u : F ↦ A x u) '' {u | d u ≤ 1}) := by
  -- Rewrite the transported dual norm through the support-function formula on the `d`-unit ball.
  simpa [InnerProductSpace.toDual_symm_apply] using
    (Seminorm.dualNorm_apply d ((toDual ℝ F).symm (A x)))

/-- Helper for Definition 2.32: every pairing value on the dual unit ball is bounded by the
corresponding slice dual norm. -/
private theorem pairing_le_dualNorm_slice
    (A : E →ₗ[ℝ] StrongDual ℝ F) (x : E) {u : F} (hu : d u ≤ 1) :
    A x u ≤ ‖(toDual ℝ F).symm (A x)‖[d,*] := by
  -- Convert the dual pairing into an inner product so the dual-norm estimate applies directly.
  calc
    A x u = inner ℝ ((toDual ℝ F).symm (A x)) u := by
      simp [InnerProductSpace.toDual_symm_apply]
    _ ≤ ‖(toDual ℝ F).symm (A x)‖[d,*] * d u :=
      Seminorm.inner_le_dualNorm_mul d u ((toDual ℝ F).symm (A x))
    _ ≤ ‖(toDual ℝ F).symm (A x)‖[d,*] * 1 := by
      have hdual_nonneg : 0 ≤ ‖(toDual ℝ F).symm (A x)‖[d,*] := by
        rw [Seminorm.dualNorm_apply]
        obtain ⟨C, hC_pos, hnorm_le⟩ := d.exists_norm_le_mul
        have himage_bdd :
            BddAbove
              ((fun v : F ↦ inner ℝ ((toDual ℝ F).symm (A x)) v) '' {v | d v ≤ 1}) := by
          refine ⟨‖(toDual ℝ F).symm (A x)‖ * C, ?_⟩
          rintro y ⟨v, hv, rfl⟩
          have hv_norm : ‖v‖ ≤ C := by
            calc
              ‖v‖ ≤ C * d v := hnorm_le v
              _ ≤ C * 1 := mul_le_mul_of_nonneg_left hv hC_pos.le
              _ = C := by ring
          calc
            inner ℝ ((toDual ℝ F).symm (A x)) v ≤
                ‖(toDual ℝ F).symm (A x)‖ * ‖v‖ := real_inner_le_norm _ _
            _ ≤ ‖(toDual ℝ F).symm (A x)‖ * C :=
              mul_le_mul_of_nonneg_left hv_norm (norm_nonneg _)
        exact le_csSup
          himage_bdd
          ⟨0, by simp, by simp⟩
      exact mul_le_mul_of_nonneg_left hu hdual_nonneg
    _ = ‖(toDual ℝ F).symm (A x)‖[d,*] := by
      ring

/-- Helper for Definition 2.32: the global product-image of the dual pairing over the primal and
dual unit balls is bounded above. -/
private theorem bddAbove_dualPairingImage
    (A : E →ₗ[ℝ] StrongDual ℝ F) :
    BddAbove ((fun xu : E × F ↦ A xu.1 xu.2) '' Set.prod {x | p x ≤ 1} {u | d u ≤ 1}) := by
  have hT_bdd :
      BddAbove ((fun x : E ↦ ‖(toDual ℝ F).symm (A x)‖[d,*]) '' {x | p x ≤ 1}) := by
    -- Reuse the boundedness of the defining operator-norm image.
    simpa [p.closedBall_zero_eq] using
      (bddAbove_primalDualOperatorNormImage (p := p) (d := d) A)
  refine ⟨sSup ((fun x : E ↦ ‖(toDual ℝ F).symm (A x)‖[d,*]) '' {x | p x ≤ 1}), ?_⟩
  rintro y ⟨⟨x, u⟩, hxu, rfl⟩
  rcases hxu with ⟨hx, hu⟩
  have hpair : A x u ≤ ‖(toDual ℝ F).symm (A x)‖[d,*] :=
    pairing_le_dualNorm_slice (d := d) A x hu
  have hslicemem :
      ‖(toDual ℝ F).symm (A x)‖[d,*] ∈
        ((fun x : E ↦ ‖(toDual ℝ F).symm (A x)‖[d,*]) '' {x | p x ≤ 1}) := by
    exact ⟨x, hx, rfl⟩
  exact hpair.trans (le_csSup hT_bdd hslicemem)

/-- Helper for Definition 2.32: for a fixed primal point in the unit ball, the corresponding slice
support function is bounded by the global two-ball pairing supremum. -/
private theorem slice_sSup_le_global_dualPairing
    (A : E →ₗ[ℝ] StrongDual ℝ F) {x : E} (hx : p x ≤ 1) :
    sSup ((fun u : F ↦ A x u) '' {u | d u ≤ 1}) ≤
      sSup ((fun xu : E × F ↦ A xu.1 xu.2) '' Set.prod {x | p x ≤ 1} {u | d u ≤ 1}) := by
  have hS_bdd := bddAbove_dualPairingImage (p := p) (d := d) A
  have hslice_nonempty : ((fun u : F ↦ A x u) '' {u | d u ≤ 1}).Nonempty := by
    -- The zero vector lies in the dual unit ball, so each slice image is nonempty.
    exact ⟨A x 0, ⟨0, by simp, rfl⟩⟩
  refine csSup_le hslice_nonempty ?_
  rintro y ⟨u, hu, rfl⟩
  -- Embed each slice value into the global product image at the same `(x,u)`.
  exact le_csSup hS_bdd ⟨(x, u), ⟨hx, hu⟩, rfl⟩

/-- Expanding `d.dualNorm` inside `‖A‖[p ⇀ d,*]` yields the intrinsic two-ball dual-pairing
formula. -/
-- Proof sketch: unfold `primalDualOperatorNorm` and `Seminorm.dualNorm`, rewrite the inner
-- product via `toDual_symm_apply`, and identify the iterated supremum with the supremum over the
-- product set.
theorem primalDualOperatorNorm_eq_sSup_dualPairing (A : E →ₗ[ℝ] StrongDual ℝ F) :
    ‖A‖[p ⇀ d,*] =
      sSup ((fun xu : E × F ↦ A xu.1 xu.2) ''
        Set.prod {x | p x ≤ 1} {u | d u ≤ 1}) := by
  rw [primalDualOperatorNorm_def]
  set T : Set ℝ := ((fun x : E ↦ ‖(toDual ℝ F).symm (A x)‖[d,*]) '' {x | p x ≤ 1}) with hTdef
  set S : Set ℝ := ((fun xu : E × F ↦ A xu.1 xu.2) '' Set.prod {x | p x ≤ 1} {u | d u ≤ 1})
    with hSdef
  have hT_bdd : BddAbove T := by
    -- The defining image for `‖A‖[p ⇀ d,*]` is already known to be bounded above.
    simpa [hTdef, p.closedBall_zero_eq] using
      (bddAbove_primalDualOperatorNormImage (p := p) (d := d) A)
  have hS_bdd : BddAbove S := by
    -- Transfer boundedness from slice norms to the global pairing image.
    simpa [hSdef] using (bddAbove_dualPairingImage (p := p) (d := d) A)
  have hT_nonempty : T.Nonempty := by
    -- The primal unit ball contains `0`, so the defining image is nonempty.
    rw [hTdef]
    exact ⟨‖(toDual ℝ F).symm (A 0)‖[d,*], ⟨0, by simp, rfl⟩⟩
  have hS_nonempty : S.Nonempty := by
    -- The product of the two unit balls also contains `(0,0)`.
    rw [hSdef]
    exact ⟨A 0 0, ⟨(0, 0), ⟨by simp, by simp⟩, rfl⟩⟩
  have hT_le : sSup T ≤ sSup S := by
    refine csSup_le hT_nonempty ?_
    rintro y hy
    rw [hTdef] at hy
    rcases hy with ⟨x, hx, rfl⟩
    -- Rewrite the slice norm as a slice supremum and compare that slice with the global image.
    change ‖(toDual ℝ F).symm (A x)‖[d,*] ≤ sSup S
    rw [dualNorm_slice_eq_sSup_pairing (d := d) A x]
    simpa [hSdef] using
      (slice_sSup_le_global_dualPairing (p := p) (d := d) A hx)
  have hS_le : sSup S ≤ sSup T := by
    refine csSup_le hS_nonempty ?_
    rintro y hy
    rw [hSdef] at hy
    rcases hy with ⟨⟨x, u⟩, hxu, rfl⟩
    rcases hxu with ⟨hx, hu⟩
    have hpair : A x u ≤ ‖(toDual ℝ F).symm (A x)‖[d,*] :=
      pairing_le_dualNorm_slice (d := d) A x hu
    have hslicemem : ‖(toDual ℝ F).symm (A x)‖[d,*] ∈ T := by
      rw [hTdef]
      exact ⟨x, hx, rfl⟩
    -- Each product-point value is bounded by its slice norm, which already lies in `T`.
    exact hpair.trans (le_csSup hT_bdd hslicemem)
  exact le_antisymm hT_le hS_le

/-- Composing an `F`-valued linear map with `InnerProductSpace.toDual` recovers the textbook
inner-product formula for `‖(toDual ℝ F).toLinearMap.comp A‖[p ⇀ d,*]`. -/
theorem primalDualOperatorNorm_toDual_eq_sSup_pairing (A : E →ₗ[ℝ] F) :
    ‖(toDual ℝ F).toLinearMap.comp A‖[p ⇀ d,*] =
      sSup ((fun xu : E × F ↦ inner ℝ (A xu.1) xu.2) ''
        Set.prod {x | p x ≤ 1} {u | d u ≤ 1}) := by
  simpa [toDual_apply_apply] using
    primalDualOperatorNorm_eq_sSup_dualPairing p d ((toDual ℝ F).toLinearMap.comp A)

end

end Seminorm

namespace Seminorm

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- In the ambient-norm case, `primalDualOperatorNorm` is the ordinary operator norm of the
associated continuous linear map into `StrongDual ℝ F`. This is the canonical
stronger-assumption bridge from the source-facing owner to `ContinuousLinearMap.opNorm`. -/
theorem primalDualOperatorNorm_normSeminorm_eq_opNorm (A : E →ₗ[ℝ] StrongDual ℝ F) :
    ‖A‖[normSeminorm ℝ E ⇀ normSeminorm ℝ F,*] =
      ‖A.toContinuousLinearMap‖ := by
  have hball_fun : (normSeminorm ℝ E).closedBall = Metric.closedBall := closedBall_normSeminorm ℝ E
  have hball : (normSeminorm ℝ E).closedBall 0 1 = Metric.closedBall (0 : E) 1 := by
    simp [hball_fun]
  simpa [primalDualOperatorNorm, hball, dualNorm_normSeminorm_eq_norm] using
    A.toContinuousLinearMap.sSup_unitClosedBall_eq_norm

/-- For an `F`-valued linear map, composing with `InnerProductSpace.toDual` turns the ambient-norm
specialization into the ordinary operator norm. -/
theorem primalDualOperatorNorm_toDual_normSeminorm_eq_opNorm (A : E →ₗ[ℝ] F) :
    ‖(toDual ℝ F).toLinearMap.comp A‖[normSeminorm ℝ E ⇀ normSeminorm ℝ F,*] =
      ‖A.toContinuousLinearMap‖ := by
  rw [primalDualOperatorNorm_normSeminorm_eq_opNorm]
  change ‖(toDual ℝ F).toContinuousLinearMap.comp A.toContinuousLinearMap‖ =
      ‖A.toContinuousLinearMap‖
  exact (toDual ℝ F).toLinearIsometry.norm_toContinuousLinearMap_comp

end Seminorm

namespace Matrix

variable {m n : ℕ}

/-- For a matrix `A`, composing the Euclidean realization `A.toEuclideanLin` with
`InnerProductSpace.toDual` yields the canonical dual-valued operator whose
`Seminorm.primalDualOperatorNorm` is the ordinary operator norm. -/
theorem toEuclideanLin_toDual_primalDualOperatorNorm_eq_opNorm
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖(toDual ℝ (EuclideanSpace ℝ (Fin m))).toLinearMap.comp A.toEuclideanLin‖[
        normSeminorm ℝ (EuclideanSpace ℝ (Fin n)) ⇀
          normSeminorm ℝ (EuclideanSpace ℝ (Fin m)),*] =
      ‖A.toEuclideanLin.toContinuousLinearMap‖ := by
  simpa using Seminorm.primalDualOperatorNorm_toDual_normSeminorm_eq_opNorm A.toEuclideanLin

/-- The same Euclidean matrix specialization, after composing with `InnerProductSpace.toDual`, can
be read directly as the canonical matrix `ℓ₂`-operator norm. -/
theorem toEuclideanLin_toDual_primalDualOperatorNorm_eq_l2_opNorm
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖(toDual ℝ (EuclideanSpace ℝ (Fin m))).toLinearMap.comp A.toEuclideanLin‖[
        normSeminorm ℝ (EuclideanSpace ℝ (Fin n)) ⇀
          normSeminorm ℝ (EuclideanSpace ℝ (Fin m)),*] =
      ‖A‖ := by
  simpa [Matrix.l2_opNorm_def] using toEuclideanLin_toDual_primalDualOperatorNorm_eq_opNorm A

end Matrix

end

/-! ### Proposition_2_32 (from Chap02) -/
open scoped BigOperators

section

/- Primary domain: scalar logarithmic bounds for accumulated internal iteration counts.

Owner abstractions sampled before refining:
* project `accuracyStoppingIndex_le_one_add_sqrt_condition_log_ratio` in `Lemma_2_28.lean`, the
  one-step logarithmic owner bound used immediately downstream with the same log-ratio term;
* mathlib `Real.log_div`, the canonical logarithm identity turning ratios into additive
  telescoping terms;
* mathlib `Finset.sum_range_sub'`, the canonical telescoping-sum owner on `Finset.range`;
* mathlib `Finset.sum_le_sum`, the canonical accumulation of termwise upper bounds.

Best owner abstraction:
* source-facing/core: `sum_le_of_log_ratio_step_bounds`

Primitive data:
* the positive stage sequence `Δ`;
* the internal-cost sequence `j`;
* the one-step logarithmic upper bound on each `j k`.

Derived API:
* the helper telescoping identity `sum_range_log_div_eq_log_div`;
* the accumulated logarithmic estimate `sum_le_of_log_ratio_step_bounds`.

Source/core/bridge triage:
* source-facing: Proposition 2.32, the accumulated bound for `∑_{k=0}^N j(k)`;
* core/canonical: `sum_le_of_log_ratio_step_bounds`;
* bridge/view: the helper telescoping lemma `sum_range_log_div_eq_log_div`.
-/

/-- Helper for Proposition 2.32: positive consecutive ratios telescope after taking logarithms. -/
theorem sum_range_log_div_eq_log_div
    (N : ℕ) (Δ : ℕ → ℝ) (hΔ_pos : ∀ k ≤ N + 1, 0 < Δ k) :
    Finset.sum (Finset.range (N + 1)) (fun k ↦ Real.log (Δ k / Δ (k + 1))) =
      Real.log (Δ 0 / Δ (N + 1)) := by
  calc
    Finset.sum (Finset.range (N + 1)) (fun k ↦ Real.log (Δ k / Δ (k + 1))) =
        Finset.sum (Finset.range (N + 1)) (fun k ↦ Real.log (Δ k) - Real.log (Δ (k + 1))) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          simpa using
            (Real.log_div
              (hΔ_pos k (Nat.le_trans (Nat.le_of_lt_succ <| Finset.mem_range.mp hk) <|
                Nat.le_succ N)).ne'
              (hΔ_pos (k + 1) (Nat.succ_le_succ <| Nat.le_of_lt_succ <|
                Finset.mem_range.mp hk)).ne')
    _ = Real.log (Δ 0) - Real.log (Δ (N + 1)) := by
          simpa using Finset.sum_range_sub' (fun k ↦ Real.log (Δ k)) (N + 1)
    _ = Real.log (Δ 0 / Δ (N + 1)) := by
          symm
          simpa using
            (Real.log_div (hΔ_pos 0 <| Nat.zero_le (N + 1)).ne' (hΔ_pos (N + 1) <|
              Nat.le_refl _).ne')

/-- Proposition 2.32: if each internal cost `j(k)` satisfies the one-step logarithmic bound
`j(k) ≤ 1 + √Q_f log (2 (L - μ) / (κ μ)) + √Q_f log (Δ_k / Δ_{k+1})`, then summing from
`k = 0` to `N` yields
`∑_{k=0}^N j(k) ≤ (N + 1) * (1 + √Q_f log (2 (L - μ) / (κ μ))) + √Q_f log (Δ_0 / Δ_{N+1})`. -/
theorem sum_le_of_log_ratio_step_bounds
    (N : ℕ) (j Δ : ℕ → ℝ) (Qf L μ κ : ℝ)
    (hΔ_pos : ∀ k ≤ N + 1, 0 < Δ k)
    (hj_bound : ∀ k ≤ N,
      j k ≤ 1 + Real.sqrt Qf * Real.log (2 * (L - μ) / (κ * μ)) +
        Real.sqrt Qf * Real.log (Δ k / Δ (k + 1))) :
    Finset.sum (Finset.range (N + 1)) j ≤
      (N + 1 : ℝ) * (1 + Real.sqrt Qf * Real.log (2 * (L - μ) / (κ * μ))) +
        Real.sqrt Qf * Real.log (Δ 0 / Δ (N + 1)) := by
  let c : ℝ := 1 + Real.sqrt Qf * Real.log (2 * (L - μ) / (κ * μ))
  calc
    Finset.sum (Finset.range (N + 1)) j ≤
        Finset.sum (Finset.range (N + 1))
          (fun k ↦ c + Real.sqrt Qf * Real.log (Δ k / Δ (k + 1))) := by
            refine Finset.sum_le_sum ?_
            intro k hk
            exact hj_bound k <| Nat.le_of_lt_succ <| Finset.mem_range.mp hk
    _ = Finset.sum (Finset.range (N + 1)) (fun _ ↦ c) +
          Finset.sum (Finset.range (N + 1))
            (fun k ↦ Real.sqrt Qf * Real.log (Δ k / Δ (k + 1))) := by
            rw [Finset.sum_add_distrib]
    _ = (N + 1 : ℝ) * c +
          Finset.sum (Finset.range (N + 1))
            (fun k ↦ Real.sqrt Qf * Real.log (Δ k / Δ (k + 1))) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            simp
    _ = (N + 1 : ℝ) * c +
          Real.sqrt Qf *
            Finset.sum (Finset.range (N + 1)) (fun k ↦ Real.log (Δ k / Δ (k + 1))) := by
            rw [← Finset.mul_sum]
    _ = (N + 1 : ℝ) * c + Real.sqrt Qf * Real.log (Δ 0 / Δ (N + 1)) := by
            rw [sum_range_log_div_eq_log_div N Δ hΔ_pos]
    _ = (N + 1 : ℝ) * (1 + Real.sqrt Qf * Real.log (2 * (L - μ) / (κ * μ))) +
          Real.sqrt Qf * Real.log (Δ 0 / Δ (N + 1)) := by
            simp [c]

end

/-! ### Theorem_2_32 (from Chap02) -/
/-
Primary domain: constrained minimization for strongly convex functions on finite-dimensional real
normed spaces.

Sampled owner-style declarations:
* project `StrongConvexOnWith` in `Definition_2_14`
* project `StrongConvexOnWith.exists_pos_strongConvexOn` in `Definition_2_14`
* project `StrongConvexOnWith.existsUnique_isMinOn_of_isClosed` in `Definition_2_14`
* project `StrongConvexOn.existsUnique_isMinOn_of_isClosed` in `Theorem_3_45`

Best owner abstraction:
* source-facing/core: `StrongConvexOnWith p μ Q f`

Primitive data:
* the normed seminorm `p`
* the feasible set `Q`
* the objective `f`
* the owner predicate `StrongConvexOnWith p μ Q f`

Derived API:
* `StrongConvexOnWith.exists_pos_strongConvexOn`, the bridge to Euclidean `StrongConvexOn`
* `StrongConvexOnWith.existsUnique_isMinOn_of_isClosed`, the owner unique-minimizer theorem
* `StrongConvexOn.existsUnique_isMinOn_of_isClosed`, the lower-level Euclidean theorem used by the
  bridge

Source/core/bridge triage:
* source-facing: the unique constrained minimizer conclusion for the textbook arbitrary-norm
  hypothesis
* core/canonical: `StrongConvexOnWith.existsUnique_isMinOn_of_isClosed`
* bridge/view: the internal passage through `StrongConvexOnWith.exists_pos_strongConvexOn`

This numbered theorem is direct owner API for `StrongConvexOnWith`, so the declaration now lives
with the rest of that owner in `Definition_2_14`. This file is recall-only and keeps no parallel
theorem shell.
-/

/- Theorem 2.32 is the direct owner recall of the closed-set unique-minimizer theorem for
`StrongConvexOnWith`. -/
recall StrongConvexOnWith.existsUnique_isMinOn_of_isClosed
