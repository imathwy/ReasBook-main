import BauschkeLean.Chap23.Corollary_23_11
import BauschkeLean.Chap23.Definition_23_42
import BauschkeLean.Chap23.Proposition_23_7

-- Semantic recall note: `lean_leansearch` surfaced only general minimal-norm projection lemmas,
-- not the Chapter 23 set-valued Yosida/minimal-norm API, so this file follows the verified
-- local owners `yosidaApproximationMap`, `minimalNormValue`, and the additive parameter surface
-- `γ + μ`.

open scoped Pointwise SetValuedOperator
open ERealFunction

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: Proposition 23.43 compares the norms of the canonical Yosida values at a fixed
  domain point and bounds them by the least norm occurring in the value set `A x`.
- `core/canonical`: the chapter owner for that least-norm value is `A⁰[hA, hx]`.
- `bridge/view`: the textbook infimum surface `sInf (Set.image (fun u ↦ ‖u‖) (A x))` is the
  corresponding norm of `A⁰[hA, hx]`. -/

/-- Helper for Proposition 23.43: every value `u ∈ A x` bounds the norm of the canonical Yosida
value at `x` through the squared inner-product estimate
`‖{}^[γ] A x‖ ^ 2 ≤ ⟪{}^[γ] A x, u⟫`. -/
private theorem norm_sq_yosidaApproximationMap_le_inner_of_mem
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) (γ : PosReal) {x u : H}
    (hu : u ∈ A x) :
    ‖yosidaApproximationMap A hA γ x‖ ^ 2 ≤ inner ℝ (yosidaApproximationMap A hA γ x) u := by
  let p := yosidaApproximationMap A hA γ x
  -- Route correction: use the source proof's single monotonicity step on graph points instead of
  -- the older cocoercive normalization route.
  have hp_mem : p ∈ ({}^[γ] A) x := by
    rw [yosidaApproximation_eq_singleton_yosidaApproximationMap_of_maximal A hA γ x]
    simp [p]
  have hp_graph : (x - (γ : ℝ) • p, p) ∈ gra A :=
    (mem_yosidaApproximation_iff_mem_graph A γ x p).1 hp_mem
  have hu_graph : (x, u) ∈ gra A := by
    simpa [SetValuedOperator.mem_graph] using hu
  have hmono :
      0 ≤ inner ℝ ((x - (γ : ℝ) • p) - x) (p - u) :=
    (isMonotone_iff A).1 hA.1 hp_graph hu_graph
  have hsq : ‖p‖ ^ 2 ≤ inner ℝ p u := by
    have hmono' : 0 ≤ inner ℝ (-((γ : ℝ) • p)) (p - u) := by
      have hsub : ((x - (γ : ℝ) • p) - x) = -((γ : ℝ) • p) := by
        abel_nf
      rw [hsub] at hmono
      exact hmono
    have hineq : 0 ≤ (γ : ℝ) * (inner ℝ p u - ‖p‖ ^ 2) := by
      calc
        0 ≤ inner ℝ (-((γ : ℝ) • p)) (p - u) := hmono'
        _ = (γ : ℝ) * (inner ℝ p u - ‖p‖ ^ 2) := by
              rw [inner_neg_left, real_inner_smul_left, inner_sub_right,
                real_inner_self_eq_norm_sq, real_inner_comm]
              ring
    have hdiff : 0 ≤ inner ℝ p u - ‖p‖ ^ 2 := by
      exact nonneg_of_mul_nonneg_right (by simpa [mul_comm] using hineq) γ.2
    exact sub_nonneg.mp hdiff
  simpa [p] using hsq

/-- Helper for Proposition 23.43: every value `u ∈ A x` bounds the norm of the canonical Yosida
value at `x`. -/
private theorem norm_yosidaApproximationMap_le_norm_of_mem
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) (γ : PosReal) {x u : H}
    (hu : u ∈ A x) :
    ‖yosidaApproximationMap A hA γ x‖ ≤ ‖u‖ := by
  have hsq := norm_sq_yosidaApproximationMap_le_inner_of_mem hA γ hu
  -- Cauchy--Schwarz turns the quadratic inequality into the desired norm comparison.
  by_cases hp : yosidaApproximationMap A hA γ x = 0
  · rw [hp]
    simp
  · have hp_pos : 0 < ‖yosidaApproximationMap A hA γ x‖ := norm_pos_iff.mpr hp
    have hprod :
        ‖yosidaApproximationMap A hA γ x‖ * ‖yosidaApproximationMap A hA γ x‖
          ≤ ‖u‖ * ‖yosidaApproximationMap A hA γ x‖ := by
      calc
        ‖yosidaApproximationMap A hA γ x‖ * ‖yosidaApproximationMap A hA γ x‖
            = ‖yosidaApproximationMap A hA γ x‖ ^ 2 := by
                rw [pow_two]
        _ ≤ inner ℝ (yosidaApproximationMap A hA γ x) u := hsq
        _ ≤ ‖yosidaApproximationMap A hA γ x‖ * ‖u‖ := real_inner_le_norm _ _
        _ = ‖u‖ * ‖yosidaApproximationMap A hA γ x‖ := by ring
    exact le_of_mul_le_mul_right (by simpa [pow_two] using hprod) hp_pos

/-- Helper for Proposition 23.43: iterating the Yosida realizer at parameters `γ` and `μ`
produces the same point as the single Yosida realizer at parameter `γ + μ`. -/
private theorem yosidaApproximationMap_iterated_eq_add
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) (γ μ : PosReal) (x : H) :
    yosidaApproximationMap ({}^[γ] A) (yosidaApproximation_isMaximallyMonotone A hA γ) μ x =
      yosidaApproximationMap A hA (γ + μ) x := by
  -- Rewrite one canonical iterated Yosida point into the singleton-valued `γ + μ` surface.
  have hmem :
      yosidaApproximationMap ({}^[γ] A) (yosidaApproximation_isMaximallyMonotone A hA γ) μ x ∈
        ({}^[(γ + μ)] A) x := by
    have hmemIter :
        yosidaApproximationMap ({}^[γ] A) (yosidaApproximation_isMaximallyMonotone A hA γ) μ x ∈
          ({}^[μ] ({}^[γ] A)) x := by
      rw [yosidaApproximation_eq_singleton_yosidaApproximationMap_of_maximal
        ({}^[γ] A) (yosidaApproximation_isMaximallyMonotone A hA γ) μ x]
      simp
    have happly :
        ({}^[μ] ({}^[γ] A)) x = ({}^[(γ + μ)] A) x := by
      have hEq :=
        congrArg (fun B : SetValuedOperator H H ↦ B x)
          (yosidaApproximation_add_eq_iterated_yosidaApproximation A μ γ).symm
      simpa [add_comm] using hEq
    exact happly ▸ hmemIter
  rw [yosidaApproximation_eq_singleton_yosidaApproximationMap_of_maximal A hA (γ + μ) x] at hmem
  simpa using hmem

/-- Proposition 23.43 (1): if `A : H → 2^H` is maximally monotone, `γ ∈ ℝ_{++}`, and
`x ∈ dom A`, then the norm of the canonical single-valued Yosida value `{}^[γ] A` at `x`
is bounded above by `inf ‖A x‖`, realized as the `sInf` norm-image surface of the canonical
least-norm value. -/
theorem norm_yosidaApproximationMap_le_sInf_norm_image
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) (γ : PosReal) {x : H}
    (hx : x ∈ A.dom) :
    ‖yosidaApproximationMap A hA γ x‖ ≤ sInf (Set.image (fun u : H ↦ ‖u‖) (A x)) := by
  refine le_csInf ?_ ?_
  · exact ⟨‖A⁰[hA, hx]‖, ⟨A⁰[hA, hx], minimalNormValue_mem_of_maximal_of_mem_dom hA hx, rfl⟩⟩
  · rintro y ⟨u, hu, rfl⟩
    exact norm_yosidaApproximationMap_le_norm_of_mem hA γ hu

/-- Proposition 23.43 (2): if `A : H → 2^H` is maximally monotone, `γ, μ ∈ ℝ_{++}`, and
`x ∈ dom A`, then increasing the Yosida parameter from `γ` to `γ + μ` decreases the norm of the
canonical Yosida value at `x`. -/
theorem norm_yosidaApproximationMap_add_le_norm_yosidaApproximationMap
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) (γ μ : PosReal) {x : H}
    (hx : x ∈ A.dom) :
    ‖yosidaApproximationMap A hA (γ + μ) x‖ ≤ ‖yosidaApproximationMap A hA γ x‖ := by
  have hmem : yosidaApproximationMap A hA γ x ∈ ({}^[γ] A) x := by
    -- The `γ`-Yosida value is singleton-valued with center `yosidaApproximationMap A hA γ x`.
    rw [yosidaApproximation_eq_singleton_yosidaApproximationMap_of_maximal A hA γ x]
    simp
  have hbound :
      ‖yosidaApproximationMap ({}^[γ] A)
          (yosidaApproximation_isMaximallyMonotone A hA γ) μ x‖
        ≤ ‖yosidaApproximationMap A hA γ x‖ :=
    norm_yosidaApproximationMap_le_norm_of_mem
      (A := {}^[γ] A) (hA := yosidaApproximation_isMaximallyMonotone A hA γ) (γ := μ) hmem
  -- Route correction: rewrite the iterated Yosida realizer to the single parameter `γ + μ`.
  rw [← yosidaApproximationMap_iterated_eq_add (A := A) hA γ μ x]
  exact hbound

end SetValuedOperator
