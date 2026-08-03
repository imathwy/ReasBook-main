import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import BauschkeLean.Chap23.Proposition_23_29
import BauschkeLean.Chap23.Corollary_23_46

-- Semantic recall note: `lean_leansearch` only surfaced unrelated algebra-spectrum resolvent
-- results, so this item follows the verified local Chapter 23 owners
-- `resolventMap A hA γ`, `minimalNormValue`, and `IsAtMostSingleValued`.

open scoped Pointwise SetValuedOperator
open ERealFunction

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: Remark 23.47 records the first-order small-`γ` expansion of the resolvent.
- `core/canonical`: the Chapter 23 owner for the point value of `A x` is `A⁰[hA, hx]`.
- `bridge/view`: under `A.IsAtMostSingleValued`, part (3) is expressed using an explicit element
  `u ∈ A x`, avoiding a public choice-built witness while still matching the textbook
  single-valued formula. -/

/-- For a maximally monotone at-most-single-valued operator, every element of the value set at a
domain point coincides with the least-norm value `{}^0 A x`. -/
theorem eq_minimalNormValue_of_mem_of_maximal_of_isAtMostSingleValued
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A)
    (hsingle : A.IsAtMostSingleValued) {x u : H} (hx : x ∈ A.dom) (hu : u ∈ A x) :
    u = A⁰[hA, hx] := by
  -- Both points lie in the same subsingleton fiber `A x`.
  exact (hsingle x) hu (minimalNormValue_mem_of_maximal_of_mem_dom hA hx)

/-- Helper for Remark 23.47: at a fixed parameter `γ`, the normalized resolvent error equals the
difference between the least-norm value `{}^0 A x` and the Yosida value `{}^[γ] A x`. -/
private theorem inv_smul_resolventError_eq_minimalNormValue_sub_yosidaApproximationMap
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) {x : H} (hx : x ∈ A.dom)
    (γ : PosReal) :
    (γ : ℝ)⁻¹ • (resolventMap A hA γ x - (x - (γ : ℝ) • A⁰[hA, hx])) =
      A⁰[hA, hx] - yosidaApproximationMap A hA γ x := by
  let a : H := A⁰[hA, hx]
  -- Route correction: use Proposition 23.29's canonical scaled-resolvent identity
  -- instead of rebuilding the resolvent/Yosida singleton graph equation locally.
  have hinv :
      (γ : ℝ)⁻¹ • resolventMap A hA γ x =
        (γ : ℝ)⁻¹ • x - yosidaApproximationMap A hA γ x := by
    simpa using
      congrFun (inv_smul_resolventMap_eq_inv_smul_id_sub_yosidaApproximationMap hA γ) x
  calc
    (γ : ℝ)⁻¹ • (resolventMap A hA γ x - (x - (γ : ℝ) • a))
        = (γ : ℝ)⁻¹ • resolventMap A hA γ x -
            ((γ : ℝ)⁻¹ • x - a) := by
            rw [smul_sub, smul_sub, inv_smul_smul₀ (ne_of_gt γ.2)]
    _ = ((γ : ℝ)⁻¹ • x - yosidaApproximationMap A hA γ x) -
          ((γ : ℝ)⁻¹ • x - a) := by
            rw [hinv]
    _ = a - yosidaApproximationMap A hA γ x := by
          exact
            sub_sub_sub_cancel_left (yosidaApproximationMap A hA γ x) a ((γ : ℝ)⁻¹ • x)

/-- Remark 23.47 (1): if `A : H → 2^H` is maximally monotone and `x ∈ dom A`, then the scaled
resolvent error
`(γ : ℝ)⁻¹ • (resolventMap A hA γ x - (x - (γ : ℝ) • A⁰[hA, hx]))` tends to `0` as
`γ ↓ 0` through `]0,1[`. -/
theorem tendsto_inv_smul_resolventMap_sub_sub_smul_minimalNormValue_atZeroRight_of_mem_dom
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) {x : H} (hx : x ∈ A.dom) :
    Filter.Tendsto
      (fun γ : PosReal ↦
        (γ : ℝ)⁻¹ • (resolventMap A hA γ x - (x - (γ : ℝ) • A⁰[hA, hx])))
      atZeroRightWithinUnitInterval
      (nhds (0 : H)) := by
  -- Corollary 23.46 gives convergence of the Yosida realizer to the least-norm value.
  have hconst :
      Filter.Tendsto (fun _ : PosReal ↦ A⁰[hA, hx]) atZeroRightWithinUnitInterval
        (nhds (A⁰[hA, hx])) :=
    tendsto_const_nhds
  have hsub :
      Filter.Tendsto (fun γ : PosReal ↦ A⁰[hA, hx] - yosidaApproximationMap A hA γ x)
        atZeroRightWithinUnitInterval
        (nhds (0 : H)) := by
    simpa using
      hconst.sub
        (tendsto_yosidaApproximationMap_atZeroRight_to_minimalNormValue_of_mem_dom hA hx)
  refine Filter.Tendsto.congr' ?_ hsub
  exact Filter.Eventually.of_forall fun γ =>
    (inv_smul_resolventError_eq_minimalNormValue_sub_yosidaApproximationMap hA hx γ).symm

/-- Remark 23.47 (2): if `A : H → 2^H` is maximally monotone, at most single-valued, and
`x ∈ dom A`, then the domain value `A x` is the singleton `{A⁰[hA, hx]}`. -/
theorem value_eq_singleton_minimalNormValue_of_maximal_of_mem_dom_of_isAtMostSingleValued
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A)
    (hsingle : A.IsAtMostSingleValued) {x : H} (hx : x ∈ A.dom) :
    A x = ({A⁰[hA, hx]} : Set H) := by
  -- The least-norm value belongs to `A x`, and the fiber is subsingleton.
  exact (hsingle x).eq_singleton_of_mem (minimalNormValue_mem_of_maximal_of_mem_dom hA hx)

/-- Helper for Remark 23.47: the inverse-scaled resolvent error is little-`o` of `1` at
`γ ↓ 0` along the unit interval. -/
private theorem scaledResolventError_isLittleO_one_atZeroRight_of_mem_dom
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) {x : H} (hx : x ∈ A.dom) :
    (fun γ : PosReal ↦
      (γ : ℝ)⁻¹ • (resolventMap A hA γ x - (x - (γ : ℝ) • A⁰[hA, hx])))
      =o[atZeroRightWithinUnitInterval] (fun _ : PosReal ↦ (1 : ℝ)) := by
  -- Convert the already-proved convergence of the scaled error to the canonical `=o 1` form.
  rw [Asymptotics.isLittleO_one_iff ℝ]
  simpa using
    tendsto_inv_smul_resolventMap_sub_sub_smul_minimalNormValue_atZeroRight_of_mem_dom hA hx

/-- Remark 23.47 (3): if `A : H → 2^H` is maximally monotone, at most single-valued, and
`x ∈ dom A`, then for any `u ∈ A x` the resolvent expansion can be written as
`resolventMap A hA γ x = x - (γ : ℝ) • u + o(γ)` at `γ ↓ 0`;
by part (2), such a `u` is exactly the unique value of `A x`. -/
theorem resolventMap_error_isLittleO_atZeroRight_of_mem_dom_of_isAtMostSingleValued
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A)
    (hsingle : A.IsAtMostSingleValued) {x u : H} (hx : x ∈ A.dom) (hu : u ∈ A x) :
    (fun γ : PosReal ↦
      resolventMap A hA γ x - (x - (γ : ℝ) • u))
      =o[atZeroRightWithinUnitInterval]
        (fun γ : PosReal ↦ (γ : ℝ)) := by
  -- Rewrite the explicit value `u` to the canonical least-norm value before packaging
  -- the inverse-scaled convergence as a little-`o` statement.
  have hu_eq : u = A⁰[hA, hx] :=
    eq_minimalNormValue_of_mem_of_maximal_of_isAtMostSingleValued hA hsingle hx hu
  rw [hu_eq]
  let error : PosReal → H :=
    fun γ ↦ resolventMap A hA γ x - (x - (γ : ℝ) • A⁰[hA, hx])
  let parameter : PosReal → ℝ := fun γ ↦ (γ : ℝ)
  let scaled : PosReal → H := fun γ ↦ (parameter γ)⁻¹ • error γ
  have hlittle :
      scaled =o[atZeroRightWithinUnitInterval] (fun _ : PosReal ↦ (1 : ℝ)) := by
    -- Repackage the scaled convergence via the ordinary normed-space `=o 1` equivalence.
    simpa [scaled, error, parameter] using
      scaledResolventError_isLittleO_one_atZeroRight_of_mem_dom hA hx
  have hsmul :
      (fun γ : PosReal ↦ parameter γ • scaled γ)
        =o[atZeroRightWithinUnitInterval]
          (fun γ : PosReal ↦ parameter γ • (1 : ℝ)) :=
    (Asymptotics.isBigO_refl parameter atZeroRightWithinUnitInterval).smul_isLittleO hlittle
  -- Multiplying the `o(1)` scaled error by `γ` recovers the original `o(γ)` resolvent error.
  refine hsmul.congr' ?_ ?_
  · exact Filter.Eventually.of_forall fun γ => by
      dsimp [scaled, error, parameter]
      rw [smul_inv_smul₀ (ne_of_gt γ.2)]
  · exact Filter.Eventually.of_forall fun γ => by
      simp [parameter]

end SetValuedOperator
