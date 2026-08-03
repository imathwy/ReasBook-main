import BauschkeLean.Chap03.Definition_3_8
import BauschkeLean.Chap03.Theorem_3_16_1
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap20.Proposition_20_36

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

noncomputable section

/- Source/core/bridge triage:
- `source-facing`: Definition 23.42 introduces the textbook element `{}^0 A x`, the least-norm
  point of the value set `A x`.
- `core/canonical`: on a real Hilbert space, this is the metric projection of `0` onto the closed
  convex set `A x`.
- `bridge/view`: the argmin formulation is the source-facing specification of that projection. -/

private theorem value_isChebyshev_of_maximal_of_mem_dom
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) {x : H} (hx : x ∈ A.dom) :
    IsChebyshev (A x) :=
  isChebyshev_of_nonempty_isClosed_convex
    ((SetValuedOperator.mem_dom_iff A x).1 hx)
    (Maximal.value_isClosed hA x)
    (Maximal.value_convex hA x)

/-- Definition 23.42: for a maximally monotone operator `A` and `x ∈ A.dom`, the textbook symbol
`{}^0 A x` is the metric projection of `0` onto the closed convex value set `A x`, i.e. the
canonical element of `A x` having minimal norm. -/
noncomputable def minimalNormValue
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) {x : H} (hx : x ∈ A.dom) : H :=
  projectionPoint (A x) (value_isChebyshev_of_maximal_of_mem_dom hA hx) 0

/- Lean surface notation for the textbook least-norm value `{}^0 A x`. -/
scoped notation:max A:max "⁰[" hA:max ", " hx:max "]" =>
  SetValuedOperator.minimalNormValue A hA hx

/-- The element `A⁰[hA, hx]` is the best approximation of `0` from the value set `A x`. -/
theorem minimalNormValue_isBestApproximation_zero_of_maximal_of_mem_dom
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) {x : H} (hx : x ∈ A.dom) :
    IsBestApproximation (0 : H) (A x) (A⁰[hA, hx]) := by
  simpa [minimalNormValue] using
    projectionPoint_isBestApproximation (A x)
      (value_isChebyshev_of_maximal_of_mem_dom hA hx) (0 : H)

/-- The least-norm value `A⁰[hA, hx]` belongs to `A x`. -/
@[simp] theorem minimalNormValue_mem_of_maximal_of_mem_dom
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) {x : H} (hx : x ∈ A.dom) :
    A⁰[hA, hx] ∈ A x :=
  (minimalNormValue_isBestApproximation_zero_of_maximal_of_mem_dom hA hx).1

/-- The least-norm value belongs to the canonical argmin set of the norm on `A x`. -/
theorem minimalNormValue_mem_argmin_norm_of_maximal_of_mem_dom
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) {x : H} (hx : x ∈ A.dom) :
    A⁰[hA, hx] ∈ Argmin[A x] (fun v : H ↦ ((‖v‖ : ℝ) : EReal)) := by
  refine ERealFunction.mem_argminOn_iff.mpr
    ⟨minimalNormValue_mem_of_maximal_of_mem_dom hA hx, ?_⟩
  rw [isMinOn_iff]
  intro y hy
  have hbest :=
    minimalNormValue_isBestApproximation_zero_of_maximal_of_mem_dom hA hx
  have hy_dist : dist (0 : H) (A⁰[hA, hx]) ≤ dist (0 : H) y := by
    rw [hbest.2]
    exact Metric.infDist_le_dist_of_mem hy
  exact_mod_cast (by simpa [dist_eq_norm] using hy_dist)

/-- A point lies in the argmin set of the norm on `A x` exactly when it is the least-norm value
`A⁰[hA, hx]`. -/
theorem mem_argmin_norm_iff_eq_minimalNormValue_of_maximal_of_mem_dom
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) {x u : H} (hx : x ∈ A.dom) :
    u ∈ Argmin[A x] (fun v : H ↦ ((‖v‖ : ℝ) : EReal)) ↔ u = A⁰[hA, hx] := by
  constructor
  · intro hu
    rcases ERealFunction.mem_argminOn_iff.mp hu with ⟨hu_mem, hu_min⟩
    have hu_best : IsBestApproximation (0 : H) (A x) u := by
      refine ⟨hu_mem, le_antisymm ?_ (Metric.infDist_le_dist_of_mem hu_mem)⟩
      exact (Metric.le_infDist ⟨u, hu_mem⟩).2 fun y hy ↦ by
        rw [isMinOn_iff] at hu_min
        have hy_dist : ((dist (0 : H) u : ℝ) : EReal) ≤ ((dist (0 : H) y : ℝ) : EReal) := by
          simpa [dist_eq_norm] using hu_min y hy
        exact_mod_cast hy_dist
    exact eq_projectionPoint_of_isBestApproximation (A x)
      (value_isChebyshev_of_maximal_of_mem_dom hA hx) hu_best
  · intro hu
    rw [hu]
    exact minimalNormValue_mem_argmin_norm_of_maximal_of_mem_dom hA hx

/-- The argmin set of the norm on `A x` is the singleton containing the least-norm value. -/
theorem argmin_norm_eq_singleton_minimalNormValue_of_maximal_of_mem_dom
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) {x : H} (hx : x ∈ A.dom) :
    Argmin[A x] (fun v : H ↦ ((‖v‖ : ℝ) : EReal)) = ({A⁰[hA, hx]} : Set H) := by
  ext u
  rw [Set.mem_singleton_iff, mem_argmin_norm_iff_eq_minimalNormValue_of_maximal_of_mem_dom hA hx]

/-- Definition 23.42: if `A` is maximally monotone and `x ∈ dom A`, then the textbook symbol
`{}^0 A x` is the unique point of the canonical argmin set
`Argmin[A x] (fun u : H ↦ ((‖u‖ : ℝ) : EReal))`, i.e. the unique element of `A x` of minimal
norm. -/
theorem existsUnique_mem_argmin_norm_of_maximal_of_mem_dom
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) {x : H} (hx : x ∈ A.dom) :
    ∃! u : H, u ∈ Argmin[A x] (fun v : H ↦ ((‖v‖ : ℝ) : EReal)) := by
  refine ⟨A⁰[hA, hx], minimalNormValue_mem_argmin_norm_of_maximal_of_mem_dom hA hx, ?_⟩
  intro u hu
  exact (mem_argmin_norm_iff_eq_minimalNormValue_of_maximal_of_mem_dom hA hx).1 hu

end

end SetValuedOperator
