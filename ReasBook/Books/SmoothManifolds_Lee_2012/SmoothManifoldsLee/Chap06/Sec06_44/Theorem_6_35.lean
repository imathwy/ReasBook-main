import SmoothManifolds_Lee_2012.Chap05.Sec05_30.Definition_5_30_extra_2
import SmoothManifolds_Lee_2012.Chap06.Sec06_38.Definition_6_38_extra_2
import SmoothManifolds_Lee_2012.Chap06.Sec06_44.Definition_6_44_extra_1
import SmoothManifolds_Lee_2012.Chap06.Sec06_44.Definition_6_44_extra_2

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open Manifold Set
open scoped ContDiff Manifold

-- Semantic search note: `lean_leansearch` did not return a usable parametric-transversality
-- theorem, so this file follows the local Chapter 6 owners `IsSmoothFamily`,
-- `IsTransverseToSubmanifold`, and `has_measure_zero_in_manifold`.

section ParametricTransversality

universe uEM uEN uES uEX uEW uHM uHN uHS uHX uHW uM uN uS

variable {EM : Type uEM} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
variable {EN : Type uEN} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
variable {ES : Type uES} [NormedAddCommGroup ES] [NormedSpace ℝ ES] [FiniteDimensional ℝ ES]
variable {EX : Type uEX} [NormedAddCommGroup EX] [NormedSpace ℝ EX]
variable {EW : Type uEW} [NormedAddCommGroup EW] [NormedSpace ℝ EW]
variable [MeasurableSpace ES] [BorelSpace ES]
variable {HM : Type uHM} [TopologicalSpace HM]
variable {HN : Type uHN} [TopologicalSpace HN]
variable {HS : Type uHS} [TopologicalSpace HS]
variable {HX : Type uHX} [TopologicalSpace HX]
variable {HW : Type uHW} [TopologicalSpace HW]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace HM M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace HN N]
variable {S : Type uS} [TopologicalSpace S] [ChartedSpace HS S]
variable {IM : ModelWithCorners ℝ EM HM} [IsManifold IM ∞ M]
variable {IN : ModelWithCorners ℝ EN HN} [IsManifold IN ∞ N]
variable {IS : ModelWithCorners ℝ ES HS} [IsManifold IS ∞ S]
variable {X : Set M}
variable {JX : ModelWithCorners ℝ EX HX}
variable {JW : ModelWithCorners ℝ EW HW}
variable [ChartedSpace HX X] [IsManifold JX ∞ X] [IsEmbeddedSubmanifold IM JX X]

/-- Helper for Theorem 6.35: if the natural projection from the transverse preimage
`(Function.uncurry F) ⁻¹' X ⊆ S × N` to the parameter manifold `S` has `s` as a regular value,
then the slice `F s : N → M` is transverse to `X`. -/
theorem isTransverseToSubmanifold_of_isRegularValue_parametricPreimageProjection
    {F : S → N → M}
    (htrans : IsTransverseToSubmanifold IM (IS.prod IN) JX X (Function.uncurry F))
    [ChartedSpace HW ((Function.uncurry F) ⁻¹' X)]
    [IsManifold JW ∞ ((Function.uncurry F) ⁻¹' X)]
    [IsEmbeddedSubmanifold (IS.prod IN) JW ((Function.uncurry F) ⁻¹' X)]
    {s : S}
    (hs : IsRegularValue JW IS (fun w : (Function.uncurry F) ⁻¹' X ↦ w.1.1) s) :
    IsTransverseToSubmanifold IM IN JX X (F s) := sorry

/-- Theorem 6.35 (Parametric Transversality Theorem): if `F : S → N → M` is a smooth family and
its uncurried map `S × N → M` is transverse to the embedded submanifold `X ⊆ M`, then the set of
parameters `s : S` for which the slice `F s : N → M` fails to be transverse to `X` has measure
zero in `S`. Equivalently, the transverse slices occur for almost every parameter. -/
theorem parametric_transversality_setOf_not_transverse_has_measure_zero_in_manifold
    {F : S → N → M} (hF : IsSmoothFamily IM IS IN F)
    (htrans : IsTransverseToSubmanifold IM (IS.prod IN) JX X (Function.uncurry F)) :
    has_measure_zero_in_manifold IS {s : S | ¬ IsTransverseToSubmanifold IM IN JX X (F s)} := sorry

end ParametricTransversality
