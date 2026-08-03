import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.SunYuanOptimizationTheoryMethods.Chapter01.Theorem_1_3_9

-- Domain-style sampling for this item:
-- * core/canonical owner in mathlib: `LowerSemicontinuous`
-- * canonical mathlib characterization APIs in the same domain:
--   `lowerSemicontinuous_iff_isClosed_preimage`,
--   `lowerSemicontinuous_iff_isClosed_epigraph`
-- * project-level source-facing bridge already established upstream:
--   `lowerSemicontinuous_iff_isClosed_realEpigraph`,
--   `lowerSemicontinuous_iff_forall_isClosed_sublevelSet`

section Definition1310

variable {α : Type*} [TopologicalSpace α]

/-
Chapter01 Definition 1.3.10 is a `source-facing` recall of the canonical owner
`LowerSemicontinuous` for `WithTop ℝ`-valued functions. The source's ambient
specialization to `ℝⁿ` is a downstream specialization of this topological-domain
owner. Chapter01 Theorem 1.3.9 is the `bridge/view` layer: it identifies the same
notion with closedness of the real-height epigraph and of all real sublevel sets.
-/
#check (LowerSemicontinuous : (α → WithTop ℝ) → Prop)
#check lowerSemicontinuous_iff_isClosed_realEpigraph
#check lowerSemicontinuous_iff_forall_isClosed_sublevelSet

end Definition1310
