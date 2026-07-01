import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace Function

open Filter Set

variable {M : Type u} [TopologicalSpace M]

/-- Definition 2.11-extra-3: An exhaustion function on `M` is a continuous real-valued function
whose closed sublevel set `f ⁻¹' Iic c` is compact for every `c : ℝ`. -/
@[mk_iff isExhaustionFunction_iff]
class IsExhaustionFunction (f : M → ℝ) : Prop where
  continuous : Continuous f
  isCompact_sublevelSet (c : ℝ) : IsCompact (f ⁻¹' Iic c)

/-- An exhaustion function tends to `+∞` away from compact sets. -/
theorem IsExhaustionFunction.tendsto_atTop {f : M → ℝ} (hf : f.IsExhaustionFunction) :
    Tendsto f (cocompact M) atTop := by
  rw [Filter.atTop_basis_Ioi.tendsto_right_iff]
  intro c _
  change f ⁻¹' Ioi c ∈ cocompact M
  convert (hf.isCompact_sublevelSet c).compl_mem_cocompact using 1
  ext x
  simp [not_le]

/-- Every exhaustion function is a proper map. -/
theorem IsExhaustionFunction.isProperMap {f : M → ℝ} (hf : f.IsExhaustionFunction) :
    IsProperMap f :=
  isProperMap_iff_tendsto_cocompact.2 ⟨hf.continuous, hf.tendsto_atTop.trans atTop_le_cocompact⟩

/-- An exhaustion function canonically yields a proper map. -/
instance instIsProperMapOfIsExhaustionFunction {f : M → ℝ} [hf : f.IsExhaustionFunction] :
    IsProperMap f :=
  hf.isProperMap

/-- An exhaustion function canonically yields continuity of its underlying function. -/
instance instContinuousOfIsExhaustionFunction {f : M → ℝ} [hf : f.IsExhaustionFunction] :
    Continuous f :=
  hf.continuous

end Function

/-- Any continuous real-valued function on a compact space is an exhaustion function. -/
-- Proof sketch: for each `c`, the set `Set.Iic c` is closed in `ℝ`, so its preimage under a
-- continuous map is closed; closed subsets of a compact space are compact.
theorem Continuous.isExhaustionFunction {M : Type u} [TopologicalSpace M] [CompactSpace M]
    {f : M → ℝ} (hf : Continuous f) : f.IsExhaustionFunction := by
  refine ⟨hf, fun c ↦ ?_⟩
  exact isCompact_univ.of_isClosed_subset (isClosed_Iic.preimage hf) (Set.subset_univ _)
