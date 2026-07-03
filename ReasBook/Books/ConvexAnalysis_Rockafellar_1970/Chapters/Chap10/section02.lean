import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_10_2 (from Chap02) -/
section

variable {γ E : Type*}
variable [TopologicalSpace E]
variable [LinearOrder γ] [TopologicalSpace γ] [OrderTopology γ]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 10.2 compares relative lower/upper semicontinuity with relative
  continuity.
- `core/canonical`: the primary owners are mathlib's
  `LowerSemicontinuousOn`, `UpperSemicontinuousOn`, `LowerSemicontinuous`, and `ContinuousOn`.
- `bridge/view`: the source phrase “relative to `S`” is represented directly by setwise owners
  `LowerSemicontinuousOn f S`, `UpperSemicontinuousOn f S`, and `ContinuousOn f S`.

Revision note for this pass:
- the source implications already owned canonically by mathlib are reused via `recall`:
  `continuousOn_iff_lower_upperSemicontinuousOn` and `ContinuousOn.upperSemicontinuousOn`;
- this file keeps only the non-redundant bridge from global lower semicontinuity plus relative
  upper semicontinuity to relative continuity.
-/

recall continuousOn_iff_lower_upperSemicontinuousOn
recall ContinuousOn.upperSemicontinuousOn

variable {f : E → γ} {S : Set E}

namespace LowerSemicontinuous

/-- If `f` is lower semicontinuous globally and upper semicontinuous relative to `S`, then `f` is
continuous relative to `S`. -/
theorem continuousOn_of_upperSemicontinuousOn
    (hf_lsc : LowerSemicontinuous f) (hf_usc : UpperSemicontinuousOn f S) :
    ContinuousOn f S :=
  (continuousOn_iff_lower_upperSemicontinuousOn).2 ⟨hf_lsc.lowerSemicontinuousOn S, hf_usc⟩

end LowerSemicontinuous

end
